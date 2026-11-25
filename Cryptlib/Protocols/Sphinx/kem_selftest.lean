/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.OracleComp.RunIO
import Cryptlib.Protocols.Sphinx.Geometry
import Cryptlib.Protocols.Sphinx.Types
import Cryptlib.Protocols.Sphinx.KEMSphinxTail
import Cryptlib.Protocols.Sphinx.KEMSphinxRSOR
import Cryptlib.Protocols.Sphinx.SURB
import Cryptlib.Util.HexBytes
import Cryptlib.Util.Bytes

/-!
# KEM-Sphinx create/unwrap round-trip self-test

Builds packets with fresh keys and checks that unwrapping recovers them, for every registered
KEM-Sphinx scheme. `runRSORRound` runs KEM Sphinx as a `Protocols.RSOR.Scheme`: a request, the
exit relay's reply, and the sender opening it. -/

open Cryptlib.Util.HexBytes
open Cryptlib.Protocols.Sphinx.Geometry
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.KEMSphinx
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Util.Bytes (ofVector)

private def x25519Ladder := Cryptlib.Primitives.KEM.kemX25519Ladder
private def x25519Group := Cryptlib.Primitives.KEM.kemX25519
private def mlkem768 := Cryptlib.Primitives.KEM.MLKEM768.kemMLKEM768
private def mlkem768X25519 := Cryptlib.Primitives.KEM.kemMLKEM768X25519
private def mlkem768Hedged := Cryptlib.Primitives.KEM.MLKEMHedged.kemMLKEMHedged768
private def mlkem768HedgedX25519 := Cryptlib.Primitives.KEM.kemMLKEMHedged768X25519

private def wbCipher := Cryptlib.Primitives.WideBlockCipher.AEZ.aez
private def macS := Cryptlib.Primitives.MAC.HMAC.hmacSha256MAC
private def kdfS := Cryptlib.Primitives.KDF.HKDF.hkdfSha256Expand
private def streamS := Cryptlib.Primitives.StreamCipher.AES256CTR.aes256CTR

private def randomVector (n : Nat) : IO (Vector UInt8 n) := do
  let bs ← IO.getRandomBytes (USize.ofNat n)
  pure (Vector.ofFn fun i : Fin n => bs[i.val]!)

private def randomBytes (n : Nat) : IO ByteArray := IO.getRandomBytes (USize.ofNat n)

structure Node where
  id : Vector UInt8 32
  /-- `kem.privateKeySize` bytes. -/
  priv : ByteArray
  pub : ByteArray
  deriving Inhabited

/-- A fresh node keypair. Lattice KEM private keys must come from `generate`, not random bytes. -/
private def newNode (kem : KEM) : IO Node := do
  let seed ← randomVector 32
  let id ← randomVector 32
  match kem.generate (kem.stateFromSeed seed) with
  | .error _ _ => throw (IO.userError "newNode: kem.generate failed")
  | .ok ⟨pk, sk, _⟩ _ =>
    pure { id, priv := ofVector (kem.encodePrivateKey sk), pub := ofVector (kem.encodePublicKey pk) }

private def buildPath (nodes : Array Node) (isSURB : Bool := false) : IO (Array PathHop) := do
  let n := nodes.size
  let mut path : Array PathHop := #[]
  for i in [0:n] do
    let node := nodes[i]!
    let cmds : List RoutingCommand ←
      if i < n - 1 then
        pure [.nodeDelay (UInt32.ofNat (1000 + i))]
      else do
        let rid ← randomVector 32
        if isSURB then
          let sid ← randomVector 16
          pure [.recipient rid, .surbReply sid]
        else
          pure [.recipient rid]
    path := path.push { id := node.id, publicKey := node.pub, commands := cmds }
  pure path

def unwrapAll (kem : KEM) (geom : Geometry) (nodes : Array Node) (pkt0 : ByteArray)
    (wantPayload : ByteArray) : IO Bool := do
  let n := nodes.size
  let mut pkt := pkt0
  let mut ok := true
  let mut stop := false
  for i in [0:n] do
    if !stop then
      let node := nodes[i]!
      match unwrapKEM kem wbCipher macS kdfS streamS geom node.priv pkt with
      | .error e =>
        IO.eprintln s!"  hop {i}: unwrap failed: {e}"
        ok := false
        stop := true
      | .ok (payload, _replayTag, cmds, forwardPkt) =>
        if i < n - 1 then
          match forwardPkt with
          | none =>
            IO.eprintln s!"  hop {i}: expected forwarding, got terminal"
            ok := false; stop := true
          | some fwd =>
            if cmds.length ≠ 2 then
              IO.eprintln s!"  hop {i}: expected 2 commands, got {cmds.length}"
              ok := false
            pkt := ofVector fwd
        else
          match payload with
          | none =>
            IO.eprintln s!"  hop {i}: expected terminal payload, got forwarding"
            ok := false
          | some p =>
            if byteArrayToHex p ≠ byteArrayToHex wantPayload then
              IO.eprintln s!"  hop {i}: payload mismatch"
              IO.eprintln s!"    want {byteArrayToHex wantPayload}"
              IO.eprintln s!"    got  {byteArrayToHex p}"
              ok := false
            if cmds.length ≠ 1 then
              IO.eprintln s!"  hop {i}: expected 1 command, got {cmds.length}"
              ok := false
  pure ok

def runRound (kem : KEM) (geom : Geometry) : IO Bool := do
  let nodes ← (List.range geom.nrHops).toArray.mapM (fun _ => newNode kem)
  let path ← buildPath nodes
  let seeds ← nodes.mapM (fun _ => randomVector 32)
  let payload ← randomBytes geom.forwardPayloadLength
  match newKEMPacket kem wbCipher macS kdfS streamS geom seeds ByteArray.empty path payload with
  | .error e =>
    IO.eprintln s!"newKEMPacket failed: {e}"
    pure false
  | .ok pkt0 =>
    if pkt0.size ≠ geom.packetLength then
      IO.eprintln s!"packet length mismatch: got {pkt0.size}, want {geom.packetLength}"
      pure false
    else
      unwrapAll kem geom nodes pkt0 payload

def runFillerRound (schemeName : String) (kem : KEM) : IO Bool := do
  let geom ← IO.ofExcept (ofKEM schemeName 103 false 5)
  let nodes ← (List.range 3).toArray.mapM (fun _ => newNode kem)
  let path ← buildPath nodes
  let seeds ← nodes.mapM (fun _ => randomVector 32)
  let payload ← randomBytes geom.forwardPayloadLength
  let filler ← randomBytes ((geom.nrHops - 3) * geom.perHopRoutingInfoLength)
  match newKEMPacket kem wbCipher macS kdfS streamS geom seeds filler path payload with
  | .error e =>
    IO.eprintln s!"filler round: newKEMPacket failed: {e}"
    pure false
  | .ok pkt0 => unwrapAll kem geom nodes pkt0 payload

/-- As `runRound`, through `Sphinx.Interface.wrap`. `wrapKEM` draws one seed per hop, so the
stream must vary with the counter. -/
def runAbstractWrapRound (kem : KEM) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (pathLen : Nat := geom.nrHops) : IO Bool := do
  let scheme := kemSphinxSchemeOf kem wbCipher macS kdfS streamS geom hvalid rfl h16
  let nodes ← (List.range pathLen).toArray.mapM (fun _ => newNode kem)
  let path ← buildPath nodes
  let fillerSeeds := (Cryptlib.Protocols.Sphinx.Interface.fillerLength geom pathLen + 31) / 32
  let seeds ← (List.range (pathLen + fillerSeeds)).toArray.mapM (fun _ => randomVector 32)
  let payload ← randomVector geom.forwardPayloadLength
  let stream := fun i => seeds[i]!
  match scheme.wrap path.toList payload (Cryptlib.Protocols.Sphinx.Interface.initWith stream) with
  | .error e _ =>
    IO.eprintln s!"abstract wrap failed: {e}"
    pure false
  | .ok pkt _ => unwrapAll kem geom nodes (ofVector pkt) (ofVector payload)

/-- Empirical check of `Sphinx.Interface.unwrap_complete`. -/
def runCompletenessRound (kem : KEM) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) : IO Bool := do
  let scheme := kemSphinxSchemeOf kem wbCipher macS kdfS streamS geom hvalid rfl h16
  let nodes ← (List.range geom.nrHops).toArray.mapM (fun _ => newNode kem)
  let path ← buildPath nodes
  let seeds ← nodes.mapM (fun _ => randomVector 32)
  let payload ← randomVector geom.forwardPayloadLength
  let stream := fun i => seeds[i]!
  match scheme.wrap path.toList payload (Cryptlib.Protocols.Sphinx.Interface.initWith stream) with
  | .error e _ =>
    IO.eprintln s!"completeness: wrap failed: {e}"
    pure false
  | .ok pkt _ =>
    let privKeys := (nodes.map (fun n => n.priv)).toList
    match Cryptlib.Protocols.Sphinx.Interface.unwrapChainAux (unwrapKEM kem wbCipher macS kdfS streamS geom) privKeys (ofVector pkt) with
    | .error e =>
      IO.eprintln s!"completeness: unwrapChainAux failed: {e}"
      pure false
    | .ok none =>
      IO.eprintln "completeness: unwrapChainAux returned no payload"
      pure false
    | .ok (some p) =>
      if byteArrayToHex p ≠ byteArrayToHex (ofVector payload) then
        IO.eprintln "completeness: payload mismatch"
        pure false
      else
        pure true

/-- As `runAbstractWrapRound`, over `newSURB`/`newPacketFromSURB`. The stream needs
`nodes.size + 2` distinct entries. -/
def runAbstractSURBRound (kem : KEM) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) : IO Bool := do
  let scheme := kemSphinxSchemeOf kem wbCipher macS kdfS streamS geom hvalid rfl h16
  let nodes ← (List.range geom.nrHops).toArray.mapM (fun _ => newNode kem)
  let path ← buildPath nodes true
  let seeds ← (List.range (nodes.size + 2)).toArray.mapM (fun _ => randomVector 32)
  let stream := fun i => seeds[i]!
  match scheme.newSURB path.toList (Cryptlib.Protocols.Sphinx.Interface.initWith stream) with
  | .error e _ =>
    IO.eprintln s!"abstract newSURB failed: {e}"
    pure false
  | .ok (surb, surbKeys) _ =>
    let payload ← randomBytes geom.forwardPayloadLength
    match scheme.newPacketFromSURB surb payload with
    | .error e =>
      IO.eprintln s!"abstract newPacketFromSURB failed: {e}"
      pure false
    | .ok (pkt0, firstHopID) =>
      if byteArrayToHex (ofVector firstHopID) ≠ byteArrayToHex (ofVector nodes[0]!.id) then
        IO.eprintln "first-hop ID mismatch"
        pure false
      else do
      let mut pkt := pkt0
      let mut ok := true
      let mut stop := false
      let n := nodes.size
      for i in [0:n] do
        if !stop then
          let node := nodes[i]!
          match unwrapKEM kem wbCipher macS kdfS streamS geom node.priv pkt with
          | .error e =>
            IO.eprintln s!"hop {i}: unwrap failed: {e}"
            ok := false; stop := true
          | .ok (respPayload, _replayTag, _cmds, forwardPkt) =>
            if i < n - 1 then
              match forwardPkt with
              | none =>
                IO.eprintln s!"hop {i}: expected forwarding"
                ok := false; stop := true
              | some fwd => pkt := ofVector fwd
            else
              match respPayload with
              | none =>
                IO.eprintln s!"hop {i}: expected terminal payload"
                ok := false
              | some p =>
                match Cryptlib.Protocols.Sphinx.SURB.decryptSURBPayload wbCipher geom surbKeys p with
                | .error e =>
                  IO.eprintln s!"decryptSURBPayload failed: {e}"
                  ok := false
                | .ok final =>
                  if byteArrayToHex final ≠ byteArrayToHex payload then
                    IO.eprintln "SURB payload mismatch"
                    ok := false
      pure ok

/-- SURB round trip: build a SURB, build a reply packet from it, unwrap through every hop, and
check `decryptSURBPayload` recovers the payload. -/
def runSURBRound (kem : KEM) (geom : Geometry) : IO Bool := do
  let nodes ← (List.range geom.nrHops).toArray.mapM (fun _ => newNode kem)
  let path ← buildPath nodes true
  let seeds ← nodes.mapM (fun _ => randomVector 32)
  let kp1 ← randomVector 32
  let kp2 ← randomVector 32
  match newKEMSURB kem macS kdfS streamS geom seeds (kp1 ++ kp2) ByteArray.empty path with
  | .error e =>
    IO.eprintln s!"newKEMSURB failed: {e}"
    pure false
  | .ok (surb, surbKeys) =>
    if surb.size ≠ geom.surbLength then
      IO.eprintln s!"SURB length mismatch: got {surb.size}, want {geom.surbLength}"
      pure false
    else
    let payload ← randomBytes geom.forwardPayloadLength
    match Cryptlib.Protocols.Sphinx.SURB.newPacketFromSURB wbCipher geom surb payload with
    | .error e =>
      IO.eprintln s!"newPacketFromSURB failed: {e}"
      pure false
    | .ok (pkt0, firstHopID) =>
      if byteArrayToHex (ofVector firstHopID) ≠ byteArrayToHex (ofVector nodes[0]!.id) then
        IO.eprintln "first-hop ID mismatch"
        pure false
      else do
      let mut pkt := pkt0
      let mut ok := true
      let mut stop := false
      let n := nodes.size
      for i in [0:n] do
        if !stop then
          let node := nodes[i]!
          match unwrapKEM kem wbCipher macS kdfS streamS geom node.priv pkt with
          | .error e =>
            IO.eprintln s!"hop {i}: unwrap failed: {e}"
            ok := false; stop := true
          | .ok (respPayload, _replayTag, cmds, forwardPkt) =>
            if i < n - 1 then
              match forwardPkt with
              | none =>
                IO.eprintln s!"hop {i}: expected forwarding"
                ok := false; stop := true
              | some fwd => pkt := ofVector fwd
            else
              if cmds.length ≠ 2 then
                IO.eprintln s!"hop {i}: expected 2 commands, got {cmds.length}"
                ok := false
              match respPayload with
              | none =>
                IO.eprintln s!"hop {i}: expected terminal payload"
                ok := false
              | some p =>
                match Cryptlib.Protocols.Sphinx.SURB.decryptSURBPayload wbCipher geom surbKeys p with
                | .error e =>
                  IO.eprintln s!"decryptSURBPayload failed: {e}"
                  ok := false
                | .ok final =>
                  if byteArrayToHex final ≠ byteArrayToHex payload then
                    IO.eprintln "SURB payload mismatch"
                    ok := false
      pure ok

/-- A relay of the RSOR scheme and its private key, made as the scheme's `keygen` makes them. -/
private def newRelay (kem : KEM) :
    IO (Cryptlib.Protocols.RSOR.Hop (Vector UInt8 32) kem.PublicKey × kem.PrivateKey) := do
  let sk := (keygenOf kem (← randomVector 32)).2
  pure (⟨← randomVector 32, kem.derivePublicKey sk⟩, sk)

private def randomDraw (geom : Geometry) : IO (RSOR.Draw geom) := do
  let bs ← randomBytes (32 * geom.nrHops)
  pure (Vector.ofFn fun i : Fin geom.nrHops => Vector.ofFn fun j : Fin 32 => bs[32 * i.val + j.val]!,
    ← randomVector _)

/-- What a relay of the scheme gets from an onion. -/
private abbrev Step (geom : Geometry) :=
  Cryptlib.Protocols.RSOR.Step RSOR.Name (RSOR.Onion geom) (RSOR.Msg geom) RSOR.Name
    (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))

/-- `v` with one bit of its byte `i` flipped. -/
private def flipBit {n : Nat} (v : Vector UInt8 n) (i : Nat) : Vector UInt8 n :=
  Vector.ofFn fun k => if k.val = i then v[k] ^^^ 1 else v[k]

/-- The RSOR scheme end to end: a request over `nFwd` relays, the exit relay's reply over
`nBack` relays, and the sender opening it. Each layer a relay receives is compared with `form`
or `formBack`, which is what the scheme's laws state. A relay must reject a changed header, and
a changed reply payload must not open. -/
def runRSORRound (kem : KEM) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) (nFwd nBack : Nat) :
    IO Bool := do
  let S := RSOR.scheme kem wbCipher macS kdfS streamS geom hvalid rfl h16
  let fwd ← (List.range nFwd).mapM fun _ => newRelay kem
  let back ← (List.range nBack).mapM fun _ => newRelay kem
  let fh := fwd.map (·.1)
  let bh := back.map (·.1)
  if h : fh.length ≤ geom.nrHops ∧ (fh.map (·.name)).Nodup ∧ bh.length ≤ geom.nrHops ∧
      (bh.map (·.name)).Nodup ∧ 0 < fh.length then
    let some (_, exitKey) := fwd.getLast? | return false
    let q : RSOR.Request kem geom :=
      { msg := ← randomVector _, receiver := ← randomVector 32, fwd := ⟨fh, h.1, h.2.1⟩,
        back := ⟨bh, h.2.2.1, h.2.2.2.1⟩, fwd_ne := List.ne_nil_of_length_pos h.2.2.2.2 }
    let r : RSOR.Randomness geom := (← randomDraw geom, ← randomDraw geom, ← randomVector 64,
      ← randomVector 16)
    let answer : RSOR.Msg geom ← randomVector _
    let mut ok := true
    let mut o : RSOR.Onion geom := S.form q r q.first
    for (i, sk) in (List.finRange q.fwd.hops.length).zip (fwd.map (·.2)) do
      let want : RSOR.Onion geom := S.form q r i
      if o ≠ want then
        IO.eprintln s!"  forward hop {i}: the layer is not form's"
        ok := false
      if (S.proc sk q.fwd.hops[i].name (flipBit o.1 (geom.headerLength - 1), o.2)).isSome then
        IO.eprintln s!"  forward hop {i}: accepted a changed header"
        ok := false
      let step : Option (Step geom) := S.proc sk q.fwd.hops[i].name o
      match step with
      | some (.forward next o') =>
        if some next ≠ (q.fwd.hops[i.val + 1]?).map (·.name) then
          IO.eprintln s!"  forward hop {i}: wrong next relay"
          ok := false
        o := o'
      | some (.deliver m receiver) =>
        if i.val + 1 ≠ q.fwd.hops.length ∨ m ≠ q.msg ∨ receiver ≠ q.receiver then
          IO.eprintln s!"  forward hop {i}: wrong delivery"
          ok := false
      | _ =>
        IO.eprintln s!"  forward hop {i}: proc failed"
        ok := false
    let exit : Option (RSOR.Name × RSOR.Onion geom) :=
      S.reply exitKey q.fwd.hops[q.last].name answer o
    if hb : q.back.hops.length = 0 then
      if exit.isSome then
        IO.eprintln "  the exit relay replied to a request with no backward path"
        ok := false
    else
      match exit with
      | none =>
        IO.eprintln "  the exit relay's reply failed"
        ok := false
      | some (next, first) =>
        if some next ≠ (q.back.hops[0]?).map (·.name) then
          IO.eprintln "  the reply goes to the wrong relay"
          ok := false
        let mut ob := first
        for (j, sk) in (List.finRange q.back.hops.length).zip (back.map (·.2)) do
          let want : RSOR.Onion geom := S.formBack q r answer j
          if ob ≠ want then
            IO.eprintln s!"  backward hop {j}: the layer is not formBack's"
            ok := false
          let step : Option (Step geom) := S.proc sk q.back.hops[j].name ob
          match step with
          | some (.forward next ob') =>
            if some next ≠ (q.back.hops[j.val + 1]?).map (·.name) then
              IO.eprintln s!"  backward hop {j}: wrong next relay"
              ok := false
            ob := ob'
          | some (.reply p) =>
            let opened : Option (RSOR.Msg geom) := S.recover q r p
            if j.val + 1 ≠ q.back.hops.length ∨ opened ≠ some answer then
              IO.eprintln s!"  backward hop {j}: the sender does not recover the reply"
              ok := false
            if (S.recover q r (flipBit p 0)).isSome then
              IO.eprintln s!"  backward hop {j}: a changed reply payload opened"
              ok := false
          | _ =>
            IO.eprintln s!"  backward hop {j}: proc failed"
            ok := false
    pure ok
  else
    IO.eprintln "  runRSORRound: the paths are not routes"
    pure false

/-! ## The games, played honestly

Each round below plays one game of `Protocols.RSOR` in both of its worlds with an adversary that
only routes: it processes the layers of its own relays and hands the others to the honest
relays' oracles. What it sees, apart from the bytes of the onions, must be the same in both
worlds, and must be what the request says. A game that fails this is won without any
cryptanalysis, so it is checked here before anything is proved about it. -/

open Cryptlib.Protocols.RSOR (Role Honest World Log Hop ForwardChallenge BackwardChallenge
  TailChallenge)

section Games

variable {kem : KEM} {geom : Geometry} {hvalid : geom.ValidForKEM kem}
  {h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength}

/-- KEM Sphinx as the scheme the games are played with. -/
private abbrev sch (kem : KEM) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) :
    Cryptlib.Protocols.RSOR.Scheme :=
  RSOR.scheme kem wbCipher macS kdfS streamS geom hvalid rfl h16

private def hex {n : Nat} (v : Vector UInt8 n) : String := byteArrayToHex (ofVector v)

/-- What a relay got from an onion, without the onion's bytes. -/
private def seen : Option (Step geom) → String
  | some (.forward next _) => s!"forward to {hex next}"
  | some (.deliver m receiver) => s!"deliver {hex m} to {hex receiver}"
  | some (.reply _) => "a sealed reply"
  | none => "nothing"

private def seenReply : Option (RSOR.Name × RSOR.Onion geom) → String
  | some (next, _) => s!"reply to {hex next}"
  | none => "no reply"

/-- The onion a relay passes on, or the one it was given if it passes nothing on. -/
private def passedOn (o : RSOR.Onion geom) : Option (Step geom) → RSOR.Onion geom
  | some (.forward _ o') => o'
  | _ => o

/-- An adversarial relay processes an onion. -/
private def advProc (key : kem.PrivateKey) (o : RSOR.Onion geom) : Option (Step geom) :=
  (sch kem geom hvalid h16).proc key (default : Vector UInt8 32) o

/-- An honest relay's oracle processes an onion. -/
private def askProc (hon : Honest (sch kem geom hvalid h16)) (sk : Role → kem.PrivateKey)
    (w : World (sch kem geom hvalid h16)) (log : Log (sch kem geom hvalid h16)) (role : Role)
    (o : RSOR.Onion geom) : IO (Option (Step geom) × Log (sch kem geom hvalid h16)) :=
  OracleComp.runIO ((Cryptlib.Protocols.RSOR.process hon sk w.patch (role, o)).run log)

/-- An honest relay's oracle replies to an onion. -/
private def askReply (hon : Honest (sch kem geom hvalid h16)) (sk : Role → kem.PrivateKey)
    (w : World (sch kem geom hvalid h16)) (log : Log (sch kem geom hvalid h16)) (role : Role)
    (m : RSOR.Msg geom) (o : RSOR.Onion geom) :
    IO (Option (RSOR.Name × RSOR.Onion geom) × Log (sch kem geom hvalid h16)) :=
  OracleComp.runIO ((Cryptlib.Protocols.RSOR.answer hon sk w.patch (role, m, o)).run log)

/-- Play `play` in both worlds and compare what the adversary saw with `want`. -/
private def bothWorlds (name : String) (want : List String)
    (world : Bool → IO (World (sch kem geom hvalid h16)))
    (play : World (sch kem geom hvalid h16) → IO (List String)) : IO Bool := do
  let mut ok := true
  for b in [false, true] do
    let got ← play (← world b)
    if got ≠ want then
      IO.eprintln s!"  {name}, world {b}: the adversary saw {got}, not {want}"
      ok := false
  IO.println s!"{name}, honest run in both worlds: {if ok then "ok" else "FAIL"}"
  pure ok

end Games

/-- TLU→. `tag` has the adversary change the payload on the way to the honest relay. -/
def runForwardGame (kem : KEM) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) (atExit tag : Bool) :
    IO Bool := do
  let (first, firstKey) ← newRelay kem
  let (relay, relayKey) ← newRelay kem
  let (third, thirdKey) ← newRelay kem
  let (back, backKey) ← newRelay kem
  let (sender, senderKey) ← newRelay kem
  let hon : Honest (sch kem geom hvalid h16) := fun | .relay => relay | .back => back | .sender => sender
  let sk : Role → kem.PrivateKey := fun | .relay => relayKey | .back => backKey | .sender => senderKey
  let answer : RSOR.Msg geom ← randomVector _
  let msg : RSOR.Msg geom ← randomVector _
  let receiver : RSOR.Name ← randomVector 32
  if h : 3 ≤ geom.nrHops ∧ ([first, relay].map Hop.name).Nodup ∧
      ([first, relay, third].map Hop.name).Nodup ∧ ([back, sender].map Hop.name).Nodup then
    let backRoute : Cryptlib.Protocols.RSOR.Route geom.nrHops RSOR.Name kem.PublicKey :=
      ⟨[back, sender], Nat.le_of_succ_le h.1, h.2.2.2⟩
    let c : ForwardChallenge (S := sch kem geom hvalid h16) hon :=
      if atExit then
        { req := { msg, receiver, back := backRoute, fwd_ne := by simp
                   fwd := ⟨[first, relay], Nat.le_of_succ_le h.1, h.2.1⟩ }
          pos := ⟨1, Nat.one_lt_two⟩, relay := rfl, sender := rfl }
      else
        { req := { msg, receiver, back := backRoute, fwd_ne := by simp
                   fwd := ⟨[first, relay, third], h.1, h.2.2.1⟩ }
          pos := ⟨1, by show 1 < 3; omega⟩, relay := rfl, sender := rfl }
    let after := if atExit then
        [s!"deliver {hex msg} to {hex receiver}", s!"reply to {hex back.name}"]
      else [s!"forward to {hex third.name}", s!"deliver {hex msg} to {hex receiver}",
        s!"reply to {hex back.name}"]
    let want := if tag then
        [s!"forward to {hex relay.name}", if atExit then "nothing" else s!"forward to {hex third.name}",
          if atExit then "no reply" else "nothing"]
      else [s!"forward to {hex relay.name}"] ++ after ++
        [s!"forward to {hex sender.name}", "a sealed reply"]
    bothWorlds s!"TLU→ game ({if atExit then "exit relay" else "middle relay"}{if tag then ", tagged" else ""})"
      want (fun b => OracleComp.runIO (Cryptlib.Protocols.RSOR.forwardUnlinkable.world c b))
      fun w => do
        let s1 := advProc (hvalid := hvalid) (h16 := h16) firstKey w.onion
        let o1 := passedOn w.onion s1
        let o1 := if tag then (o1.1, flipBit o1.2 0) else o1
        let (s2, log) ← askProc hon sk w {} .relay o1
        if atExit then
          let (re, log) ← askReply hon sk w log .relay answer o1
          if tag then return [seen s1, seen s2, seenReply re]
          let ob := (re.map (·.2)).getD o1
          let s3 := advProc (hvalid := hvalid) (h16 := h16) backKey ob
          let (s4, _) ← askProc hon sk w log .sender (passedOn ob s3)
          return [seen s1, seen s2, seenReply re, seen s3, seen s4]
        else
          let o2 := passedOn o1 s2
          let s3 := advProc (hvalid := hvalid) (h16 := h16) thirdKey o2
          if tag then return [seen s1, seen s2, seen s3]
          let re : Option (RSOR.Name × RSOR.Onion geom) :=
            (sch kem geom hvalid h16).reply thirdKey (default : Vector UInt8 32) answer o2
          let ob := (re.map (·.2)).getD o2
          let s4 := advProc (hvalid := hvalid) (h16 := h16) backKey ob
          let (s5, _) ← askProc hon sk w log .sender (passedOn ob s4)
          return [seen s1, seen s2, seen s3, seenReply re, seen s4, seen s5]
  else
    IO.eprintln "  runForwardGame: the paths are not routes"
    pure false

/-- Every round, against one KEM-Sphinx scheme. -/
def runSuite (schemeName : String) (kem : KEM) : IO Bool := do
  IO.println s!"-- {schemeName} --"
  let mut ok := true
  for nrHops in [1, 2, 3, 5] do
    let geom ← IO.ofExcept (ofKEM schemeName 103 false nrHops)
    let roundOk ← runRound kem geom
    IO.println s!"{nrHops} hop(s), no filler: {if roundOk then "ok" else "FAIL"}"
    ok := ok && roundOk

  let fillerOk ← runFillerRound schemeName kem
  IO.println s!"3 hop(s) of 5 (filler path): {if fillerOk then "ok" else "FAIL"}"
  ok := ok && fillerOk

  let geom3 := ofKEMWith schemeName kem 103 false 3
  let hvalid3 := ofKEMWith_validForKEM schemeName kem 103 false 3
  let h163 : 16 ≤ geom3.payloadTagLength + geom3.forwardPayloadLength := by
    rw [ofKEMWith_payloadTagLength schemeName kem 103 false 3]
    unfold Cryptlib.Protocols.Sphinx.Constants.payloadTagLength; omega

  let abstractOk ← runAbstractWrapRound kem geom3 hvalid3 h163
  IO.println s!"abstract Sphinx.Interface.wrap (3 hops): {if abstractOk then "ok" else "FAIL"}"
  ok := ok && abstractOk

  let geom5 := ofKEMWith schemeName kem 103 false 5
  let hvalid5 := ofKEMWith_validForKEM schemeName kem 103 false 5
  let h165 : 16 ≤ geom5.payloadTagLength + geom5.forwardPayloadLength := by
    rw [ofKEMWith_payloadTagLength schemeName kem 103 false 5]
    unfold Cryptlib.Protocols.Sphinx.Constants.payloadTagLength; omega
  let abstractFillerOk ← runAbstractWrapRound kem geom5 hvalid5 h165 3
  IO.println s!"abstract Sphinx.Interface.wrap (3 hops of 5, drawn filler): {if abstractFillerOk then "ok" else "FAIL"}"
  ok := ok && abstractFillerOk

  let completeOk ← runCompletenessRound kem geom3 hvalid3 h163
  IO.println s!"Sphinx.Interface.unwrap_complete via unwrapChainAux (3 hops): {if completeOk then "ok" else "FAIL"}"
  ok := ok && completeOk

  let geom3surb := ofKEMWith schemeName kem 103 true 3
  let hvalid3s := ofKEMWith_validForKEM schemeName kem 103 true 3
  let h163s : 16 ≤ geom3surb.payloadTagLength + geom3surb.forwardPayloadLength := by
    rw [ofKEMWith_payloadTagLength schemeName kem 103 true 3]
    unfold Cryptlib.Protocols.Sphinx.Constants.payloadTagLength; omega
  let abstractSurbOk ← runAbstractSURBRound kem geom3surb hvalid3s h163s
  IO.println s!"abstract Sphinx.Interface.newSURB/newPacketFromSURB (3 hops): {if abstractSurbOk then "ok" else "FAIL"}"
  ok := ok && abstractSurbOk

  for nrHops in [1, 2, 3, 5] do
    let geom ← IO.ofExcept (ofKEM schemeName 103 true nrHops)
    let surbOk ← runSURBRound kem geom
    IO.println s!"SURB round trip ({nrHops} hop(s)): {if surbOk then "ok" else "FAIL"}"
    ok := ok && surbOk

  let geom5surb := ofKEMWith schemeName kem 103 true 5
  let hvalid5s := ofKEMWith_validForKEM schemeName kem 103 true 5
  let h165s : 16 ≤ geom5surb.payloadTagLength + geom5surb.forwardPayloadLength := by
    rw [ofKEMWith_payloadTagLength schemeName kem 103 true 5]
    unfold Cryptlib.Protocols.Sphinx.Constants.payloadTagLength; omega
  for (nFwd, nBack) in [(1, 1), (3, 2), (5, 5), (2, 0)] do
    let rsorOk ← runRSORRound kem geom5surb hvalid5s h165s nFwd nBack
    IO.println s!"RSOR scheme ({nFwd} forward, {nBack} back of 5): {if rsorOk then "ok" else "FAIL"}"
    ok := ok && rsorOk

  for (atExit, tag) in [(true, false), (false, false), (true, true), (false, true)] do
    ok := (← runForwardGame kem geom5surb hvalid5s h165s atExit tag) && ok

  pure ok

def main (args : List String) : IO UInt32 := do
  match args with
  | [schemeName] =>
    match Cryptlib.Primitives.KEM.byName schemeName with
    | none => IO.eprintln s!"unknown KEM scheme: {schemeName}"; pure 1
    | some kem =>
      let ok ← runSuite schemeName kem
      if ok then pure 0 else IO.eprintln "KEM-Sphinx round-trip self-tests FAILED"; pure 1
  | _ =>
    let okLadder ← runSuite "X25519LadderKEM" x25519Ladder
    IO.println ""
    let okGroup ← runSuite "X25519KEM" x25519Group
    IO.println ""
    let okMLKEM ← runSuite "MLKEM768" mlkem768
    IO.println ""
    let okHybrid ← runSuite "MLKEM768X25519" mlkem768X25519
    IO.println ""
    let okHedged ← runSuite "MLKEM768Hedged" mlkem768Hedged
    IO.println ""
    let okHedgedHybrid ← runSuite "MLKEM768HedgedX25519" mlkem768HedgedX25519
    IO.println ""
    if okLadder && okGroup && okMLKEM && okHybrid && okHedged && okHedgedHybrid then
      IO.println "all KEM-Sphinx round-trip self-tests passed (all six schemes)"
      pure 0
    else
      IO.eprintln "KEM-Sphinx round-trip self-tests FAILED"
      pure 1
