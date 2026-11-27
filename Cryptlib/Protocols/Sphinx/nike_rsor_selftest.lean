/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.Geometry
import Cryptlib.Protocols.Sphinx.NIKESphinxRSOR
import Cryptlib.Primitives.NIKE.Schemes

/-!
# NIKE Sphinx as an RSOR scheme, end to end

`runRound` runs NIKE Sphinx as a `Protocols.RSOR.Scheme`: a request, the exit relay's reply, and
the sender opening it. Every layer a relay receives is compared with `form` or `formBack`, which
is what the scheme's laws state. -/

open Cryptlib.Protocols.Sphinx.Geometry
open Cryptlib.Protocols.Sphinx.NIKESphinx
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)

private def wbCipher := Cryptlib.Primitives.WideBlockCipher.AEZ.aez
private def macS := Cryptlib.Primitives.MAC.HMAC.hmacSha256MAC
private def kdfS := Cryptlib.Primitives.KDF.HKDF.hkdfSha256Expand
private def streamS := Cryptlib.Primitives.StreamCipher.AES256CTR.aes256CTR

private def randomVector (n : Nat) : IO (Vector UInt8 n) := do
  let bs ← IO.getRandomBytes (USize.ofNat n)
  pure (Vector.ofFn fun i : Fin n => bs[i.val]!)

/-- A relay of the scheme and its private key, made as the scheme's `keygen` makes them. -/
private def newRelay (nike : NIKE) :
    IO (Cryptlib.Protocols.RSOR.Hop (Vector UInt8 32) (RSOR.Key nike) × nike.PrivateKey) := do
  let sk := nike.privateKeyFromSeed (← randomVector 32)
  pure (⟨← randomVector 32, nike.derivePublicKey sk, sk, rfl⟩, sk)

private def randomDraw (nike : NIKE) (geom : Geometry) : IO (RSOR.Draw nike geom) := do
  pure (← randomVector _, ← randomVector _)

/-- What a relay of the scheme gets from an onion. -/
private abbrev Step (geom : Geometry) :=
  Cryptlib.Protocols.RSOR.Step Name (Onion geom) (Msg geom) Name
    (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))

/-- `v` with one bit of its byte `i` flipped. -/
private def flipBit {n : Nat} (v : Vector UInt8 n) (i : Nat) : Vector UInt8 n :=
  Vector.ofFn fun k => if k.val = i then v[k] ^^^ 1 else v[k]

/-- The scheme end to end: a request over `nFwd` relays, the exit relay's reply over `nBack`
relays, and the sender opening it. A relay must reject a changed header, and a changed reply
payload must not open. -/
def runRound (nike : NIKE) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) (nFwd nBack : Nat) :
    IO Bool := do
  let S := RSOR.scheme nike wbCipher macS kdfS streamS geom hvalid rfl h16
  let fwd ← (List.range nFwd).mapM fun _ => newRelay nike
  let back ← (List.range nBack).mapM fun _ => newRelay nike
  let fh := fwd.map (·.1)
  let bh := back.map (·.1)
  if h : fh.length ≤ geom.nrHops ∧ (fh.map (·.name)).Nodup ∧ bh.length ≤ geom.nrHops ∧
      (bh.map (·.name)).Nodup ∧ 0 < fh.length then
    let some (_, exitKey) := fwd.getLast? | return false
    let q : RSOR.Request nike geom :=
      { msg := ← randomVector _, receiver := ← randomVector 32, fwd := ⟨fh, h.1, h.2.1⟩,
        back := ⟨bh, h.2.2.1, h.2.2.2.1⟩, fwd_ne := List.ne_nil_of_length_pos h.2.2.2.2 }
    let r : RSOR.Randomness nike geom := (← randomDraw nike geom, ← randomDraw nike geom,
      ← randomVector 64, ← randomVector 16)
    let answer : Msg geom ← randomVector _
    let mut ok := true
    let mut o : Onion geom := S.form q r q.first
    for (i, sk) in (List.finRange q.fwd.hops.length).zip (fwd.map (·.2)) do
      let want : Onion geom := S.form q r i
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
    let exit : Option (Name × Onion geom) := S.reply exitKey q.fwd.hops[q.last].name answer o
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
          let want : Onion geom := S.formBack q r answer j
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
            let opened : Option (Msg geom) := S.recover q r p
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
    IO.eprintln "  runRound: the paths are not routes"
    pure false

/-- The sender asked to reply to the last layer of a reply. A relay replies only to a packet it
delivers, so the sender must not answer. Counts the answers over `trials` runs: the old rule
read any decrypted payload whose first byte is 1 as carrying a SURB, about 1 run in 256. -/
def runSenderReply (nike : NIKE) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) (trials : Nat) : IO Bool := do
  let S := RSOR.scheme nike wbCipher macS kdfS streamS geom hvalid rfl h16
  let mut answers := 0
  for _ in [0:trials] do
    let (exit, exitKey) ← newRelay nike
    let (sender, senderKey) ← newRelay nike
    if h : 1 ≤ geom.nrHops then
      let q : RSOR.Request nike geom :=
        { msg := ← randomVector _, receiver := ← randomVector 32,
          fwd := ⟨[exit], h, by simp⟩, back := ⟨[sender], h, by simp⟩, fwd_ne := by simp }
      let r : RSOR.Randomness nike geom := (← randomDraw nike geom, ← randomDraw nike geom,
        ← randomVector 64, ← randomVector 16)
      let answer : Msg geom ← randomVector _
      let re : Option (Name × Onion geom) := S.reply exitKey exit.name answer (S.form q r q.first)
      let some (_, last) := re
        | IO.eprintln "  runSenderReply: the exit relay's reply failed"; return false
      let re2 : Option (Name × Onion geom) := S.reply senderKey sender.name answer last
      if re2.isSome then answers := answers + 1
    else
      IO.eprintln "  runSenderReply: no hops"
      return false
  let ok := answers == 0
  IO.println (s!"the sender asked to reply to a reply's last layer ({trials} runs): "
    ++ s!"answered {answers} times: {if ok then "ok" else "FAIL"}")
  pure ok

def runSuite (schemeName : String) (nike : NIKE) : IO Bool := do
  IO.println s!"-- {schemeName} --"
  let geom := ofNIKEWith schemeName nike 103 true 5
  let hvalid := ofNIKEWith_validForNIKE schemeName nike 103 true 5
  let h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength := by
    rw [ofNIKEWith_payloadTagLength schemeName nike 103 true 5]
    unfold Cryptlib.Protocols.Sphinx.Constants.payloadTagLength; omega
  let mut ok := true
  for (nFwd, nBack) in [(1, 1), (3, 2), (5, 5), (2, 0)] do
    let roundOk ← runRound nike geom hvalid h16 nFwd nBack
    IO.println (s!"RSOR scheme ({nFwd} forward, {nBack} back of 5): "
      ++ (if roundOk then "ok" else "FAIL"))
    ok := ok && roundOk
  ok := (← runSenderReply nike geom hvalid h16 5) && ok
  pure ok

def main : IO UInt32 := do
  let okLadder ← runSuite "x25519-ladder" Cryptlib.Primitives.NIKE.X25519LadderScheme
  IO.println ""
  let okGroup ← runSuite "x25519-group" Cryptlib.Primitives.NIKE.X25519Scheme
  IO.println ""
  if okLadder && okGroup then
    IO.println "all NIKE-Sphinx RSOR self-tests passed (both schemes)"
    pure 0
  else
    IO.eprintln "NIKE-Sphinx RSOR self-tests FAILED"
    pure 1
