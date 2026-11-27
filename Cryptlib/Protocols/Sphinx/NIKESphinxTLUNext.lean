/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLU
import Cryptlib.Protocols.Sphinx.NIKESphinxPeel

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult relayImpl keysKs keysTag keysEnc)
open Cryptlib.Protocols.Sphinx.Common (v0AD)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # The original's next layer in world 1 of TLU→, for NIKE Sphinx

In world 1 the honest relay answers the replacement with the layer the adversary's original
onion has after the relay. That layer is built with the keys of the original's own layer at the
relay, which the adversary is never shown. Here world 1, after the relay's keys for the
replacement were replaced, is written as the key game for the original onion. -/

section NextLayer

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- The layer after hop `j` of `q`'s onion, with hop `j`'s header keystream given. Of hop `j`'s
keys it reads the MAC key and the blinding factor. -/
def nextOfStream (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) (j : ℕ) (U : ByteArray) : Onion geom :=
  if (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength then
    match nikeHdrTrace geom (Function.update (keysKs geom streamS ks.toArray) j U)
        (keysTag macS ks.toArray) (blindElem nike a ks.toArray)
        (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
            q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd [.recipient q.receiver]).size with
    | some s => split geom (peelHdr nike geom U (ks.toArray[j]!).blindingFactor
        (hdrPeels nike streamS geom ks j (v0AD ++ blindElem nike a ks.toArray 0 ++ s.1 ++ s.2))
      ++ encTrace (keysEnc cipher ks.toArray) (RSOR.path nike q.fwd [.recipient q.receiver]).size
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS
            streamS geom q r)) ((RSOR.path nike q.fwd [.recipient q.receiver]).size - (j + 1)))
    | none => default
  else default

/-- **The layer after hop `j` reads hop `j`'s header key and IV through its keystream only, and
does not read its payload key**: the hop's decryption undoes its encryption. This holds when
the header has a header's length. -/
theorem onionOfKeys_succ (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (a : ByteArray) (ks : List HopKeys) (j : ℕ) (hjp : j < (RSOR.path nike q.fwd [.recipient
        q.receiver]).size) (hjk : j < ks.length)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hgood : ∀ s, nikeHdrTrace geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
        (blindElem nike a ks.toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
            q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
            [.recipient q.receiver]).size = some s →
      (v0AD ++ blindElem nike a ks.toArray 0 ++ s.1 ++ s.2).size = 2 + nike.publicKeySize +
          geom.routingInfoLength + macLength) :
    onionOfKeys nike cipher macS kdfS streamS geom (j + 1) q r a ks
      = nextOfStream nike cipher macS kdfS streamS geom q r a ks j
        (keysKs geom streamS ks.toArray j) := by
  unfold onionOfKeys nextOfStream nikePktFn
  rw [Function.update_eq_self]
  by_cases hb : (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength
  · rw [ite_eq_left hb, ite_eq_left hb]
    generalize hs : nikeHdrTrace geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
      (blindElem nike a ks.toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
          q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
          [.recipient q.receiver]).size = o at hgood
    cases o with
    | none => rfl
    | some s =>
      have hz : (⟨Array.replicate geom.payloadTagLength (0 : UInt8)⟩ : ByteArray).size
          = geom.payloadTagLength := Array.size_replicate
      have hp := (peels_append nike cipher streamS geom ks (RSOR.path nike q.fwd [.recipient
          q.receiver]).size
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS
            streamS geom q r)) _ (hgood s rfl)
        (by rw [ByteArray.size_append, hb, hz]; exact h16) (j + 1) hjp hjk).2
      rw [hdrPeels_succ nike streamS geom ks j _ hjk] at hp
      exact congrArg (split geom) hp
  · rw [ite_eq_right hb, ite_eq_right hb]

/-- `nextOfStream` reads the hops' keys off hop `j`, and of hop `j`'s its MAC key and blinding
factor. -/
theorem nextOfStream_congr (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (a : ByteArray) (ks ks' : List HopKeys) (j : ℕ) (U : ByteArray) (hjp : j < (RSOR.path nike
        q.fwd [.recipient q.receiver]).size)
    (hne : ∀ i, i ≠ j → ks.toArray[i]! = ks'.toArray[i]!)
    (hmac : (ks.toArray[j]!).headerMAC = (ks'.toArray[j]!).headerMAC)
    (hbf : (ks.toArray[j]!).blindingFactor = (ks'.toArray[j]!).blindingFactor)
    (htake : ks.take j = ks'.take j) :
    nextOfStream nike cipher macS kdfS streamS geom q r a ks j U
      = nextOfStream nike cipher macS kdfS streamS geom q r a ks' j U := by
  have hks : Function.update (keysKs geom streamS ks.toArray) j U
      = Function.update (keysKs geom streamS ks'.toArray) j U := by
    funext i
    by_cases hi : i = j
    · rw [hi, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      unfold keysKs
      rw [hne i hi]
  have htag : keysTag macS ks.toArray = keysTag macS ks'.toArray := by
    funext i
    unfold keysTag
    by_cases hi : i = j
    · rw [hi, hmac]
    · rw [hne i hi]
  have hge : blindElem nike a ks.toArray = blindElem nike a ks'.toArray := by
    funext i
    refine blindElem_congr nike a _ _ (fun m => ?_) i
    by_cases hm : m = j
    · rw [hm, hbf]
    · rw [hne m hm]
  have hh : hdrPeels nike streamS geom ks j = hdrPeels nike streamS geom ks' j := by
    funext H
    unfold hdrPeels
    rw [htake]
  have henc := encTrace_congr (keysEnc cipher ks.toArray) (keysEnc cipher ks'.toArray)
    (RSOR.path nike q.fwd [.recipient q.receiver]).size ((⟨Array.replicate geom.payloadTagLength 0⟩
        : ByteArray) ++ (RSOR.body nike macS kdfS streamS geom q r)) ((RSOR.path nike q.fwd
        [.recipient q.receiver]).size - (j + 1)) (by omega) fun i hi _ => by
      unfold keysEnc
      rw [hne i (by omega)]
  unfold nextOfStream
  rw [hks, htag, hge, hh, henc, hbf]

end NextLayer

section ForwardNext

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- The replacement's layer `i`, from the honest relay's header keystream `U`, its tag and the
block `u` it is handed as its encryption of the payload. -/
def strOnion (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) (U :
        KEMSphinx.Keystream geom) (u : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) (i : ℕ) :
    Onion geom :=
  onionOfStream nike cipher macS kdfS streamS geom i
    (W.req (⟨x.2.2.keys, x.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        names x.2.2.k.1) x.2.2.o) (W.rnd x.2.2.o)
    (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W x) default)).toArray 0)
    (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names W x) default)) x.2.2.c.pos
    (Util.Bytes.ofVector U) (Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names W x U)) (Util.Bytes.ofVector u)

/-- The second phase of world 1 as an adversary on the key game for the original onion plays
it: the replacement's element is answered in front of the relay's oracle, under one header, from
the keystream `U` and the ideal cipher's blocks `u` and `v`; the original's next layer is built
from the group element `a` and the keys `ks` it is handed. The relay's own key is not used. -/
def nextPost (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) {pk
    : RSOR.Key nike}
    (ch : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names pk) (ast : A.State)
        (log : Protocols.RSOR.Log 𝒮)
    (U : KEMSphinx.Keystream geom) (km seed : Vector UInt8 32) (o : (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth)
    (d' : Vector UInt8 nike.privateKeySize) (u v : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))
    (a : ByteArray) (ks : List HopKeys) : OracleComp procSpec Bool :=
  let x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) A := (km, seed, ⟨(pk, default), ch.keys, ch.c,
      ast, log, o, d'⟩)
  let mine := strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) x U u ch.c.pos
  let next := if (ch.c.pos : ℕ) + 1 < ch.c.req.fwd.hops.length then
      onionOfKeys nike cipher macS kdfS streamS geom (ch.c.pos + 1) ch.c.req o.1 a ks
    else mine
  simulateQ (Relay.first
      (fun pkt => decide (pkt.extract 2 (2 + nike.publicKeySize)
        = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names)) x.2.2))
      (fun pkt => if pkt.extract 0 ((2 + nike.publicKeySize + geom.routingInfoLength) +
          macS.tagSize)
          = strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) x U
            ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
                names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x U) then
        procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x
            U))
          (constStream (Util.Bytes.ofVector U)) geom
          (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names) x) default).1 default))
          (fun _ y => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain
            (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names) x) else v) pkt
      else none))
    ((simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h =>
        (ch.keys h).2) (ch.c.patchWith next o.1 mine))
      (if drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names)) x.2.2
          < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names)) x.2.2).size then
        A.guess ast (strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x U u 0)
      else pure false)).run' log)

/-- **The adversary on the key game for the original onion.** Its first phase is the first phase
of TLU→ with the original's forward path as the path of keys. Its second phase draws what the
challenger of world 1 draws besides the original's forward secret, and plays `nextPost`. -/
def nextAdv (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    KeyAdversary nike where
  St pk := ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names pk × A.State ×
      Protocols.RSOR.Log 𝒮
  pre := (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A).pre
  post st a ks := do
    let U ← (liftM ($ᵗ (KEMSphinx.Keystream geom)) : OracleComp procSpec _)
    let km ← (liftM ($ᵗ (Vector UInt8 32)) : OracleComp procSpec _)
    let seed ← (liftM ($ᵗ (Vector UInt8 32)) : OracleComp procSpec _)
    let o ← (liftM (shortDraw nike geom) : OracleComp procSpec _)
    let d' ← (liftM ($ᵗ (Vector UInt8 nike.privateKeySize)) : OracleComp procSpec _)
    let u ← (liftM ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) :
        OracleComp procSpec _)
    let v ← (liftM ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) :
        OracleComp procSpec _)
    nextPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A st.1 st.2.1 st.2.2 U km
        seed o d' u v a ks

set_option maxHeartbeats 4000000 in
/-- **The second phase of `nextAdv`, answered by the honest relay, is world 1 after its first
chain**, on a draw, with the original's next layer built from the handed keys. -/
theorem nextPost_real (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary)
    (k : RSOR.Key nike × nike.PrivateKey) (ch : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names k.1) (ast : A.State)
    (log : Protocols.RSOR.Log 𝒮) (U : KEMSphinx.Keystream geom) (km seed : Vector UInt8 32)
    (o : (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth) (d' : Vector UInt8
        nike.privateKeySize) (u v : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))
    (a : ByteArray) (ks : List HopKeys)
    (hcar : (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
        (km, seed, ⟨k, ch.keys, ch.c, ast, log, o, d'⟩) U).extract 2 (2 + nike.publicKeySize)
      = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names))
        (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) :
    simulateQ (procImpl nike cipher macS kdfS streamS geom k.2)
        (nextPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A ch ast log U km
            seed o d' u v a ks)
      = strRunP nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (km, seed, ⟨k, ch.keys, ch.c, ast, log, o,
          d'⟩) U u v
        (fun mine => ch.c.patchWith
          (if (ch.c.pos : ℕ) + 1 < ch.c.req.fwd.hops.length then
            onionOfKeys nike cipher macS kdfS streamS geom (ch.c.pos + 1) ch.c.req o.1 a ks
          else mine) o.1 mine) := by
  unfold nextPost
  dsimp only
  rw [show procImpl nike cipher macS kdfS streamS geom k.2
      = relayImpl (procWith nike cipher macS streamS geom (relayKeys nike kdfS k.2)) from rfl,
    ← QueryImpl.simulateQ_compose, Relay.relayImpl_comp_first]
  have hrel : ∀ (f g : ByteArray → ProcResult) (oa : OracleComp procSpec Bool), f = g →
      simulateQ (relayImpl f) oa = simulateQ (relayImpl g) oa := by
    rintro _ _ _ rfl
    rfl
  show simulateQ (relayImpl (fun pkt =>
      if decide (pkt.extract 2 (2 + nike.publicKeySize) = (drawElem nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
          (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o,
          d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A))) = true then
        (if pkt.extract 0 ((2 + nike.publicKeySize + geom.routingInfoLength) + macS.tagSize) =
            (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast,
            log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U) ++ Util.Bytes.ofVector (strTag nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩
            : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U) then
          procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
              names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U))
              (constStream (Util.Bytes.ofVector U)) geom
            (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
                names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast,
                log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names).Oth A))) default).1 default)) (fun _ =>
                (fun y => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid
                hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
                names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
                (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k,
                ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom
                hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A))) else v)) pkt
        else none)
      else procWith nike cipher macS streamS geom (relayKeys nike kdfS k.2) pkt))
    ((simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h =>
        (ch.keys h).2)
      (ch.c.patchWith (if (ch.c.pos : ℕ) + 1 < ch.c.req.fwd.hops.length then onionOfKeys nike
          cipher macS kdfS streamS geom (ch.c.pos + 1) ch.c.req o.1 a ks else strOnion nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
          𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth
          A)) U u ch.c.pos) o.1 (strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k,
          ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U u ch.c.pos))) (if drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
          𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys,
          ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A) < (drawHops nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
          (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o,
          d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A)).size then A.guess ast (strOnion nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ :
          PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A)) U u 0) else pure false)).run' log) = _
  have hans : (fun pkt =>
      if decide (pkt.extract 2 (2 + nike.publicKeySize) = (drawElem nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
          (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o,
          d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A))) = true then
        (if pkt.extract 0 ((2 + nike.publicKeySize + geom.routingInfoLength) + macS.tagSize) =
            (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast,
            log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U) ++ Util.Bytes.ofVector (strTag nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩
            : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U) then
          procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
              names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U))
              (constStream (Util.Bytes.ofVector U)) geom
            (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
                names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast,
                log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names).Oth A))) default).1 default)) (fun _ =>
                (fun y => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid
                hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
                names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
                (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k,
                ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom
                hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A))) else v)) pkt
        else none)
      else procWith nike cipher macS streamS geom (relayKeys nike kdfS k.2) pkt)
      = onlyAnsH nike cipher macS kdfS streamS geom k.2 (drawElem nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
          (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o,
          d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A)) (strMsg nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U) (strTag
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ :
          PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A)) U)
        (procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
            names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U))
            (constStream (Util.Bytes.ofVector U)) geom
          (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o,
              d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names).Oth A))) default).1 default)) (fun _ => (fun y
              => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast,
              log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names).Oth A))) else v))) := by
    funext pkt
    unfold onlyAnsH
    by_cases he : pkt.extract 2 (2 + nike.publicKeySize) = (drawElem nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ :
        PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A))
    · exact (ite_eq_left (decide_eq_true he)).trans (ite_eq_left he).symm
    · exact (ite_eq_right fun h => he (of_decide_eq_true h)).trans (ite_eq_right he).symm
  refine (hrel _ _ _ hans).trans ?_
  rw [viaOracle_congr nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h =>
      (ch.keys h).2) (fun h => if h = Role.relay then k.2 else (ch.keys h).2)
    (fun h hr => (ite_eq_right hr).symm)]
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have hH : Util.Bytes.ofVector (Util.Bytes.toVecN geom.headerLength
        ((strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o,
            d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U) ++ Util.Bytes.ofVector (strTag nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩
            : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U)))
      = (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o,
          d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A)) U) ++ Util.Bytes.ofVector (strTag nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ :
          PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).Oth A)) U) :=
    Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, Util.Bytes.size_ofVector, hmactag, hhdr]
      unfold strMsg
      rw [Util.Bytes.size_ofVector]
      rfl)
  have hMsz : (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o,
      d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).Oth A)) U).size = (2 + nike.publicKeySize +
      geom.routingInfoLength) := by
    unfold strMsg
    exact Util.Bytes.size_ofVector _
  have hcar' : (Util.Bytes.ofVector (Util.Bytes.toVecN geom.headerLength
        ((strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o,
            d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U) ++ Util.Bytes.ofVector (strTag nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩
            : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A)) U)))).extract 2 (2 + nike.publicKeySize)
            = (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
            .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A))
            := by
    rw [hH, ← hcar]
    exact KEMSphinx.extract_of_prefix_eq (n := (strMsg nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (km,
        seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U).size)
      (by rw [Util.Bytes.extract_append_left]; exact ByteArray.extract_zero_size.symm) 2
      (2 + nike.publicKeySize) (by rw [hMsz]; omega)
  refine (relayImpl_onlyAnsH_run nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun
      h => if h = Role.relay then k.2 else (ch.keys h).2) (drawElem nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ :
      PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).Oth A)) (strMsg nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (km,
      seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U) (strTag nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U) _ _ hH hcar'
    (fun on y => stepOf geom (procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
        .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)) U))
      (constStream (Util.Bytes.ofVector U)) geom (fun _ => .ok (restKeys (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k,
          ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names).Oth A))) default).1 default)) (fun _ _
          => y) (join on)))
    (fun msg on y => replyOf cipher geom msg (procD nike (Primitives.MAC.MAC.const (strTag nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
        := 𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth
        A)) U))
      (constStream (Util.Bytes.ofVector U)) geom (fun _ => .ok (restKeys (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (km, seed, (⟨k,
          ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names).Oth A))) default).1 default)) (fun _ _
          => y) (join on)))
    (fun y => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
        := 𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth
        A))) else v)
    (fun on _ => congrArg (stepOf geom) (procD_join nike geom hvalid _ _ _ (fun y => if y = u then
        (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) A).plain (strPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
        .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)))
        else v) on))
    (fun msg on _ => congrArg (replyOf cipher geom msg) (procD_join nike geom hvalid _ _ _ (fun y
        => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
        := 𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth
        A))) else v) on))
    _ _ _).trans ?_
  have hp : (fun (h : Role) (on : Onion geom) => if h = Role.relay then
        stepOf geom (noneAns nike cipher macS kdfS streamS geom ((fun h => if h = Role.relay then
            k.2 else (ch.keys h).2) Role.relay) (drawElem nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
            (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names).Oth A)) (join on))
      else RSOR.proc nike cipher macS kdfS streamS geom ((fun h => if h = Role.relay then k.2 else
          (ch.keys h).2) h) on)
      = (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
          .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)))
          :=
    funext fun h => funext fun on => by
      by_cases hh : h = Role.relay
      · subst hh
        rfl
      · exact (ite_eq_right hh).trans ((congrArg (fun sk =>
          RSOR.proc nike cipher macS kdfS streamS geom sk on) (ite_eq_right hh)).trans
          (ite_eq_right hh).symm)
  have hrp : (fun (h : Role) (msg : Msg geom) (on : Onion geom) => if h = Role.relay then
        replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom ((fun h => if h =
            Role.relay then k.2 else (ch.keys h).2) Role.relay) (drawElem nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
            names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names)) (⟨k, ch.keys, ch.c, ast,
            log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).Oth A))
          (join on))
      else RSOR.reply nike cipher macS kdfS streamS geom ((fun h => if h = Role.relay then k.2 else
          (ch.keys h).2) h) msg on)
      = (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (km, seed, (⟨k, ch.keys, ch.c, ast, log, o, d'⟩ : PropDraw nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
          .relay names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A)))
          :=
    funext fun h => funext fun msg => funext fun on => by
      by_cases hh : h = Role.relay
      · subst hh
        rfl
      · exact (ite_eq_right hh).trans ((congrArg (fun sk =>
          RSOR.reply nike cipher macS kdfS streamS geom sk msg on) (ite_eq_right hh)).trans
          (ite_eq_right hh).symm)
  have key : ∀ (impl impl' : QueryImpl (Protocols.RSOR.oracleSpec 𝒮)
      (StateT (Protocols.RSOR.Log 𝒮) ProbComp))
      (oa oa' : OracleComp (Protocols.RSOR.oracleSpec 𝒮) Bool) (lg : Protocols.RSOR.Log 𝒮),
      impl = impl' → oa = oa' →
        (simulateQ impl oa).run' lg = (simulateQ impl' oa').run' lg := by
    rintro _ _ _ _ _ rfl rfl
    rfl
  unfold strRunP
  exact key _ _ _ _ _
    (Protocols.RSOR.withDec_congr (S := 𝒮) (L := (geom.payloadTagLength +
        geom.forwardPayloadLength)) _ _ _ _ rfl rfl hp hrp rfl) rfl

/-- **On the original's own keys, the patch built from the handed keys is the challenger's.**
The original's next layer from its group element and hop keys is its own next layer, when its
onion builds; the reply the patch hands out does not read the forward path's secret. -/
theorem patchWith_real (names : Role → Name) {pk : RSOR.Key nike} (ch : ForwardCh nike cipher macS
    kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) (pkt : ByteArray)
    (mine : Onion geom)
    (h : RSOR.layer nike cipher macS kdfS streamS geom
      (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]) (setKey r d).1
      (RSOR.body nike macS kdfS streamS geom ch.c.req (setKey r d)) 0 = .ok pkt) :
    ch.c.patchWith
        (if (ch.c.pos : ℕ) + 1 < ch.c.req.fwd.hops.length then
          onionOfKeys nike cipher macS kdfS streamS geom (ch.c.pos + 1) ch.c.req r
            (groupElem nike ((nike.decodePrivateKey d).getD default)
              (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
                (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver])
                (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size).toArray 0)
            (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
              (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver])
              (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
        else mine) r mine
      = ch.c.patch (setKey r d) mine := by
  have hn : (if (ch.c.pos : ℕ) + 1 < ch.c.req.fwd.hops.length then
        onionOfKeys nike cipher macS kdfS streamS geom (ch.c.pos + 1) ch.c.req r
          (groupElem nike ((nike.decodePrivateKey d).getD default)
            (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
              (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver])
              (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size).toArray 0)
          (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
            (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver])
            (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
      else mine) = ch.c.next (setKey r d) mine := by
    unfold Protocols.RSOR.ForwardChallenge.next
    by_cases hlt : (ch.c.pos : ℕ) + 1 < ch.c.req.fwd.hops.length
    · simp only [hlt, ↓reduceIte, ↓reduceDIte]
      exact onionOfKeys_real nike cipher macS kdfS streamS geom ch.c.req r d pkt
        ⟨ch.c.pos + 1, hlt⟩ h
    · simp only [hlt, ↓reduceIte, ↓reduceDIte]
  exact (congrArg (fun nx => ch.c.patchWith nx r mine) hn).trans rfl

/-- The draws of world 1 after its first chain, with the original's forward secret drawn apart:
the honest relays' keys and the adversary's first phase, that secret, the relay's header
keystream, MAC key and blinding seed for the replacement, the challenger's draws, the
replacement's forward secret, and the ideal cipher's two blocks. -/
structure NextDraw (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) where
  k : RSOR.Key nike × nike.PrivateKey
  keys : Role → RSOR.Key nike × nike.PrivateKey
  c : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Challenge (honAt nike cipher macS kdfS streamS
      geom hvalid hmactag h16 .relay names k.1 keys)
  st : A.State
  log : Protocols.RSOR.Log 𝒮
  d0 : Vector UInt8 nike.privateKeySize
  U : KEMSphinx.Keystream geom
  km : Vector UInt8 32
  seed : Vector UInt8 32
  o : (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth
  d' : Vector UInt8 nike.privateKeySize
  u : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
  v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)

/-- The draw of `NextDraw`. -/
def nextDraw (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ProbComp (NextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) := do
  let k ← RSOR.keygen nike
  let k₁ ← RSOR.keygen nike
  let k₂ ← RSOR.keygen nike
  let out ← (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid
      hmactag h16 .relay names k.1 (keysOf nike .relay k₁ k₂))
      (fun h => if h = .relay then k.2 else (keysOf nike .relay k₁ k₂ h).2) {})
    (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1 (keysOf
        nike .relay k₁ k₂)))).run {}
  let d0 ← $ᵗ (Vector UInt8 nike.privateKeySize)
  let U ← $ᵗ (KEMSphinx.Keystream geom)
  let km ← $ᵗ (Vector UInt8 32)
  let seed ← $ᵗ (Vector UInt8 32)
  let o ← shortDraw nike geom
  let d' ← $ᵗ (Vector UInt8 nike.privateKeySize)
  let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  return ⟨k, keysOf nike .relay k₁ k₂, out.1.1, out.1.2, out.2, d0, U, km, seed, o, d', u, v⟩

/-- The key game's real world for `nextAdv` on a draw: its second phase, answered by the honest
relay, on the original's own group element and hop keys. -/
def nextRunK (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (z :
    NextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) :
    ProbComp Bool :=
  simulateQ (procImpl nike cipher macS kdfS streamS geom z.k.2)
    (nextPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (⟨z.keys, z.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names z.k.1) z.st z.log z.U
        z.km z.seed z.o
      z.d' z.u z.v
      (groupElem nike ((nike.decodePrivateKey z.d0).getD default)
        (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey z.d0).getD default)
          (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver])
          (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver]).size).toArray 0)
      (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey z.d0).getD default)
        (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver])
        (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver]).size))

/-- The first phase of `nextAdv`, answered by the honest relay: the first phase of the
adversary of TLU→ against the game's honest relays. -/
theorem nextAdv_pre (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary)
    (k : RSOR.Key nike × nike.PrivateKey) :
    simulateQ (procImpl nike cipher macS kdfS streamS geom k.2) ((nextAdv nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names A).pre k.1)
      = (do
        let k₁ ← RSOR.keygen nike
        let k₂ ← RSOR.keygen nike
        let out ← (simulateQ (Protocols.RSOR.honest
            (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1 (keysOf
                nike .relay k₁ k₂))
            (fun h => if h = .relay then k.2 else (keysOf nike .relay k₁ k₂ h).2) {})
          (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1
              (keysOf nike .relay k₁ k₂)))).run {}
        return (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (⟨keysOf nike .relay k₁ k₂, out.1.1⟩ : ForwardCh nike cipher macS kdfS streamS geom
                hvalid hmactag h16 names k.1),
          ((⟨keysOf nike .relay k₁ k₂, out.1.1⟩ : ForwardCh nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names k.1), out.1.2, out.2))) :=
  propAdv_pre nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names)) (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).draw
    (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names)) A k

set_option maxHeartbeats 4000000 in
/-- **The key game's real world for `nextAdv`, as its draws and then the second phase.** -/
theorem keyGame_true_nextAdv (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    keyGame cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names A) true
      =ᵈ nextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= nextRunK nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names A := by
  have of_eq : ∀ {a b : ProbComp Bool}, a = b → a =ᵈ b := fun h => h ▸ EvalDistEq.rfl
  unfold keyGame
  simp only [ite_true, hopKeysWith_hopKey]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  refine of_eq ?_
  unfold nextDraw
  simp only [nextAdv_pre, bind_assoc, pure_bind]
  simp only [RSOR.keygen, bind_assoc, pure_bind]
  refine bind_congr fun s => bind_congr fun s₁ => bind_congr fun s₂ => bind_congr fun out =>
    bind_congr fun d0 => ?_
  have hpos : (out.1.1.pos : ℕ) < out.1.1.req.fwd.hops.length := out.1.1.pos.isLt
  have hsz := RSOR.path_size nike out.1.1.req.fwd [.recipient out.1.1.req.receiver]
  have hkey : (out.1.1.req.fwd.hops[(out.1.1.pos : ℕ)]'hpos).key
      = ⟨nike.derivePublicKey (nike.privateKeyFromSeed s), _, rfl⟩ :=
    congrArg (·.key) out.1.1.relay
  have hpk : ((RSOR.path nike out.1.1.req.fwd [.recipient out.1.1.req.receiver])[
        (out.1.1.pos : ℕ)]!).publicKey
      = Util.Bytes.ofVector (nike.encodePublicKey
        (nike.derivePublicKey (nike.privateKeyFromSeed s))) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey
  have hmod := modify_publicKey_self
    (RSOR.path nike out.1.1.req.fwd [.recipient out.1.1.req.receiver]) out.1.1.pos
    (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey (nike.privateKeyFromSeed s))))
    (by rw [hsz]; exact hpos) hpk
  have hlt : (out.1.1.pos : ℕ)
      < (RSOR.path nike out.1.1.req.fwd [.recipient out.1.1.req.receiver]).size := by
    rw [hsz]; exact hpos
  simp only [forwardPlace, fwd0, hmod]
  refine (ite_eq_left hlt).trans ?_
  rw [procImplK_hopKeys nike cipher macS kdfS streamS geom _ _ _ _ _ hlt hpk]
  unfold nextAdv
  simp only [simulateQ_bind, simulateQ_procImpl_liftM]
  rfl

omit cipher macS kdfS streamS hvalid hmactag h16 in
/-- Three uniform draws may be made after another draw. -/
theorem evalDistEq_swap3 {α β : Type} (ma : ProbComp α)
    (K : KEMSphinx.Keystream geom → Vector UInt8 32 → Vector UInt8 32 → α → ProbComp β) :
    (do
      let U ← $ᵗ (KEMSphinx.Keystream geom)
      let km ← $ᵗ (Vector UInt8 32)
      let seed ← $ᵗ (Vector UInt8 32)
      let a ← ma
      K U km seed a)
      =ᵈ (do
        let a ← ma
        let U ← $ᵗ (KEMSphinx.Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let seed ← $ᵗ (Vector UInt8 32)
        K U km seed a) := by
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U => EvalDistEq.bind_right _ fun km =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- World 1 after its first chain, on a draw: its keystream-level run, with the original's
forward secret put into the challenger's randomness. -/
def nextRunW (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (z :
    NextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) :
    ProbComp Bool :=
  strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) A
    (z.km, z.seed, ⟨z.k, z.keys, z.c, z.st, z.log, (setKey z.o.1 z.d0, z.o.2), z.d'⟩) z.U z.u z.v

set_option maxHeartbeats 4000000 in
/-- **World 1 after its first chain, over the same draws**, the original's forward secret drawn
apart. -/
theorem prgIdeal_fwd1_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    PRGScheme.prgIdealExperiment (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)
      =ᵈ nextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= nextRunW nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names A := by
  have of_eq : ∀ {a b : ProbComp Bool}, a = b → a =ᵈ b := fun h => h ▸ EvalDistEq.rfl
  have h0 : PRGScheme.prgIdealExperiment (forwardStreamAdv nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)
      = (do
        let U ← $ᵗ (KEMSphinx.Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let seed ← $ᵗ (Vector UInt8 32)
        let k ← RSOR.keygen nike
        let k₁ ← RSOR.keygen nike
        let k₂ ← RSOR.keygen nike
        let out ← (simulateQ (Protocols.RSOR.honest
            (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1 (keysOf
                nike .relay k₁ k₂))
            (fun h => if h = .relay then k.2 else (keysOf nike .relay k₁ k₂ h).2) {})
          (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1
              (keysOf nike .relay k₁ k₂)))).run {}
        let r ← $ᵗ (RSOR.Randomness nike geom)
        let m ← $ᵗ (Msg geom)
        let n ← $ᵗ Name
        let r' ← $ᵗ (RSOR.Randomness nike geom)
        let d' ← $ᵗ (Vector UInt8 nike.privateKeySize)
        let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) A
          (km, seed, ⟨k, keysOf nike .relay k₁ k₂, out.1.1, out.1.2, out.2, (r, m, n, r'), d'⟩)
          U u v) := by
    unfold PRGScheme.prgIdealExperiment forwardStreamAdv forwardDraw propDrawOf
    show _ = _
    simp only [fwd1, shortDraw, bind_assoc, pure_bind]
  rw [h0]
  refine EvalDistEq.trans (evalDistEq_swap3 geom _ _) ?_
  unfold nextDraw nextRunW
  simp only [shortDraw, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => ?_
  refine EvalDistEq.trans (evalDistEq_swap3 geom _ _) ?_
  refine EvalDistEq.bind_right _ fun k₁ => ?_
  refine EvalDistEq.trans (evalDistEq_swap3 geom _ _) ?_
  refine EvalDistEq.bind_right _ fun k₂ => ?_
  refine EvalDistEq.trans (evalDistEq_swap3 geom _ _) ?_
  refine EvalDistEq.bind_right _ fun out => ?_
  refine EvalDistEq.trans ?_ (evalDistEq_swap3 geom _ _)
  refine EvalDistEq.bind_right _ fun U => EvalDistEq.bind_right _ fun km =>
    EvalDistEq.bind_right _ fun seed => ?_
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  exact (evalDistEq_setKey nike geom _).symm

/-- The draws that step 1 of the hidden layer does not cover: the bytes under the relay's tag do
not carry the replacement's element, or the original onion cannot be built. -/
def nextBad {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (z :
    NextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) : Prop :=
  ¬ ((strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (A := A)
        (z.km, z.seed, ⟨z.k, z.keys, z.c, z.st, z.log, z.o, z.d'⟩) z.U).extract 2
        (2 + nike.publicKeySize)
      = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names))
        (⟨z.k, z.keys, z.c, z.st, z.log, z.o, z.d'⟩ :
          PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names).Oth A) ∧
    ∃ pkt, RSOR.layer nike cipher macS kdfS streamS geom
      (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver]) (setKey z.o.1 z.d0).1
      (RSOR.body nike macS kdfS streamS geom z.c.req (setKey z.o.1 z.d0)) 0 = .ok pkt)

set_option maxHeartbeats 4000000 in
/-- On a draw that is not bad, the two games run alike. -/
theorem nextRun_eq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (z : NextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)
    (hz : ¬ nextBad nike cipher macS kdfS streamS geom hvalid hmactag h16 z) : nextRunW nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names A z = nextRunK nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names A z := by
  obtain ⟨hcar, pkt, hpkt⟩ := Classical.not_not.mp hz
  unfold nextRunK
  rw [nextPost_real nike cipher macS kdfS streamS geom hvalid hmactag h16 names A z.k (⟨z.keys,
      z.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names z.k.1) z.st
      z.log z.U z.km
    z.seed z.o z.d' z.u z.v _ _ hcar]
  have hpatch : (fun mine : Onion geom => z.c.patchWith
        (if (z.c.pos : ℕ) + 1 < z.c.req.fwd.hops.length then
          onionOfKeys nike cipher macS kdfS streamS geom (z.c.pos + 1) z.c.req z.o.1
            (groupElem nike ((nike.decodePrivateKey z.d0).getD default)
              (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey z.d0).getD default)
                (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver])
                (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver]).size).toArray 0)
            (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey z.d0).getD default)
              (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver])
              (RSOR.path nike z.c.req.fwd [.recipient z.c.req.receiver]).size)
        else mine) z.o.1 mine)
      = fun mine => z.c.patch (setKey z.o.1 z.d0) mine :=
    funext fun mine => patchWith_real nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (⟨z.keys, z.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        z.k.1) z.o.1
      z.d0 pkt mine hpkt
  rw [hpatch]
  rfl

/-- **Step 1 of the hidden layer.** World 1 after its first chain is the key game's real world
for the adversary `nextAdv` on the original onion, off the bad draws. -/
theorem prgIdeal_fwd1_sub_keyGame_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable
    (S := 𝒮)).Adversary) :
    |(Pr{let b ← (PRGScheme.prgIdealExperiment
          (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b = true]).toReal
      - (Pr{let b ← (keyGame cipher macS kdfS streamS geom
          (nextAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) true)}[b =
              true]).toReal|
    ≤ (Pr{let z ← (nextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[nextBad
        nike cipher macS kdfS streamS geom hvalid hmactag h16 z]).toReal := by
  rw [(prgIdeal_fwd1_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun b => b = true),
    (keyGame_true_nextAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A).prEvent_eq
        (fun b => b = true)]
  exact KEMSphinx.prEvent_bind_toReal_sub_le_of_bad (nextDraw nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names A) (nextRunW nike cipher macS kdfS streamS geom hvalid hmactag h16
      names A)
    (nextRunK nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) (nextBad nike cipher
        macS kdfS streamS geom hvalid hmactag h16) (fun z hz => nextRun_eq nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names A z hz) (fun b => b = true)

/-! ## The relay refuses the original's element -/

/-- The draws of the key game for `nextAdv` before its second phase: the honest relays' keys,
the adversary's first phase, and the original's forward secret. -/
structure NextPre (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    where
  k : RSOR.Key nike × nike.PrivateKey
  keys : Role → RSOR.Key nike × nike.PrivateKey
  c : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Challenge (honAt nike cipher macS kdfS streamS
      geom hvalid hmactag h16 .relay names k.1 keys)
  st : A.State
  log : Protocols.RSOR.Log 𝒮
  d0 : Vector UInt8 nike.privateKeySize

/-- The draw of `NextPre`. -/
def nextPre (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ProbComp (NextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) := do
  let k ← RSOR.keygen nike
  let k₁ ← RSOR.keygen nike
  let k₂ ← RSOR.keygen nike
  let out ← (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid
      hmactag h16 .relay names k.1 (keysOf nike .relay k₁ k₂))
      (fun h => if h = .relay then k.2 else (keysOf nike .relay k₁ k₂ h).2) {})
    (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1 (keysOf
        nike .relay k₁ k₂)))).run {}
  let d0 ← $ᵗ (Vector UInt8 nike.privateKeySize)
  return ⟨k, keysOf nike .relay k₁ k₂, out.1.1, out.1.2, out.2, d0⟩

/-- The original's hop keys with the honest relay's replaced by the uniform `u`. -/
def nextKeysI {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : (KEMSphinx.KeyTuple × Vector UInt8 32) × NextPre nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names A) : List HopKeys :=
  hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d0).getD default)
    (RSOR.path nike x.2.c.req.fwd [.recipient x.2.c.req.receiver]) x.2.c.pos (keysOfDraw x.1)
    (RSOR.path nike x.2.c.req.fwd [.recipient x.2.c.req.receiver]).size

/-- The original's element at the honest relay. -/
def nextElemI {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : (KEMSphinx.KeyTuple × Vector UInt8 32) × NextPre nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names A) : ByteArray :=
  groupElem nike ((nike.decodePrivateKey x.2.d0).getD default) (nextKeysI nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x).toArray x.2.c.pos

/-- The second phase of `nextAdv` on the original's group element and the replaced keys. -/
def nextRunI (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : (KEMSphinx.KeyTuple × Vector UInt8 32) × NextPre nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names A) : OracleComp procSpec Bool :=
  (nextAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A).post
    ((⟨x.2.keys, x.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        x.2.k.1), x.2.st, x.2.log)
    (groupElem nike ((nike.decodePrivateKey x.2.d0).getD default) (nextKeysI nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x).toArray 0)
    (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 x)

/-- The key game's other world for `nextAdv` with the relay answering the original's element by
`hand`. -/
def nextGame (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (hand : (KEMSphinx.KeyTuple × Vector UInt8 32) × NextPre nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names A → ByteArray → ProcResult) :
    ProbComp Bool :=
  Relay.gameHand
    (do
      let u ← $ᵗ (KEMSphinx.KeyTuple × Vector UInt8 32)
      let p ← nextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
      return (u, p))
    (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize) = nextElemI nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x))
    (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
    (nextRunI nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) hand

set_option maxHeartbeats 4000000 in
/-- **The key game's other world for `nextAdv` is a relay game**: the relay answers the
original's element with the replaced keys. -/
theorem keyGame_false_nextAdv (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    keyGame cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names A) false
      = nextGame nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (fun x => procWith
          nike cipher macS streamS geom
        (fun _ => .ok (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16
            x).toArray[(x.2.c.pos : ℕ)]!)) := by
  unfold keyGame nextGame Relay.gameHand nextPre
  simp only [Bool.false_eq_true, ite_false, nextAdv_pre, bind_assoc, pure_bind]
  simp only [RSOR.keygen, bind_assoc, pure_bind]
  refine bind_congr fun u => bind_congr fun s => bind_congr fun s₁ => bind_congr fun s₂ =>
    bind_congr fun out => bind_congr fun d0 => ?_
  have hpos : (out.1.1.pos : ℕ) < out.1.1.req.fwd.hops.length := out.1.1.pos.isLt
  have hsz := RSOR.path_size nike out.1.1.req.fwd [.recipient out.1.1.req.receiver]
  have hkey : (out.1.1.req.fwd.hops[(out.1.1.pos : ℕ)]'hpos).key
      = ⟨nike.derivePublicKey (nike.privateKeyFromSeed s), _, rfl⟩ :=
    congrArg (·.key) out.1.1.relay
  have hpk : ((RSOR.path nike out.1.1.req.fwd [.recipient out.1.1.req.receiver])[
        (out.1.1.pos : ℕ)]!).publicKey
      = Util.Bytes.ofVector (nike.encodePublicKey
        (nike.derivePublicKey (nike.privateKeyFromSeed s))) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey
  have hmod := modify_publicKey_self
    (RSOR.path nike out.1.1.req.fwd [.recipient out.1.1.req.receiver]) out.1.1.pos
    (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey (nike.privateKeyFromSeed s))))
    (by rw [hsz]; exact hpos) hpk
  have hlt : (out.1.1.pos : ℕ)
      < (RSOR.path nike out.1.1.req.fwd [.recipient out.1.1.req.receiver]).size := by
    rw [hsz]; exact hpos
  simp only [forwardPlace, fwd0, hmod]
  refine (ite_eq_left hlt).trans ?_
  have hI : ∀ (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys),
      procImplK nike cipher macS kdfS streamS geom sk a t
        = relayImpl (fun pkt => if decide (pkt.extract 2 (2 + nike.publicKeySize) = a) = true
          then procWith nike cipher macS streamS geom (fun _ => .ok t) pkt
          else procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt) :=
    fun sk a t => congrArg relayImpl (funext fun pkt => by
      rw [procWith_keysExcept]
      by_cases he : pkt.extract 2 (2 + nike.publicKeySize) = a
      · exact (ite_eq_left he).trans (ite_eq_left (decide_eq_true he)).symm
      · exact (ite_eq_right he).trans (ite_eq_right fun h => he (of_decide_eq_true h)).symm)
  rw [hI]
  rfl

/-- **Step 3 of the hidden layer.** In the key game's other world for `nextAdv` the relay may
refuse the original's element, at the cost of the chance that the adversary sends a packet
carrying it. -/
theorem keyGame_false_nextAdv_sub_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable
    (S := 𝒮)).Adversary) :
    |(Pr{let b ← (keyGame cipher macS kdfS streamS geom
          (nextAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) false)}[b =
              true]).toReal
      - (Pr{let b ← (nextGame nike cipher macS kdfS streamS geom hvalid hmactag h16 names A fun _ _
          => none)}[b = true]).toReal|
    ≤ (Pr{let b ← (Relay.gameChal
        (do
          let u ← $ᵗ (KEMSphinx.KeyTuple × Vector UInt8 32)
          let p ← nextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
          return (u, p))
        (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize) = nextElemI nike cipher macS
            kdfS streamS geom hvalid hmactag h16 x))
        (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
        (nextRunI nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) fun _ _ =>
            none)}[b = true]).toReal := by
  rw [keyGame_false_nextAdv]
  exact Relay.gameHand_sub_le _ _ _ _ _ _

end ForwardNext

end Cryptlib.Protocols.Sphinx.NIKESphinx
