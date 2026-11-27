/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLU

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult relayImpl)
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

end ForwardNext

end Cryptlib.Protocols.Sphinx.NIKESphinx
