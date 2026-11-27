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
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult)
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

end ForwardNext

end Cryptlib.Protocols.Sphinx.NIKESphinx
