/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTLU
import Cryptlib.Protocols.Sphinx.KEMSphinxPayload

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # The payload cipher step for TLU→

A world of TLU→ in which the honest relay has uniform keys and answers the challenge header
only is a `PayloadGame`, up to the draws that are not good. So its payload cipher can be
replaced by the ideal one at the cost of the one-block cipher advantage
(`PayloadGame.exp_eq`). -/

section ForwardPayload

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

variable [SampleableType kem.Plaintext]

variable (names : Role → RSOR.Name) (Oth : Type) (drawO : ProbComp Oth)
  (view : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → KeyTuple
    → Protocols.RSOR.World (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
  (A : (Protocols.RSOR.forwardUnlinkable
    (S := sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary)
  (M : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → RestKeys → ByteArray)
  (pl : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32
    → Block geom)
  (viewE : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32
    → Block geom
    → Protocols.RSOR.World (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))

local notation "𝒜" =>
  forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO view A

local notation "𝒯" =>
  forwardSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO view

/-- A world of TLU→ with the relay answering the header `tagged M` only, cut at its payload
key: `pl` is the block the sender encrypts under it, and `viewE` the world from the
encrypted block. -/
def forwardPayloadGame : PayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16 where
  X := (Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32)
    × KeyedDraw 𝒜
  draw iv := do
    let r ← $ᵗ (Vector UInt8 32 × Vector UInt8 32)
    let d ← keyedDraw cipher macS kdfS streamS geom
      𝒜
    return ((iv, r), d)
  sk x h := if h = .relay then x.2.k.2 else x.2.cs.2.2.2 h
  c x := x.2.c
  keys x := x.1.2
  header x := Util.Bytes.toVecN _
    (tagged (S := 𝒯)
      macS M x.2.cs.1 x.2.o x.2.c (default, x.1))
  plain x := pl x.2.cs.1 x.2.o x.2.c x.1
  log x := x.2.cs.2.2.1
  patch x e := (viewE x.2.cs.1 x.2.o x.2.c x.1 e).patch
  rest x e := A.guess x.2.cs.2.1 (viewE x.2.cs.1 x.2.o x.2.c x.1 e).onion

omit [SampleableType kem.Plaintext] in
/-- **The payload cipher step, for a world of TLU→.** The world with uniform keys at the honest
relay and the challenge header only is the `PayloadGame` with the cipher, up to the chance of a
draw that is not `good`. -/
theorem forward_tagged_sub_payload_le
    (good : KeyedDraw 𝒜
      → Prop)
    (hMkp : ∀ {pk : Key kem}
      (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
      (o : Oth) (c : kem.Ciphertext) (kp kp' : Vector UInt8 48) (iv : Vector UInt8 16)
      (ke : Vector UInt8 32), M ch o c (kp, iv, ke) = M ch o c (kp', iv, ke))
    (hsize : ∀ d r, good d →
      (M d.cs.1 d.o d.c r).size = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hct : ∀ d r, good d → (M d.cs.1 d.o d.c r).extract 2 (2 + kem.ciphertextSize)
      = ofVector (kem.encodeCiphertext d.c))
    (hview : ∀ d (u : KeyTuple), good d →
      view d.cs.1 d.o d.c u = viewE d.cs.1 d.o d.c u.2 (Util.Bytes.toVecN _
        (cipher.encrypt u.1.toArray (ofVector u.2.1)
          (ofVector (pl d.cs.1 d.o d.c u.2))))) :
    |(Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
          𝒜
          (onlyHeader cipher macS streamS geom (tagged macS M)))}[x = true]).toReal
      - (Pr{let x ← ((forwardPayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16
          names Oth drawO view A M pl viewE).exp true)}[x = true]).toReal|
    ≤ (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        𝒜)}[¬ good d]).toReal := by
  let G := forwardPayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16
    names Oth drawO view A M pl viewE
  let mx : ProbComp (Vector UInt8 48 × G.X) := do
    let kp ← $ᵗ (Vector UInt8 48)
    let iv ← $ᵗ (Vector UInt8 16)
    let x ← G.draw iv
    return (kp, x)
  let F : Vector UInt8 48 × G.X → ProbComp Bool := fun z =>
    keyedRunH cipher macS kdfS streamS geom
      𝒜
      (onlyHeader cipher macS streamS geom (tagged macS M)) z.2.2 (z.1, z.2.1)
  let Gf : Vector UInt8 48 × G.X → ProbComp Bool := fun z =>
    (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16
        (G.sk z.2) (G.c z.2)
        (default, z.2.1.1, G.keys z.2) (G.header z.2)
        (fun y => Util.Bytes.toVecN _
          (cipher.decrypt z.1.toArray (ofVector z.2.1.1) (ofVector y)))
        (G.patch z.2 (Util.Bytes.toVecN _
          (cipher.encrypt z.1.toArray (ofVector z.2.1.1) (ofVector (G.plain z.2))))))
      (G.rest z.2 (Util.Bytes.toVecN _
        (cipher.encrypt z.1.toArray (ofVector z.2.1.1) (ofVector (G.plain z.2)))))).run'
      (G.log z.2)
  have h1 : Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
        𝒜
        (onlyHeader cipher macS streamS geom (tagged macS M)))}[x = true]
      = Pr{let x ← mx >>= F}[x = true] := by
    rw [(keyedGameH_evalDistEq cipher macS kdfS streamS geom
      𝒜 _).prEvent_eq
      (fun x => x = true)]
    simp only [mx, F, G, forwardPayloadGame, bind_assoc, pure_bind]
  have h2 : Pr{let x ← G.exp true}[x = true] = Pr{let x ← mx >>= Gf}[x = true] := by
    refine EvalDistEq.prEvent_eq ?_ _
    unfold PayloadGame.exp
    simp only [mx, Gf, G, forwardPayloadGame, bind_assoc, pure_bind, ↓reduceIte]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun iv =>
      EvalDistEq.bind_right _ fun r => EvalDistEq.bind_right _ fun d => ?_
    exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)
  have hbad : Pr{let z ← mx}[¬ good z.2.2]
      = Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        𝒜)}[¬ good d] := by
    have e : (fun z : Vector UInt8 48 × G.X => z.2.2) <$> mx
        =ᵈ keyedDraw cipher macS kdfS streamS geom
          𝒜 := by
      simp only [mx, G, forwardPayloadGame, map_bind, map_pure, bind_assoc, pure_bind, bind_pure]
      exact (OracleComp.EvalDistEq.bind_const _ _).trans
        ((OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _))
    exact (prEvent_map _ (fun z : Vector UInt8 48 × G.X => z.2.2)
      (fun d => ¬ good d)).symm.trans (e.prEvent_eq _)
  have hag : ∀ z : Vector UInt8 48 × G.X, ¬ ¬ good z.2.2 → F z = Gf z := by
    rintro ⟨kp, ⟨iv, r⟩, d⟩ hz
    have hg : good d := not_not.mp hz
    obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
    have hTeq : tagged (S := 𝒯) macS M d.cs.1 d.o d.c (default, iv, r)
        = tagged (S := 𝒯) macS M d.cs.1 d.o d.c (kp, iv, r) := by
      unfold tagged restOf
      dsimp only
      rw [hMkp d.cs.1 d.o d.c default kp iv r.2]
    have hTsize : (tagged (S := 𝒯) macS M d.cs.1 d.o d.c (kp, iv, r)).size
        = geom.headerLength := by
      unfold tagged
      rw [ByteArray.size_append, hsize d _ hg, Cryptlib.Util.Bytes.size_ofVector, hmactag, hhdr]
      rfl
    have hHd : ofVector (G.header ((iv, r), d))
        = tagged (S := 𝒯) macS M d.cs.1 d.o d.c (kp, iv, r) := by
      show ofVector (Util.Bytes.toVecN _ _) = _
      rw [hTeq]
      exact Cryptlib.Util.Bytes.ofVector_toVecN _ hTsize
    have hcar : ∀ pkt : ByteArray,
        pkt.extract 0 (payloadOffset kem geom) = ofVector (G.header ((iv, r), d))
          → carries kem d.c pkt = true := by
      intro pkt hp
      refine carries_of_extract kem d.c pkt ?_
      have h' := congrArg (fun x : ByteArray => x.extract 2 (2 + kem.ciphertextSize)) hp
      simp only [ByteArray.extract_extract] at h'
      rw [Nat.zero_add, Nat.zero_add, Nat.min_eq_left (by unfold payloadOffset; omega)] at h'
      rw [h', hHd]
      unfold tagged
      rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsize d _ hg]; omega)]
      exact hct d _ hg
    have hv := hview d (kp, iv, r) hg
    have hh : onlyHeader cipher macS streamS geom (tagged (S := 𝒯) macS M)
          d.cs.1 d.o d.c (kp, iv, r)
        = fun pkt => if pkt.extract 0 (payloadOffset kem geom)
              = ofVector (G.header ((iv, r), d))
            then procKeys kem cipher macS streamS geom (kp, iv, r) pkt else none := by
      funext pkt
      unfold onlyHeader
      rw [hHd]
    have hsk : ∀ h, h ≠ Role.relay → d.cs.2.2.2 h = G.sk ((iv, r), d) h := fun h hr => by
      simp [G, forwardPayloadGame, hr]
    have hrel : G.sk ((iv, r), d) .relay = d.k.2 := by
      simp [G, forwardPayloadGame]
    have hvo := fun patch oa =>
      viaOracle_onlyHeader kem cipher macS kdfS streamS geom hvalid hmactag h16
      (G.sk ((iv, r), d)) d.c (kp, iv, r) (G.header ((iv, r), d)) hcar patch (α := Bool) oa
      d.cs.2.2.1
    simp only [hrel] at hvo
    show simulateQ (procImplF kem cipher macS kdfS streamS geom d.k.2 d.c
        (onlyHeader cipher macS streamS geom (tagged (S := 𝒯) macS M)
          d.cs.1 d.o d.c (kp, iv, r)))
      ((fun out : Bool => out) <$>
        (simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 d.cs.2.2.2
            (view d.cs.1 d.o d.c (kp, iv, r)).patch)
          (A.guess d.cs.2.1 (view d.cs.1 d.o d.c (kp, iv, r)).onion)).run' d.cs.2.2.1) = _
    rw [procImplF_eq_relayImpl, hh, hv, id_map',
      viaOracle_congr kem cipher macS kdfS streamS geom hvalid hmactag h16
        d.cs.2.2.2 (G.sk ((iv, r), d)) hsk]
    simp only [StateT.run'_eq, simulateQ_map]
    rw [hvo,
      headerRelays_payloadKey kem cipher macS kdfS streamS geom hvalid hmactag h16 _ _ kp default]
    rfl
  rw [h1, h2, ← hbad]
  exact abs_prEvent_bind_sub_le_bad mx F Gf (fun z => ¬ good z.2.2) hag

end ForwardPayload

end Cryptlib.Protocols.Sphinx.KEMSphinx
