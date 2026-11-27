/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLURelay

namespace Cryptlib.Protocols.RSOR

open OracleComp OracleSpec

variable {S : Scheme}

/-- The game that tells two worlds for a challenge of STI↔ apart. -/
def tailPair (w₀ w₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S)) : Property S where
  Challenge := TailChallenge
  world c b := match b with
    | false => w₀ c
    | true => w₁ c

/-- An adversary of one such game, against another. -/
def tailPair.cast {u₀ u₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S)}
    (w₀ w₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S))
    (A : (tailPair u₀ u₁).Adversary) : (tailPair w₀ w₁).Adversary :=
  ⟨A.State, A.choose, A.guess⟩

/-- An adversary of STI↔, against the game of its two worlds. -/
def tailPair.ofTail (A : (tailIndistinguishable (S := S)).Adversary) :
    (tailPair (fun c => (tailIndistinguishable (S := S)).world c false)
      (fun c => (tailIndistinguishable (S := S)).world c true)).Adversary :=
  ⟨A.State, A.choose, A.guess⟩

/-- STI↔ is the game of its two worlds. -/
theorem tailIndistinguishable_advantage_eq (names : Role → S.Name)
    (A : (tailIndistinguishable (S := S)).Adversary) :
    (tailIndistinguishable (S := S)).advantage names A
      = (tailPair (fun c => (tailIndistinguishable (S := S)).world c false)
        (fun c => (tailIndistinguishable (S := S)).world c true)).advantage names
          (tailPair.ofTail A) :=
  rfl

/-- **Two worlds through a world in the middle.** -/
theorem tailPair_advantage_le
    (w₀ w₁ w₂ : {hon : Honest S} → TailChallenge hon → ProbComp (World S)) (names : Role → S.Name)
    (A : (tailPair w₀ w₂).Adversary) :
    ((tailPair w₀ w₂).advantage names A).toReal
      ≤ ((tailPair w₁ w₂).advantage names (tailPair.cast w₁ w₂ A)).toReal
        + ((tailPair w₀ w₁).advantage names (tailPair.cast w₀ w₁ A)).toReal := by
  rw [Property.advantage_toReal, Property.advantage_toReal, Property.advantage_toReal]
  have e1 : Property.play names (tailPair.cast w₁ w₂ A) true = Property.play names A true := rfl
  have e2 : Property.play names (tailPair.cast w₁ w₂ A) false
      = Property.play names (tailPair.cast w₀ w₁ A) true := rfl
  have e3 : Property.play names (tailPair.cast w₀ w₁ A) false = Property.play names A false :=
    rfl
  rw [e1, e2, e3]
  exact abs_sub_le _ _ _

/-- Worlds that are the same in distribution give the same game. -/
theorem tailPair_play_congr
    (w₀ w₁ u₀ u₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S))
    (h₀ : ∀ {hon : Honest S} (c : TailChallenge hon), w₀ c =ᵈ u₀ c)
    (h₁ : ∀ {hon : Honest S} (c : TailChallenge hon), w₁ c =ᵈ u₁ c)
    (names : Role → S.Name) (A : (tailPair w₀ w₁).Adversary) (b : Bool) :
    Property.play names A b =ᵈ Property.play names (tailPair.cast u₀ u₁ A) b := by
  unfold Property.play Property.playFrom
  refine EvalDistEq.bind_right _ fun kr => EvalDistEq.bind_right _ fun kb =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun out => ?_
  cases b
  · exact (h₀ out.1.1).bind_left _
  · exact (h₁ out.1.1).bind_left _

end Cryptlib.Protocols.RSOR

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.NIKESphinx (HopKeys deriveHopKeys)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # STI↔ for KEM Sphinx

World 0 of STI↔ shows a layer of the adversary's onion from a forward position on; world 1
shows the first layer of an onion over the rest of the forward path. A layer from a position on
is a layer over the rest of the path, with the filler there as the rest's padding.

The two worlds are compared through worlds in the middle (`tailPair`). -/

section RestOfForward

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

omit cipher macS in
/-- The fillers from position `j` on are the fillers built on the rest of the path from the
filler at `j`. -/
theorem fillerAt_drop (hops : Array PathHop) (seeds : Array (Vector UInt8 32))
    (filler : ByteArray) (j i : ℕ) :
    RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i)
      = RSOR.fillerAt kem kdfS streamS geom (hops.extract j hops.size)
        (seeds.extract j seeds.size) (RSOR.fillerAt kem kdfS streamS geom hops seeds filler j)
        i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i + 1) = _
    simp only [RSOR.fillerAt]
    rw [ih, extract_tail_tail hops j i, extract_tail_tail seeds j i]

/-- **A layer from a position on is a layer over the rest of the path**, when the seeds from
there on are the rest's seeds and the filler there is the rest's padding. -/
theorem layer_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (d d' : RSOR.Draw geom) (payload : ByteArray) (j i : ℕ)
    (hj : j ≤ R.hops.length)
    (hseeds : (d.1.toArray.extract 0 (RSOR.path kem R last).size).extract j
        (d.1.toArray.extract 0 (RSOR.path kem R last).size).size
      = d'.1.toArray.extract 0 (RSOR.path kem (R.drop j) last).size)
    (hfill : RSOR.fillerAt kem kdfS streamS geom (RSOR.path kem R last)
        (d.1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector d.2).extract 0
          ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j
      = (ofVector d'.2).extract 0
        ((geom.nrHops - (RSOR.path kem (R.drop j) last).size)
          * geom.perHopRoutingInfoLength)) :
    RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload (j + i)
      = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop j) last) d' payload
        i := by
  unfold RSOR.layer
  dsimp only
  rw [fillerAt_drop, hfill,
    extract_tail_tail (d.1.toArray.extract 0 (RSOR.path kem R last).size) j i,
    extract_tail_tail (RSOR.path kem R last) j i, hseeds,
    path_extract_drop kem geom R last j hj]

/-- The keystream that makes the layers after a hop, under a joined draw, the layers over the
rest of the path under the second draw: its tail sets the next layer's filler to the second
draw's padding. Its head is the given keystream's. -/
def fwdShift (hops : Array PathHop) (D dS : RSOR.Draw geom) (j : ℕ) (U : ByteArray) :
    ByteArray :=
  (xorBytes (U.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)) (zeroBytes
      (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)))
    ++ (xorBytes ((ofVector dS.2).extract ((geom.nrHops - hops.size) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) +
        (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom hops (D.1.toArray.extract 0 hops.size)
        ((ofVector D.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)) j
            (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector D.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)).size
            (((ofVector D.2).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)).size + (j + 1) * geom.perHopRoutingInfoLength)))

omit cipher macS in
/-- A game that reads two uniform draws through their join and what it leaves over reads two
uniform draws. -/
theorem evalDistEq_joinDraw {δ : Type} (j a : ℕ)
    (K : RSOR.Draw geom → RSOR.Draw geom → ProbComp δ) :
    (do
      let d ← $ᵗ (RSOR.Draw geom)
      let d' ← $ᵗ (RSOR.Draw geom)
      K (joinDraw geom d d' j a) (coJoin geom d d' j a))
      =ᵈ (do
        let d ← $ᵗ (RSOR.Draw geom)
        let d' ← $ᵗ (RSOR.Draw geom)
        K d d') := by
  have hb : Function.Bijective (Function.uncurry fun (d d' : RSOR.Draw geom) =>
      (joinDraw geom d d' j a, coJoin geom d d' j a)) :=
    Function.Involutive.bijective fun p => by
      obtain ⟨d, d'⟩ := p
      simp only [Function.uncurry, joinDraw_joinDraw, coJoin_coJoin]
  have hid : Function.Bijective (Function.uncurry fun (x y : RSOR.Draw geom) => (x, y)) :=
    Function.bijective_id
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hb fun p => K p.1 p.2) ?_
  exact (evalDistEq_pair_of_bijective hid fun p => K p.1 p.2).symm

set_option maxHeartbeats 2000000 in
/-- **The forward path past a hop, relabelled.** On a path with the joined draw and the shifted
keystream, the layers after the keyed hop are the layers over the rest of the path with the
second draw. -/
theorem fwdShift_spec (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (last : List RoutingCommand)
    (d dS : RSOR.Draw geom) (payload : ByteArray) (j a : ℕ) (U : ByteArray)
    (ha : a = ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) (hj : j
        + 1 < R.hops.length) (hU : U.size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) (i : ℕ)
    (hi : j + 1 + i ≤ R.hops.length) :
    layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j a)
        payload j
        (fwdShift kem kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j a) dS j U) (j
            + 1 + i)
      = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) dS
          payload i := by
  subst ha
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hsz0 : (RSOR.path kem R last).size = R.hops.length := RSOR.path_size kem R last
  have hszS : (RSOR.path kem (R.drop (j + 1)) last).size = R.hops.length - (j + 1) := by
    rw [RSOR.path_size]
    simp [Protocols.RSOR.Route.drop]
  have hj0 : j + 1 < (RSOR.path kem R last).size := lt_of_lt_of_eq hj hsz0.symm
  have hlen0 : (RSOR.path kem R last).size ≤ geom.nrHops := le_of_eq_of_le hsz0 hle
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hpad : ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + (j +
      1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [← Nat.add_mul, hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hpadS : ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + (j +
      1) * geom.perHopRoutingInfoLength = ((geom.nrHops - (RSOR.path kem (R.drop (j + 1))
      last).size) * geom.perHopRoutingInfoLength) := by
    rw [← Nat.add_mul, hszS]
    congr 1
    omega
  have hf : ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength)).size = ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hT : ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength)).size
      = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hseeds := joinDraw_extract_after geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (RSOR.path kem R last).size hlen0
  rw [show (RSOR.path kem R last).size - (j + 1) = (RSOR.path kem (R.drop (j + 1)) last).size by rw
      [hszS, hsz0]] at hseeds
  have hH : (xorBytes (U.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
      (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))).size
      = (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
          geom.perHopRoutingInfoLength := by
    rw [size_xorBytes, ByteArray.size_extract, hU, Nat.succ_mul]
    rw [Nat.succ_mul] at hjp
    omega
  have hfill : fillerAtF kem kdfS streamS geom (RSOR.path kem R last)
        ((joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).1.toArray.extract 0 (RSOR.path kem R last).size)
            ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j
        (fwdShift kem kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j ((geom.nrHops
            - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) dS j U) (j + 1)
      = (ofVector dS.2).extract 0 ((geom.nrHops - (RSOR.path kem (R.drop (j + 1)) last).size) *
          geom.perHopRoutingInfoLength) := by
    unfold fwdShift
    rw [fillerAtF_target kem geom kdfS streamS hrouting _ _ _ j _ _ hH hT hlen0 hj0 hf,
      joinDraw_prefix, ← hpadS]
    exact extract_adjacent _ 0 _ _ (Nat.zero_le _) (Nat.le_add_right _ _)
      (by rw [Util.Bytes.size_ofVector]; exact hpad)
  exact layerPast_drop kem geom kdfS streamS cipher macS R last (joinDraw geom d dS j ((geom.nrHops
      - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) dS payload j _ hseeds
    hfill i hi

set_option maxHeartbeats 4000000 in
/-- **The relabelled draws are uniform, on the forward path.** A game that reads two draws
through their join, and the keystream through the shifted keystream, reads one draw and one
keystream. -/
theorem evalDistEq_fwdShift {δ : Type} (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (last : List RoutingCommand)
    (j : ℕ) (hj : j + 1 < R.hops.length)
    (K : Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength) → RSOR.Draw geom →
        ProbComp δ) :
    (do
      let d ← $ᵗ (RSOR.Draw geom)
      let dS ← $ᵗ (RSOR.Draw geom)
      let U ← $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength))
      K (Util.Bytes.toVecN _ (fwdShift kem kdfS streamS geom (RSOR.path kem R last) (joinDraw geom
          d dS j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)) dS j
          (ofVector U))) (joinDraw geom d dS j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)))
      =ᵈ (do
        let D ← $ᵗ (RSOR.Draw geom)
        let U ← $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength))
        K U D) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hat : ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength) + ((j + 1) *
      geom.perHopRoutingInfoLength) ≤ geom.routingInfoLength := by
    rw [← Nat.add_mul, hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hm : (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) + ((j + 1) *
      geom.perHopRoutingInfoLength) = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := by
    rw [Nat.succ_mul] at hjp ⊢
    omega
  have e := evalDistEq_joinDraw geom j ((geom.nrHops - R.hops.length) *
      geom.perHopRoutingInfoLength) (fun D D' =>
    $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)) >>= fun U =>
      K (Util.Bytes.toVecN _ (fwdShift kem kdfS streamS geom (RSOR.path kem R last) D
        (coJoin geom D D' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)) j
            (ofVector U))) D)
  simp only [coJoin_coJoin] at e
  refine EvalDistEq.trans e (EvalDistEq.bind_right _ fun D => ?_)
  have hg : Function.Bijective (Function.uncurry fun (P : Vector UInt8 geom.routingInfoLength)
      (q : Vector (Vector UInt8 32) geom.nrHops) => ((q, P) : RSOR.Draw geom)) :=
    ⟨fun x y h => by
      obtain ⟨P, q⟩ := x
      obtain ⟨P', q'⟩ := y
      simp only [Function.uncurry, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      rfl, fun r => ⟨(r.2, r.1), rfl⟩⟩
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hg fun D' =>
    $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)) >>= fun U =>
      K (Util.Bytes.toVecN _ (fwdShift kem kdfS streamS geom (RSOR.path kem R last) D
        (coJoin geom D D' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)) j
            (ofVector U))) D).symm ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun q => ?_)
    (OracleComp.EvalDistEq.bind_const _ _)
  have key : ∀ (P : Vector UInt8 geom.routingInfoLength) (U : Vector UInt8 (geom.routingInfoLength
      + geom.perHopRoutingInfoLength)),
      fwdShift kem kdfS streamS geom (RSOR.path kem R last) D (coJoin geom D (q, P) j ((geom.nrHops
          - R.hops.length) * geom.perHopRoutingInfoLength)) j (ofVector U)
      = xorBytes ((ofVector U).extract 0 (geom.routingInfoLength - j *
          geom.perHopRoutingInfoLength))
          ((fun (_ : Vector UInt8 geom.routingInfoLength) (_ : ByteArray) =>
            zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)) P ((ofVector
                U).extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
                (geom.routingInfoLength + geom.perHopRoutingInfoLength)))
        ++ xorBytes ((ofVector P).extract ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength) (((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength) + ((j + 1) * geom.perHopRoutingInfoLength)))
          ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) (D.1.toArray.extract 0
              R.hops.length)
        ((ofVector D.2).extract 0 ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)) j
            (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector D.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).size (((ofVector D.2).extract 0 ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)) := fun P U => by
    have hreg : (ofVector (coJoin geom D (q, P) j ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength)).2).extract ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength)
          (((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength) + (j + 1) *
              geom.perHopRoutingInfoLength)
        = (ofVector P).extract ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)
            (((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength) + ((j + 1) *
            geom.perHopRoutingInfoLength)) :=
      coJoin_region geom _ _ j _ _
    unfold fwdShift
    simp only [RSOR.path_size]
    rw [hreg]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun P => EvalDistEq.bind_right _ fun U => ?_)
    (evalDistEq_headRegion hat hm
    (fun (_ : Vector UInt8 geom.routingInfoLength) (_ : ByteArray) => zeroBytes
        (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
    ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) (D.1.toArray.extract 0 R.hops.length)
        ((ofVector D.2).extract 0 ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)) j
            (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector D.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).size (((ofVector D.2).extract 0 ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)) (fun U₀ => K U₀ D))
  rw [key P U]

omit cipher macS in
/-- The shifted keystream is as long as a keystream. -/
theorem fwdShift_size (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (last : List RoutingCommand)
    (D dS : RSOR.Draw geom) (j : ℕ) (hj : j + 1 < R.hops.length) (U : ByteArray)
    (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) :
    (fwdShift kem kdfS streamS geom (RSOR.path kem R last) D dS j U).size = (geom.routingInfoLength
        + geom.perHopRoutingInfoLength) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hat : ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength) + (j + 1) *
      geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [← Nat.add_mul, hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold fwdShift
  simp only [RSOR.path_size]
  rw [ByteArray.size_append, size_xorBytes, size_xorBytes, ByteArray.size_extract,
    ByteArray.size_extract, hU, Util.Bytes.size_ofVector]
  rw [Nat.succ_mul] at hjp hat ⊢
  omega

end RestOfForward

section TailGame

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- The first layer of an onion over the rest of the forward path, with the forward draw `d`,
around the payload of the adversary's onion. The honest backward relay answers nothing to the
reply's layer, as in world 0. -/
def tailMidWorld {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (d : RSOR.Draw geom) : Protocols.RSOR.World 𝒮 where
  onion :=
    (match RSOR.layer kem cipher macS kdfS streamS geom
        (RSOR.path kem (c.req.fwd.drop c.pos) [.recipient c.req.receiver]) d
        (RSOR.body kem macS kdfS streamS geom c.req r) 0 with
    | .ok pkt => RSOR.split geom pkt
    | .error _ => (default : RSOR.Onion geom))
  patch := (Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back).patch

/-- **The world in the middle of STI↔**: `tailMidWorld` with its draws. The payload still
carries the SURB over the whole backward path. -/
def tailMid {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    ProbComp (Protocols.RSOR.World 𝒮) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let d ← $ᵗ (RSOR.Draw geom)
  return tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d

/-- The challenger's randomness with the seed `s` at the forward hop before position `pos`. -/
def tailSeed (pos : ℕ) (r : RSOR.Randomness geom) (s : Vector UInt8 32) : RSOR.Randomness geom :=
  match pos with
  | 0 => r
  | k + 1 => setSeed geom r k s

omit kem cipher macS kdfS streamS hvalid hmactag h16 in
/-- Drawing the challenger's randomness and a seed, and putting the seed at the hop before the
shown layer, is drawing the randomness. -/
theorem evalDistEq_tailSeed {δ : Type} (pos : ℕ) (hpos : pos ≤ geom.nrHops)
    (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (tailSeed geom pos r s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  cases pos with
  | zero =>
    exact EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r)
  | succ k => exact evalDistEq_setSeed geom k (by omega) K

/-- The hop before the shown layer needs no further step: there is none, or it is the honest
relay with a role in `done`. -/
def tailDone {hon : Protocols.RSOR.Honest 𝒮} (done : Role → Bool)
    (c : Protocols.RSOR.TailChallenge hon) : Prop :=
  c.pos.val = 0
    ∨ ∃ ρ, done ρ = true ∧ ∃ k, k + 1 = c.pos.val ∧ c.req.fwd.hops[k]? = some (hon ρ)

open Classical in
/-- **A world between world 0 and the world in the middle**, from its draws: the middle world
when the hop before the shown layer needs no further step, and world 0 otherwise. -/
noncomputable def tailHybWorld (done : Role → Bool) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) (r : RSOR.Randomness geom) (d : RSOR.Draw geom) :
    Protocols.RSOR.World 𝒮 :=
  if tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 done c then tailMidWorld kem
      cipher macS kdfS streamS geom hvalid hmactag h16 c r d
  else Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back

/-- That world with its draws. -/
noncomputable def tailHyb (done : Role → Bool) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) : ProbComp (Protocols.RSOR.World 𝒮) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let d ← $ᵗ (RSOR.Draw geom)
  return tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 done c r d

/-- With both roles the relay before the shown layer can have handled, the hybrid is the world
in the middle. -/
theorem tailHyb_all {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun ρ => ρ == .relay || ρ ==
        .back) c = tailMid kem cipher macS kdfS streamS geom hvalid hmactag h16 c := by
  have hd : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun ρ => ρ == .relay ||
      ρ == .back) c := by
    by_cases hp : c.pos.val = 0
    · exact Or.inl hp
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp
      rcases c.relay k hk.symm with h | h
      · exact Or.inr ⟨.relay, rfl, k, hk.symm, h⟩
      · exact Or.inr ⟨.back, rfl, k, hk.symm, h⟩
  unfold tailHyb tailHybWorld tailMid
  simp only [hd, ite_true]

/-- The middle world reads the challenger's randomness through its backward part only. -/
theorem tailMidWorld_congr {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) (r r' : RSOR.Randomness geom) (d : RSOR.Draw geom)
    (h : r.2 = r'.2) :
    tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d = tailMidWorld kem
        cipher macS kdfS streamS geom hvalid hmactag h16 c r' d := by
  obtain ⟨a, b⟩ := r
  obtain ⟨a', b'⟩ := r'
  obtain rfl : b = b' := h
  rfl

/-- When the shown layer is the first, world 0 is the middle world with the challenger's own
forward draw. -/
theorem tailWorld_zero {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (hp : c.pos.val = 0) :
    Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back
      = tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r r.1 := by
  unfold Protocols.RSOR.tailWorld tailMidWorld
  congr 1
  show RSOR.form kem cipher macS kdfS streamS geom c.req r c.pos = _
  unfold RSOR.form
  rw [hp]
  rfl

set_option maxHeartbeats 2000000 in
/-- **World 0 is the hybrid with no role handled.** When the shown layer is the first there is
no relay before it, and world 0 is the middle world after renaming the forward draw. -/
theorem tailWorld_evalDistEq_tailHyb {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) :
    (Protocols.RSOR.tailIndistinguishable (S := 𝒮)).world c false
      =ᵈ tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun _ => false) c := by
  have hw : (Protocols.RSOR.tailIndistinguishable (S := 𝒮)).world c false
      = ($ᵗ (RSOR.Randomness geom) >>= fun r =>
        pure (Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back)) := by
    simp [Protocols.RSOR.tailIndistinguishable]
    rfl
  rw [hw]
  unfold tailHyb tailHybWorld
  by_cases hp : c.pos.val = 0
  · have hd : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun _ => false) c :=
      Or.inl hp
    simp only [hd, ite_true]
    have e : ∀ (r : RSOR.Randomness geom) (d : RSOR.Draw geom),
        tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d = tailMidWorld kem
            cipher macS kdfS streamS geom hvalid hmactag h16 c (default, r.2) d :=
      fun r d => tailMidWorld_congr kem cipher macS kdfS streamS geom hvalid hmactag h16 c r _ d rfl
    simp only [tailWorld_zero kem cipher macS kdfS streamS geom hvalid hmactag h16 c _ hp]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r => by rw [e r r.1]) ?_
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_right _ fun r =>
      EvalDistEq.bind_right _ fun d => by rw [e r d]).symm
    refine EvalDistEq.trans (evalDistEq_pair_of_bijective
      (g := fun (x : RSOR.Draw geom) (y : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16) =>
        (x, y)) Function.bijective_id
      (fun r : RSOR.Randomness geom =>
        (pure (tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c (default, r.2)
            r.1) :
          ProbComp (Protocols.RSOR.World 𝒮)))).symm ?_
    refine EvalDistEq.trans ?_ (evalDistEq_snd (α := RSOR.Draw geom)
      (fun b : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16 =>
        $ᵗ (RSOR.Draw geom) >>= fun d =>
          (pure (tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c (default, b)
              d) :
            ProbComp (Protocols.RSOR.World 𝒮)))).symm
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  · have hd : ¬ tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun _ => false) c :=
      fun h => by
      rcases h with h | ⟨ρ, h, -⟩
      · exact hp h
      · cases h
    simp only [hd, ite_false]
    exact (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (RSOR.Draw geom)) _).symm

/-- The hop before the shown layer is the honest relay with the role `ρ`. -/
def tailRho {hon : Protocols.RSOR.Honest 𝒮} (ρ : Role) (c : Protocols.RSOR.TailChallenge hon) :
    Prop :=
  ∃ k, k + 1 = c.pos.val ∧ c.req.fwd.hops[k]? = some (hon ρ)

open Classical in
/-- The challenger's randomness with the seed `s` at the hop before the shown layer, when that
hop is the honest relay with the role `ρ`. -/
noncomputable def tailSeedFor {hon : Protocols.RSOR.Honest 𝒮} (ρ : Role)
    (c : Protocols.RSOR.TailChallenge hon) (r : RSOR.Randomness geom) (s : Vector UInt8 32) :
    RSOR.Randomness geom :=
  if tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c then tailSeed geom c.pos r s
      else r

/-- Drawing the randomness and a seed, and putting the seed at that hop, is drawing the
randomness. -/
theorem evalDistEq_tailSeedFor {δ : Type} {hon : Protocols.RSOR.Honest 𝒮} (ρ : Role)
    (c : Protocols.RSOR.TailChallenge hon) (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (tailSeedFor kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c r s)) =ᵈ ($ᵗ
          (RSOR.Randomness geom) >>= K) := by
  unfold tailSeedFor
  by_cases h : tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c
  · simp only [h, ite_true]
    exact evalDistEq_tailSeed geom c.pos
      (le_of_lt (lt_of_lt_of_le c.pos.isLt c.req.fwd.length_le)) K
  · simp only [h, ite_false]
    exact EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r)

open Classical in
/-- **A hybrid world from the keystream of the hop before the shown layer**, when that hop is
the honest relay with the role `ρ` and still needs its step: the shown layer is then a layer
past that hop. Otherwise the hybrid world itself. -/
noncomputable def tailViewU (done : Role → Bool) (ρ : Role)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (o : RSOR.Randomness geom × RSOR.Draw geom) (U : ByteArray) : Protocols.RSOR.World 𝒮 :=
  if tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 done c then tailMidWorld kem
      cipher macS kdfS streamS geom hvalid hmactag h16 c o.1 o.2
  else if tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c then
    { onion :=
        (match layerPast kem cipher macS kdfS streamS geom
            (RSOR.path kem c.req.fwd [.recipient c.req.receiver]) o.1.1
            (RSOR.body kem macS kdfS streamS geom c.req o.1) (c.pos.val - 1) U c.pos.val with
        | .ok pkt => RSOR.split geom pkt
        | .error _ => (default : RSOR.Onion geom))
      patch := (Protocols.RSOR.tailWorld (S := 𝒮) c.req o.1 c.pos c.back).patch }
  else Protocols.RSOR.tailWorld (S := 𝒮) c.req o.1 c.pos c.back

/-- Putting a seed at the hop before the shown layer leaves the backward part of the
randomness as it is. -/
theorem tailSeedFor_snd {hon : Protocols.RSOR.Honest 𝒮} (ρ : Role)
    (c : Protocols.RSOR.TailChallenge hon) (r : RSOR.Randomness geom) (s : Vector UInt8 32) :
    (tailSeedFor kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c r s).2 = r.2 := by
  unfold tailSeedFor tailSeed
  split_ifs
  · split <;> rfl
  · rfl

set_option maxHeartbeats 2000000 in
/-- **The keyed view with the real keys is the hybrid world.** With the keystream of the keys
that the seed `s` gives at the hop before the shown layer, `tailViewU` is the hybrid world at
the randomness with `s` at that hop. -/
theorem tailViewU_real (done : Role → Bool) (ρ : Role) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) (o : RSOR.Randomness geom × RSOR.Draw geom)
    (s : Vector UInt8 32) (ct ss : ByteArray)
    (henc : tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c → kemEncap kem
      ((RSOR.path kem c.req.fwd [.recipient c.req.receiver])[c.pos.val - 1]!).publicKey s
      = .ok (ct, ss)) :
    tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 done ρ c o (ksOf streamS geom
        (keyTuple (deriveHopKeys kdfS ss)))
      = tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 done c (tailSeedFor kem
          cipher macS kdfS streamS geom hvalid hmactag h16 ρ c o.1 s) o.2 := by
  unfold tailViewU tailHybWorld
  by_cases hd : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 done c
  · simp only [hd, ite_true]
    exact tailMidWorld_congr kem cipher macS kdfS streamS geom hvalid hmactag h16 c _ _ _
        (tailSeedFor_snd kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c o.1 s).symm
  · simp only [hd, ite_false]
    by_cases hρ : tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c
    · obtain ⟨k, hk, -⟩ := id hρ
      have henc := henc hρ
      have hlt : c.pos.val < c.req.fwd.hops.length := c.pos.isLt
      have hle := c.req.fwd.length_le
      have hsd : tailSeedFor kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c o.1 s =
          setSeed geom o.1 k s := by
        unfold tailSeedFor tailSeed
        simp only [hρ, ite_true]
        rw [← hk]
      rw [hsd]
      simp only [hρ, ite_true]
      rw [← hk, Nat.add_sub_cancel] at henc ⊢
      rw [layerPast_real kem cipher macS kdfS streamS geom _ _ _ k (k + 1) s ct ss
          (Nat.lt_succ_self k)
        (le_of_le_of_eq (show k + 1 ≤ c.req.fwd.hops.length by omega)
          (RSOR.path_size kem c.req.fwd _).symm)
        (le_of_eq_of_le (RSOR.path_size kem c.req.fwd _) hle) henc]
      unfold Protocols.RSOR.tailWorld
      congr 1
      show _ = RSOR.form kem cipher macS kdfS streamS geom c.req (setSeed geom o.1 k s) c.pos
      unfold RSOR.form
      rw [← hk]
      rfl
    · unfold tailSeedFor
      simp only [hρ, ite_false]

/-- The draws of a hybrid world. -/
def hybDraw : ProbComp (RSOR.Randomness geom × RSOR.Draw geom) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let d ← $ᵗ (RSOR.Draw geom)
  return (r, d)

set_option maxHeartbeats 2000000 in
/-- **A hybrid world as its draws**, with the seed of the hop before the shown layer drawn on
its own when that hop is the honest relay with the role `ρ`, and then the adversary's guess
against the honest relays. -/
theorem tail_play_evalDistEq (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} →
    Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn : Role → Bool) (b : Bool)
    (hw : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      (Protocols.RSOR.tailPair w₀ w₁).world c b = tailHyb kem cipher macS kdfS streamS geom hvalid
          hmactag h16 dn c)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    Protocols.RSOR.Property.play names A b
      =ᵈ propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair
          w₀ w₁) ρ names _ (hybDraw geom) A >>= fun d =>
        (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names d.k.1 d.keys)
            (fun h => if h = ρ then d.k.2 else (d.keys h).2)
            (tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 dn d.c
              (tailSeedFor kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ d.c d.o.1 d.s)
                  d.o.2).patch)
          (A.guess d.st (tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 dn d.c
            (tailSeedFor kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ d.c d.o.1 d.s)
                d.o.2).onion)).run' d.log := by
  refine (play_evalDistEq_honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.tailPair w₀ w₁) ρ names A b).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  refine (hcong _ _ _ (hw out.1.1)).trans ?_
  unfold tailHyb
  simp only [hybDraw, bind_assoc, pure_bind]
  refine EvalDistEq.symm ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_tailSeedFor kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ out.1.1 fun r
      =>
    $ᵗ (RSOR.Draw geom) >>= fun d =>
      (simulateQ (Protocols.RSOR.honest
          (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf kem ρ k₁
              k₂))
          (fun h => if h = ρ then k.2 else (keysOf kem ρ k₁ k₂ h).2)
          (tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 dn out.1.1 r d).patch)
        (A.guess out.1.2 (tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 dn
            out.1.1 r d).onion)).run' out.2

/-- The draws on which a hybrid world is not the keyed game with the real keys: the relay's
key pair is not a key pair, or the encapsulation to it fails or cannot be undone. -/
def hybBad {w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)} {ρ : Role} {names : Role → RSOR.Name}
    {A : (Protocols.RSOR.tailPair w₀ w₁).Adversary}
    (d : PropDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀
        w₁) ρ names (RSOR.Randomness geom × RSOR.Draw geom) A) : Prop :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s)
    ∧ ∃ ct ss, kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss))

variable [SampleableType kem.Plaintext]

set_option maxHeartbeats 2000000 in
/-- **A hybrid world is the keyed game with the real keys, off the bad draws.** -/
theorem tail_sub_keyedReal_le (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} →
    Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn : Role → Bool) (b : Bool)
    (hw : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      (Protocols.RSOR.tailPair w₀ w₁).world c b = tailHyb kem cipher macS kdfS streamS geom hvalid
          hmactag h16 dn c)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A b}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair
              w₀ w₁) ρ names _ (hybDraw geom)
            (fun ch o _ t => tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ
                ch.c o (ksOf streamS geom t)) A))}[x = true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.tailPair w₀ w₁) ρ names _ (hybDraw geom)
        A)}[hybBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  rw [(tail_play_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn b hw
      names A).prEvent_eq (fun x => x = true),
    (keyedReal_propAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.tailPair w₀ w₁) ρ names _ _ _ A).prEvent_eq
      (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _ (hybBad kem cipher macS kdfS streamS geom hvalid
      hmactag h16) (fun d hd => ?_)
    (fun x => x = true)
  obtain ⟨hpk, hrel, ct, ss, henc⟩ := Classical.not_not.mp hd
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
  have hdec : decapOf kem d.k.2 (encapOf kem d.k.1.1 d.s).1
      = some (encapOf kem d.k.1.1 d.s).2 := by
    have h := decapOf_encapOf kem d.k.2 d.s hrel _ _ (hpk ▸ henc)
    rwa [← hpk] at h
  have hview := tailViewU_real kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ d.c d.o
      d.s _ _ (fun hρ => by
    obtain ⟨k, hk, hh⟩ := hρ
    have hklt : k < d.c.req.fwd.hops.length := by
      have := d.c.pos.isLt
      omega
    have h1 : d.c.req.fwd.hops[k]'hklt = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
        ρ names d.k.1 d.keys ρ :=
      Option.some.inj ((List.getElem?_eq_getElem hklt).symm.trans hh)
    have hpub : ((RSOR.path kem d.c.req.fwd [.recipient d.c.req.receiver])[k]!).publicKey
        = ofVector (kem.encodePublicKey d.k.1.1) := by
      rw [RSOR.path_getElem! kem _ _ _ hklt]
      show ofVector (kem.encodePublicKey (d.c.req.fwd.hops[k]'hklt).key.1) = _
      rw [h1]
      simp [honAt]
    rw [← hk, Nat.add_sub_cancel, hpub]
    exact henc)
  rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀
      w₁) ρ names _ _ _ A d.k d.keys _ _ hdec d.st d.log _, ← hview]
  rfl

omit [SampleableType kem.Plaintext] in
/-- With the role `ρ` handled too, the hop needs no further step when it needed none before or
is the honest relay with the role `ρ`. -/
theorem tailDone_or (dn : Role → Bool) (ρ : Role) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) :
    tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => dn x || x == ρ) c
      ↔ tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 dn c ∨ tailRho kem cipher
          macS kdfS streamS geom hvalid hmactag h16 ρ c := by
  unfold tailDone tailRho
  constructor
  · rintro (h0 | ⟨ρ', hd, hk⟩)
    · exact Or.inl (Or.inl h0)
    · rcases Bool.or_eq_true_iff.mp hd with h | h
      · exact Or.inl (Or.inr ⟨ρ', h, hk⟩)
      · exact Or.inr ((beq_iff_eq.mp h) ▸ hk)
  · rintro ((h0 | ⟨ρ', hd, hk⟩) | hk)
    · exact Or.inl h0
    · exact Or.inr ⟨ρ', Bool.or_eq_true_iff.mpr (Or.inl hd), hk⟩
    · exact Or.inr ⟨ρ, Bool.or_eq_true_iff.mpr (Or.inr (beq_self_eq_true ρ)), hk⟩

omit [SampleableType kem.Plaintext] in
/-- Where the hop before the shown layer is not the relay `ρ` still waiting for its step, the
keyed view is the next hybrid world, whatever the keystream. -/
theorem tailViewU_other (dn : Role → Bool) (ρ : Role) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) (o : RSOR.Randomness geom × RSOR.Draw geom)
    (U : ByteArray)
    (h : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 dn c ∨ ¬ tailRho kem cipher
        macS kdfS streamS geom hvalid hmactag h16 ρ c) :
    tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c o U
      = tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => dn x || x == ρ)
          c o.1 o.2 := by
  unfold tailViewU tailHybWorld
  by_cases hd : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 dn c
  · have hd' := (tailDone_or kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c).mpr
      (Or.inl hd)
    simp only [hd, hd', ite_true]
  · have hρ : ¬ tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c := h.resolve_left
      hd
    have hd' : ¬ tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => dn x || x
        == ρ) c := fun h' =>
      ((tailDone_or kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c).mp h').elim hd hρ
    simp only [hd, hd', hρ, ite_false]

omit [SampleableType kem.Plaintext] in
/-- Where the relay `ρ` still waits for its step, the keyed view does not read the forward
draw of the middle world. -/
theorem tailViewU_snd (dn : Role → Bool) (ρ : Role) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) (r : RSOR.Randomness geom) (d d' : RSOR.Draw geom)
    (U : ByteArray) (hd : ¬ tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 dn c) (hρ
        : tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c) :
    tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c (r, d) U = tailViewU kem
        cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c (r, d') U := by
  unfold tailViewU
  simp only [hd, hρ, ite_true, ite_false]

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- **The keyed view under the relabelled draws is the middle world.** -/
theorem tailViewU_shift (dn : Role → Bool) (ρ : Role) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) (k : ℕ) (hk : k + 1 = c.pos.val)
    (d dS d' : RSOR.Draw geom) (b : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16)
    (U : ByteArray) (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (hd : ¬ tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 dn c) (hρ : tailRho kem
        cipher macS kdfS streamS geom hvalid hmactag h16 ρ c) :
    tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c ((joinDraw geom d dS k
        ((geom.nrHops - c.req.fwd.hops.length) * geom.perHopRoutingInfoLength), b), d')
        (fwdShift kem kdfS streamS geom (RSOR.path kem c.req.fwd [.recipient c.req.receiver])
          (joinDraw geom d dS k ((geom.nrHops - c.req.fwd.hops.length) *
              geom.perHopRoutingInfoLength)) dS k U)
      = tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c (d, b) dS := by
  have hlt : c.pos.val < c.req.fwd.hops.length := c.pos.isLt
  have h := fwdShift_spec kem cipher macS kdfS streamS geom hvalid c.req.fwd [.recipient
      c.req.receiver] d dS
    (RSOR.body kem macS kdfS streamS geom c.req (joinDraw geom d dS k ((geom.nrHops -
        c.req.fwd.hops.length) * geom.perHopRoutingInfoLength), b)) k
    ((geom.nrHops - c.req.fwd.hops.length) * geom.perHopRoutingInfoLength) U
    (congrArg (fun n => (geom.nrHops - n) * geom.perHopRoutingInfoLength)
      (RSOR.path_size kem c.req.fwd [.recipient c.req.receiver]).symm)
    (lt_of_eq_of_lt hk hlt) hU 0 (le_of_lt (lt_of_eq_of_lt hk hlt))
  rw [Nat.add_zero] at h
  unfold tailViewU tailMidWorld
  simp only [hd, hρ, ite_true, ite_false]
  rw [← hk, Nat.add_sub_cancel, h]
  rfl

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 4000000 in
/-- **From a uniform keystream, a hybrid world is the next one.** The keyed view of the hybrid
with the roles `dn` handled, read with a uniform keystream, is the hybrid world with the role
`ρ` handled too. -/
theorem evalDistEq_tailViewU {δ : Type} (dn : Role → Bool) (ρ : Role)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (K : Protocols.RSOR.World 𝒮 → ProbComp δ) :
    (do
      let o ← hybDraw geom
      let U ← $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength))
      K (tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c o (ofVector U)))
      =ᵈ (do
        let o ← hybDraw geom
        K (tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => dn x || x ==
            ρ) c o.1 o.2)) := by
  by_cases h : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 dn c ∨ ¬ tailRho kem
      cipher macS kdfS streamS geom hvalid hmactag h16 ρ c
  · refine EvalDistEq.bind_right _ fun o => ?_
    simp only [tailViewU_other kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c o _ h]
    exact OracleComp.EvalDistEq.bind_const _ _
  · obtain ⟨hd, hρ⟩ := not_or.mp h
    have hρ : tailRho kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ c :=
        Classical.not_not.mp hρ
    obtain ⟨k, hk, -⟩ := id hρ
    have hlt : c.pos.val < c.req.fwd.hops.length := c.pos.isLt
    have hd' := (tailDone_or kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c).mpr
        (Or.inr hρ)
    have hid : Function.Bijective (Function.uncurry fun (a : RSOR.Draw geom)
        (b : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16) =>
        ((a, b) : RSOR.Randomness geom)) := Function.bijective_id
    unfold hybDraw tailHybWorld
    simp only [bind_assoc, pure_bind, hd', ite_true]
    -- the right side: split the randomness, the backward part first
    refine EvalDistEq.trans ?_ (evalDistEq_pair_of_bijective hid fun r =>
      $ᵗ (RSOR.Draw geom) >>= fun dS => K (tailMidWorld kem cipher macS kdfS streamS geom hvalid
          hmactag h16 c r dS))
    refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
    -- the left side: the same, and the forward draw is not read
    refine EvalDistEq.trans (evalDistEq_pair_of_bijective hid fun r =>
      $ᵗ (RSOR.Draw geom) >>= fun d' => $ᵗ (Vector UInt8 (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)) >>= fun U =>
        K (tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c (r, d') (ofVector
            U))).symm ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.bind_right _ fun b => ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a =>
      (show ($ᵗ (RSOR.Draw geom) >>= fun d' => $ᵗ (Vector UInt8 (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)) >>= fun U =>
          K (tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c ((a, b), d')
              (ofVector U)))
        =ᵈ ($ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)) >>= fun U =>
          K (tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c ((a, b), a)
              (ofVector U))) from by
        simp only [tailViewU_snd kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c (a, b)
            _ a _ hd hρ]
        exact OracleComp.EvalDistEq.bind_const _ _)) ?_
    refine EvalDistEq.trans (evalDistEq_fwdShift kem kdfS streamS geom hvalid c.req.fwd
      [.recipient c.req.receiver] k (lt_of_eq_of_lt hk hlt) (fun U a =>
        K (tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c ((a, b), a)
            (ofVector U)))).symm ?_
    refine EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun dS => ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U => ?_)
      (OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 (geom.routingInfoLength +
          geom.perHopRoutingInfoLength))) _)
    have hc : ∀ m m' : ProbComp δ, m = m' → m =ᵈ m' := fun _ _ h => h ▸ EvalDistEq.rfl
    refine hc _ _ (congrArg K ?_)
    rw [Util.Bytes.ofVector_toVecN _ (fwdShift_size kem kdfS streamS geom hvalid c.req.fwd _ _ _
        k (lt_of_eq_of_lt hk hlt) _ (Util.Bytes.size_ofVector U))]
    exact tailViewU_shift kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ c k hk d dS _ b
        _ (Util.Bytes.size_ofVector U) hd hρ

/-- The keyed game's adversary for one step of the hybrid. -/
noncomputable def tailKeyed (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge
    hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn : Role → Bool)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :=
  propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀ w₁) ρ
      names _ (hybDraw geom)
    (fun ch o _ t => tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ ch.c o
        (ksOf streamS geom t)) A

/-- **The game from a uniform keystream**: the adversary's guess for the hybrid world with the
roles `dn'` handled, with the honest relay `ρ` rejecting the hidden ciphertext. -/
noncomputable def tailUGame (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge
    hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn dn' : Role → Bool)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) : ProbComp Bool := do
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2) ((tailKeyed kem cipher macS
      kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A).pre k.1)
  let s' ← $ᵗ (Vector UInt8 32)
  let o ← hybDraw geom
  simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1 (fun _ =>
      none))
    ((tailKeyed kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A).post cs.2
        (tailHybWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 dn' cs.1.c o.1 o.2))

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- The keystream generator's ideal experiment for one step of the hybrid is the game from a
uniform keystream with the role `ρ` handled too. -/
theorem tailUniform_evalDistEq (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} →
    Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn : Role → Bool)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    PRGScheme.prgIdealExperiment (rejectStreamAdv kem cipher macS kdfS streamS geom (tailKeyed kem
        cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A)
        (fun ch o _ U => tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ ch.c o
            U) (fun _ _ _ out => out))
      =ᵈ tailUGame kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn (fun x => dn x
          || x == ρ) names A := by
  unfold PRGScheme.prgIdealExperiment rejectStreamAdv tailUGame
  simp only [id_map']
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun k => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun cs => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun s' => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ cs.1.c fun w
      =>
    simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1 (fun _ =>
        none))
      ((tailKeyed kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A).post
          cs.2 w)

omit [SampleableType kem.Plaintext] in
/-- The game from a uniform keystream does not read the keyed view. -/
theorem tailUGame_view (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn₁ dn₂ dn' : Role → Bool)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    tailUGame kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn₁ dn' names A =
        tailUGame kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn₂ dn' names A := by
  unfold tailUGame tailKeyed propAdvOf
  rfl

/-- **The cost of one side of a step of the hybrid**: the bad draws, the replacement of the
relay's keys, a MAC forgery, and the keystream generator's advantage. -/
noncomputable def tailStepCost (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} →
    Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn : Role → Bool)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) : ℝ :=
  (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.tailPair w₀ w₁) ρ names _ (hybDraw geom)
      A)}[hybBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
    + (keyedCost cipher macS kdfS streamS geom (tailKeyed kem cipher macS kdfS streamS geom hvalid
        hmactag h16 w₀ w₁ ρ dn names A)
      + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
          (tailKeyed kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A)
          (fun _ _ _ _ => nextM0 kem geom)
          (fun ch o _ rest _ => tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ
              ch.c o
            (ksOf streamS geom (withMAC rest default)))))}[x = true]).toReal
      + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (rejectStreamAdv kem cipher macS kdfS streamS geom (tailKeyed kem cipher macS kdfS
              streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A)
            (fun ch o _ U => tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ
                ch.c o U) (fun _ _ _ out => out)))}[x = true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (rejectStreamAdv kem cipher macS kdfS streamS geom (tailKeyed kem cipher macS kdfS
              streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A)
            (fun ch o _ U => tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ
                ch.c o U) (fun _ _ _ out => out)))}[x = true]).toReal|)

set_option maxHeartbeats 2000000 in
/-- **One side of a step of the hybrid.** A game whose world is the hybrid with the roles `dn`
handled is, up to the step's cost, the game from a uniform keystream with `ρ` handled too. -/
theorem tail_sub_uniform_le (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge
    hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn : Role → Bool) (b : Bool)
    (hw : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      (Protocols.RSOR.tailPair w₀ w₁).world c b = tailHyb kem cipher macS kdfS streamS geom hvalid
          hmactag h16 dn c)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A b}[x = true]).toReal
      - (Pr{let x ← (tailUGame kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn (fun
          x => dn x || x == ρ) names
          A)}[x = true]).toReal|
    ≤ tailStepCost kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A := by
  have h1 := tail_sub_keyedReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn
      b hw names A
  have h2 := keyedReal_sub_uniform_le kem cipher macS kdfS streamS geom hmactag (tailKeyed kem
      cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A)
    (fun ch o _ U => tailViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 dn ρ ch.c o U)
        (fun _ _ _ out => out)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  rw [← (tailUniform_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn
      names A).prEvent_eq (fun x => x = true)]
  unfold tailStepCost
  unfold tailKeyed at h2 ⊢
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

set_option maxHeartbeats 2000000 in
/-- **One step of the hybrid.** Handling the role `ρ` too changes the adversary's guess by at
most the step's cost on each side. -/
theorem tailStep_le (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)) (ρ : Role) (dn : Role → Bool)
    (hw0 : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      w₀ c = tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 dn c)
    (hw1 : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      w₁ c = tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => dn x || x == ρ)
          c)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    ((Protocols.RSOR.tailPair w₀ w₁).advantage names A).toReal
    ≤ tailStepCost kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn names A
      + tailStepCost kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ (fun x => dn x ||
          x == ρ) names A := by
  have h0 := tail_sub_uniform_le kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ dn
      false (fun c => hw0 c) names A
  have h1 := tail_sub_uniform_le kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ (fun
      x => dn x || x == ρ) true (fun c => hw1 c) names A
  have hdn : (fun x => (dn x || x == ρ) || x == ρ) = (fun x => dn x || x == ρ) :=
    funext fun x => by rw [Bool.or_assoc, Bool.or_self]
  rw [hdn, tailUGame_view kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ ρ (fun x => dn
      x || x == ρ) dn (fun x => dn x || x == ρ) names A] at h1
  rw [abs_sub_comm] at h0
  rw [Protocols.RSOR.Property.advantage_toReal names A]
  refine (abs_sub_le _ (Pr{let x ← (tailUGame kem cipher macS kdfS streamS geom hvalid hmactag h16
      w₀ w₁ ρ dn (fun x => dn x || x == ρ) names
    A)}[x = true]).toReal _).trans ?_
  rw [add_comm]
  exact add_le_add h0 h1

/-- **The cost of the first half of STI↔**: the two sides of the step for a relay on the forward
path, and of the step for the relay on both paths. -/
noncomputable def tailHalfCost (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.tailPair (S := 𝒮) (fun c => (Protocols.RSOR.tailIndistinguishable (S :=
        𝒮)).world c false)
      (tailMid kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) : ℝ :=
  tailStepCost kem cipher macS kdfS streamS geom hvalid hmactag h16 (tailHyb kem cipher macS kdfS
      streamS geom hvalid hmactag h16 (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x ==
          Role.relay)) .relay (fun _ => false) names
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x ==
          Role.relay))
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A))
    + tailStepCost kem cipher macS kdfS streamS geom hvalid hmactag h16 (tailHyb kem cipher macS
        kdfS streamS geom hvalid hmactag h16 (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x ==
          Role.relay)) .relay (fun x => false || x == Role.relay) names
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x ==
          Role.relay))
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A))
    + (tailStepCost kem cipher macS kdfS streamS geom hvalid hmactag h16 (tailHyb kem cipher macS
        kdfS streamS geom hvalid hmactag h16 (fun x => false || x == Role.relay))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) .back (fun x => false || x == Role.relay) names
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun x => false || x == Role.relay))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back))
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A))
    + tailStepCost kem cipher macS kdfS streamS geom hvalid hmactag h16 (tailHyb kem cipher macS
        kdfS streamS geom hvalid hmactag h16 (fun x => false || x == Role.relay))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) .back (fun x => (false || x == Role.relay) || x ==
          Role.back) names
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun x => false || x == Role.relay))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back))
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A)))

set_option maxHeartbeats 4000000 in
/-- **The first half of STI↔ for KEM Sphinx.** World 0 and the world in the middle, which shows
the first layer of an onion over the rest of the forward path, are told apart with at most the
cost of the two steps of the hybrid over the role of the relay before the shown layer. -/
theorem tailFirstHalf_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.tailPair (S := 𝒮) (fun c => (Protocols.RSOR.tailIndistinguishable (S :=
        𝒮)).world c false)
      (tailMid kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) :
    ((Protocols.RSOR.tailPair (S := 𝒮) (fun c => (Protocols.RSOR.tailIndistinguishable (S :=
        𝒮)).world c false)
      (tailMid kem cipher macS kdfS streamS geom hvalid hmactag h16)).advantage names A).toReal
    ≤ tailHalfCost kem cipher macS kdfS streamS geom hvalid hmactag h16 names A := by
  have hd2 : (fun x => (false || x == Role.relay) || x == Role.back) = (fun ρ => ρ == Role.relay ||
      ρ == Role.back) :=
    funext fun x => by rw [Bool.false_or]
  have hp := fun b => (Protocols.RSOR.tailPair_play_congr (S := 𝒮)
    (fun c => (Protocols.RSOR.tailIndistinguishable (S := 𝒮)).world c false) (tailMid kem cipher
        macS kdfS streamS geom hvalid hmactag h16)
    (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun _ => false)) (tailHyb kem
        cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x == Role.relay) || x
        == Role.back))
    (fun c => tailWorld_evalDistEq_tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 c)
    (fun c => by
      rw [hd2, tailHyb_all kem cipher macS kdfS streamS geom hvalid hmactag h16 c]) names A
          b).prEvent_eq (fun x => x = true)
  have h1 := Protocols.RSOR.tailPair_advantage_le (S := 𝒮) (tailHyb kem cipher macS kdfS streamS
      geom hvalid hmactag h16 (fun _ => false))
    (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x ==
        Role.relay)) (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false
        || x == Role.relay) || x == Role.back)) names
    (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
        (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A)
  have s1 := tailStep_le kem cipher macS kdfS streamS geom hvalid hmactag h16 (tailHyb kem cipher
      macS kdfS streamS geom hvalid hmactag h16 (fun _ => false))
    (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x ==
        Role.relay)) .relay (fun _ => false) (fun _ => rfl) (fun _ => rfl) names
    (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
        (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x ==
          Role.relay))
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A))
  have s2 := tailStep_le kem cipher macS kdfS streamS geom hvalid hmactag h16 (tailHyb kem cipher
      macS kdfS streamS geom hvalid hmactag h16 (fun x => false || x == Role.relay))
    (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
        Role.relay) || x == Role.back)) .back (fun x => false || x == Role.relay) (fun _ => rfl)
        (fun _ => rfl) names
    (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
        (fun x => false || x == Role.relay))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back))
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A))
  rw [Protocols.RSOR.Property.advantage_toReal names A, hp true, hp false,
    ← Protocols.RSOR.Property.advantage_toReal names
      (Protocols.RSOR.tailPair.cast (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun _ => false))
      (tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun x => (false || x ==
          Role.relay) || x == Role.back)) A)]
  unfold tailHalfCost
  exact h1.trans (by rw [add_comm]; exact add_le_add s1 s2)

/-! ## The second half: the honest relay on the backward path -/

omit [SampleableType kem.Plaintext] in
/-- The request of the middle world: the adversary's, over the rest of the forward path. -/
def midReq {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    (q : RSOR.Request kem geom) × Fin q.back.hops.length :=
  ⟨{ c.req with fwd := c.req.fwd.drop c.pos, fwd_ne := c.req.fwd.drop_ne c.pos.isLt }, c.back⟩

omit [SampleableType kem.Plaintext] in
/-- The request of world 1: over the rest of the forward path, and the backward path up to
its honest relay. -/
def cutReq {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    (q : RSOR.Request kem geom) × Fin q.back.hops.length :=
  ⟨{ c.req with fwd := c.req.fwd.drop c.pos, back := c.req.back.take (c.back + 1),
                fwd_ne := c.req.fwd.drop_ne c.pos.isLt },
    ⟨c.back, lt_of_lt_of_eq (lt_min (Nat.lt_succ_self _) c.back.isLt)
      List.length_take.symm⟩⟩

omit [SampleableType kem.Plaintext] in
/-- The first layer of a request's onion, with the honest backward relay answering nothing to
the reply's layer at its position. -/
def backWorldOf (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.tailWorld (S := 𝒮) (Q c).1 r (Q c).1.first (Q c).2

omit [SampleableType kem.Plaintext] in
/-- That world with its draw. -/
def backWorld (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    ProbComp (Protocols.RSOR.World 𝒮) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  return backWorldOf kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r

omit [SampleableType kem.Plaintext] in
/-- World 1 of STI↔ is that world for the cut request. -/
theorem tailWorld_true {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    (Protocols.RSOR.tailIndistinguishable (S := 𝒮)).world c true
      = backWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 (cutReq kem cipher macS kdfS
          streamS geom hvalid hmactag h16) c := by
  unfold Protocols.RSOR.tailIndistinguishable backWorld backWorldOf
  simp only [ite_true]
  rfl

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- The world in the middle is that world for the request over the rest of the forward path,
after renaming the forward draw. -/
theorem tailMid_evalDistEq {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) :
    tailMid kem cipher macS kdfS streamS geom hvalid hmactag h16 c =ᵈ backWorld kem cipher macS
        kdfS streamS geom hvalid hmactag h16 (midReq kem cipher macS kdfS streamS geom hvalid
        hmactag h16) c := by
  have hid : Function.Bijective (Function.uncurry fun (a : RSOR.Draw geom)
      (b : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16) =>
      ((a, b) : RSOR.Randomness geom)) := Function.bijective_id
  have hpt : ∀ (a d : RSOR.Draw geom) (b : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16),
      tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c (a, b) d = backWorldOf
          kem cipher macS kdfS streamS geom hvalid hmactag h16 (midReq kem cipher macS kdfS streamS
          geom hvalid hmactag h16) c (d, b) :=
    fun _ _ _ => rfl
  unfold tailMid backWorld
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hid fun r =>
    $ᵗ (RSOR.Draw geom) >>= fun d =>
      (pure (tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d) : ProbComp
          _)).symm ?_
  simp only [hpt]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_pair_of_bijective hid fun r =>
    (pure (backWorldOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (midReq kem cipher macS
        kdfS streamS geom hvalid hmactag h16) c r) : ProbComp _)

omit [SampleableType kem.Plaintext] in
/-- **The world of a request around the honest backward relay's ciphertext and keys.** They
enter through the header of the reply's first layer, which the payload carries, and through
the header that the relay answers nothing to. -/
def backViewK (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (ct : kem.Ciphertext) (t : KeyTuple) :
    Protocols.RSOR.World 𝒮 where
  onion := backOnionF kem cipher macS kdfS streamS geom (Q c).1 r (Nat.zero_lt_of_lt (Q c).2.isLt)
      (Q c).2
    (ofVector (kem.encodeCiphertext ct)) (ksOf streamS geom t) (tagOf macS t)
  patch :=
    { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
        if h = .back ∧ o.1 = backHeaderF kem macS kdfS streamS geom (Q c).1 r (Q c).2
            (ofVector (kem.encodeCiphertext ct)) (ksOf streamS geom t) (tagOf macS t) (Q c).2
        then pure none
        else pure out }

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- **The keyed world with the real keys is the world.** With the ciphertext and keys that the
seed `s` gives at the honest relay's backward position, `backViewK` is the world from the
randomness with `s` at that position. -/
theorem backViewK_real (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (s : Vector UInt8 32) (ct : kem.Ciphertext) (ss x0 pkt : ByteArray)
    (henc : kemEncap kem ((RSOR.path kem (Q c).1.back [.surbReply r.2.2.2])[(Q
        c).2.val]!).publicKey s
      = .ok (ofVector (kem.encodeCiphertext ct), ss))
    (hx0 : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (Q c).1.back [.surbReply
        r.2.2.2])
      (setSeedBack geom r (Q c).2 s).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
          ByteArray) 0 = .ok x0)
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (Q c).1.back [.surbReply
        r.2.2.2])
      (setSeedBack geom r (Q c).2 s).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
          ByteArray) (Q c).2 = .ok pkt) :
    backViewK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r ct (keyTuple
        (deriveHopKeys kdfS ss))
      = backWorldOf kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c (setSeedBack geom r (Q
          c).2 s) := by
  have honion := backOnionF_real kem cipher macS kdfS streamS geom hvalid hmactag (Q c).1 r
    (Nat.zero_lt_of_lt (Q c).2.isLt) (Q c).2 (Q c).2.isLt s _ ss x0 henc hx0
  have hhdr := formBack_fst_realF kem cipher macS kdfS streamS geom hvalid hmactag (Q c).1 r (Q
      c).1.msg (Q c).2
    (Q c).2.isLt (Q c).2 (le_refl _) s _ ss pkt henc hpkt
  unfold backViewK backWorldOf Protocols.RSOR.tailWorld
  exact congrArg₂ (fun on (hd : Vector UInt8 geom.headerLength) =>
    ({ onion := on
       patch := { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
        if h = .back ∧ o.1 = hd then pure none else pure out } } : Protocols.RSOR.World 𝒮))
    honion hhdr.symm

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- **A world of that shape as its draws**, with the seed of the honest backward relay's layer
drawn on its own, and then the adversary's guess against the honest relays. -/
theorem back_play_evalDistEq (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} →
    Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮))
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length) (b : Bool)
    (hw : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      (Protocols.RSOR.tailPair w₀ w₁).world c b = backWorld kem cipher macS kdfS streamS geom
          hvalid hmactag h16 Q c)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    Protocols.RSOR.Property.play names A b
      =ᵈ propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair
          w₀ w₁) .back names _ ($ᵗ (RSOR.Randomness geom)) A >>= fun d =>
        (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .back names d.k.1 d.keys)
            (fun h => if h = .back then d.k.2 else (d.keys h).2)
            (backWorldOf kem cipher macS kdfS streamS geom hvalid hmactag h16 Q d.c (setSeedBack
                geom d.o (Q d.c).2 d.s)).patch)
          (A.guess d.st
            (backWorldOf kem cipher macS kdfS streamS geom hvalid hmactag h16 Q d.c (setSeedBack
                geom d.o (Q d.c).2 d.s)).onion)).run'
              d.log := by
  refine (play_evalDistEq_honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.tailPair w₀ w₁) .back names A b).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  refine (hcong _ _ _ (hw out.1.1)).trans ?_
  unfold backWorld
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.symm ?_
  exact evalDistEq_setSeedBack geom (Q out.1.1).2
    (lt_of_lt_of_le (Q out.1.1).2.isLt (Q out.1.1).1.back.length_le) fun r =>
      (simulateQ (Protocols.RSOR.honest
          (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .back names k.1 (keysOf kem
              .back k₁ k₂))
          (fun h => if h = .back then k.2 else (keysOf kem .back k₁ k₂ h).2)
          (backWorldOf kem cipher macS kdfS streamS geom hvalid hmactag h16 Q out.1.1 r).patch)
        (A.guess out.1.2 (backWorldOf kem cipher macS kdfS streamS geom hvalid hmactag h16 Q
            out.1.1 r).onion)).run' out.2

omit [SampleableType kem.Plaintext] in
/-- The draws on which a world of that shape is not the keyed game with the real keys: the
relay's key pair is not a key pair, its seed may make the KEM fail, or the reply's layers that
carry its ciphertext cannot be built. -/
def backBadK {w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)} {names : Role → RSOR.Name}
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {A : (Protocols.RSOR.tailPair w₀ w₁).Adversary}
    (d : PropDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀
        w₁) .back names (RSOR.Randomness geom) A) : Prop :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s)
    ∧ (∃ x0, RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (Q d.c).1.back [.surbReply
        d.o.2.2.2])
        (setSeedBack geom d.o (Q d.c).2 d.s).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
            ByteArray) 0 = .ok x0)
    ∧ ∃ pkt, RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (Q d.c).1.back [.surbReply
        d.o.2.2.2])
        (setSeedBack geom d.o (Q d.c).2 d.s).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
            ByteArray) (Q d.c).2 = .ok pkt)

set_option maxHeartbeats 2000000 in
/-- **A world of that shape is the keyed game with the real keys, off the bad draws.** -/
theorem back_sub_keyedReal_le (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} →
    Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮))
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    (hQ : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      (Q c).1.back.hops[(Q c).2] = hon .back) (b : Bool)
    (hw : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      (Protocols.RSOR.tailPair w₀ w₁).world c b = backWorld kem cipher macS kdfS streamS geom
          hvalid hmactag h16 Q c)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A b}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair
              w₀ w₁) .back names _ ($ᵗ (RSOR.Randomness geom))
            (fun ch o ct t => backViewK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q ch.c
                o ct t) A))}[x = true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.tailPair w₀ w₁) .back names _ ($ᵗ (RSOR.Randomness geom))
        A)}[backBadK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q d]).toReal := by
  rw [(back_play_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q b hw names
      A).prEvent_eq (fun x => x = true),
    (keyedReal_propAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.tailPair w₀ w₁) .back names _ _ _ A).prEvent_eq
      (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _ (backBadK kem cipher macS kdfS streamS geom hvalid
      hmactag h16 Q) (fun d hd => ?_)
    (fun x => x = true)
  obtain ⟨hpk, hrel, ⟨x0, hx0⟩, ⟨pkt, hpkt⟩⟩ := Classical.not_not.mp hd
  have hk : (Q d.c).2.val < (Q d.c).1.back.hops.length := (Q d.c).2.isLt
  have hle : (Q d.c).1.back.hops.length ≤ geom.nrHops := (Q d.c).1.back.length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom (Q d.c).1.back _ _ _
      x0 hx0 (Q d.c).2 hk
  have hkey : ((Q d.c).1.back.hops[(Q d.c).2]).key = d.k.1 := by
    rw [hQ d.c]
    rfl
  have hpub : ((RSOR.path kem (Q d.c).1.back [.surbReply d.o.2.2.2])[(Q d.c).2.val]!).publicKey
      = ofVector (kem.encodePublicKey d.k.1.1) := by
    rw [RSOR.path_getElem! kem _ _ _ hk]
    exact congrArg (fun key : Key kem => ofVector (kem.encodePublicKey key.1)) hkey
  have hs : (setSeedBack geom d.o (Q d.c).2 d.s).2.1.1.toArray[(Q d.c).2.val]! = d.s := by
    simp [setSeedBack, lt_of_lt_of_le hk hle]
  rw [hs] at henc
  have henc' : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) d.s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc'
  have hdec : decapOf kem d.k.2 (encapOf kem d.k.1.1 d.s).1
      = some (encapOf kem d.k.1.1 d.s).2 := by
    have h := decapOf_encapOf kem d.k.2 d.s hrel _ _ (hpk ▸ henc')
    rwa [← hpk] at h
  have hview := backViewK_real kem cipher macS kdfS streamS geom hvalid hmactag h16 Q d.c d.o d.s _
      _ x0 pkt (by rw [hpub]; exact henc')
    hx0 hpkt
  rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀
      w₁) .back names _ _ _ A d.k d.keys _ _ hdec d.st d.log _,
    ← hview]
  rfl

/-! ### The MAC step at the honest backward relay -/

omit [SampleableType kem.Plaintext] in
/-- The bytes of the reply's layer at the honest backward relay which its MAC covers, from its
keys other than its MAC key. -/
def backMK (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (ct : kem.Ciphertext) (rest : RestKeys) : ByteArray :=
  relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem (Q c).1.back [.surbReply r.2.2.2])
      r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) (Q c).2
    (ofVector (kem.encodeCiphertext ct)) (ksOf streamS geom (withMAC rest default))

omit [SampleableType kem.Plaintext] in
/-- The reply's layer at the honest backward relay, from the tag of those bytes. -/
def backLayerT (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (ct : kem.Ciphertext) (rest : RestKeys) (tag : Vector UInt8
        macS.tagSize) : ByteArray :=
  backMK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r ct rest ++ ofVector tag
    ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem (Q c).1.back [.surbReply
        r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) (Q c).2
      (ksOf streamS geom (withMAC rest default)) (encOf default (withMAC rest default))

omit [SampleableType kem.Plaintext] in
/-- The world of a request, from the tag of those bytes. -/
def backViewT (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (ct : kem.Ciphertext) (rest : RestKeys) (tag : Vector UInt8
        macS.tagSize) :
    Protocols.RSOR.World 𝒮 where
  onion := backOnionX kem cipher macS kdfS streamS geom (Q c).1 r (Nat.zero_lt_of_lt (Q c).2.isLt)
    (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem (Q c).1.back [.surbReply
        r.2.2.2]) r.2.1 0 (Q c).2
      (backLayerT kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r ct rest tag)))
  patch :=
    { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
        if h = .back ∧ o.1 = (RSOR.split geom (backLayerT kem cipher macS kdfS streamS geom hvalid
            hmactag h16 Q c r ct rest tag)).1
        then pure none
        else pure out }

omit [SampleableType kem.Plaintext] in
/-- The draws on which the reply's layers are as the closed form says: the honest relay's
public key is the one its private key gives, its seed does not make the KEM fail, the reply's
first layer can be built, and the seeds in front of the relay do not make the KEM fail. -/
def backGoodAtK (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) (pk : Key kem)
    (sk : kem.PrivateKey) (r : RSOR.Randomness geom) (s : Vector UInt8 32) : Prop :=
  pk.1 = kem.derivePublicKey sk ∧ kem.Reliable (kem.stateFromSeed s)
    ∧ (∃ x0, RSOR.layer kem default macS kdfS streamS geom (RSOR.path kem (Q c).1.back [.surbReply
        r.2.2.2])
        (setSeedBack geom r (Q c).2 s).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
            ByteArray) 0 = .ok x0)
    ∧ ∀ m, m < (Q c).2.val → kem.Reliable (kem.stateFromSeed r.2.1.1.toArray[m]!)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- On such a draw, the keyed world uses the honest relay's MAC key for one tag, on bytes of
the length of a header without its tag. -/
theorem backViewK_tag (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) (pk : Key kem)
    (hkey : ((Q c).1.back.hops[(Q c).2]).key = pk)
    (sk : kem.PrivateKey) (r : RSOR.Randomness geom) (s : Vector UInt8 32)
    (hg : backGoodAtK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c pk sk r s) (u :
        KeyTuple) :
    backViewK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r (encapOf kem pk.1 s).1 u
        = backViewT kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r (encapOf kem pk.1
            s).1 (restOf u)
          (macS.mac (ofVector u.2.2.1)
            (backMK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r (encapOf kem pk.1
                s).1 (restOf u)))
      ∧ (backMK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q c r (encapOf kem pk.1 s).1
          (restOf u)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨hpk, hrel, ⟨x0, hx0⟩, hfront⟩ := hg
  have hk : (Q c).2.val < (Q c).1.back.hops.length := (Q c).2.isLt
  have hle : (Q c).1.back.hops.length ≤ geom.nrHops := (Q c).1.back.length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem default macS kdfS streamS geom (Q c).1.back _ _ _
      x0 hx0 (Q c).2 hk
  have hs : (setSeedBack geom r (Q c).2 s).2.1.1.toArray[(Q c).2.val]! = s := by
    simp [setSeedBack, lt_of_lt_of_le hk hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem pk.1 s ct ss henc
  obtain ⟨hz, hsize, hzk⟩ := routeK_parts kem default macS kdfS streamS geom hvalid hmactag h16 (Q
      c).1.back
    [.surbReply r.2.2.2]
    (fun x hx => by
      rw [List.mem_singleton.1 hx]
      exact ⟨by simp, by simp⟩)
    r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) (Q c).2 hk pk sk hkey hpk s
        hrel _ _ x0 henc hx0 hfront u
  refine ⟨?_, hsize⟩
  unfold backViewK backViewT backLayerT backMK backOnionF backHeaderF headerF
  simp only [layerF_id]
  rw [hz, hzk]
  rfl

omit [SampleableType kem.Plaintext] in
/-- The bytes the honest backward relay's MAC covers, in the keyed game. -/
def backM (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮))
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length) (names : Role → RSOR.Name) {pk : Key
          kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀
        w₁) .back names pk)
    (o : RSOR.Randomness geom) (ct : kem.Ciphertext) (rest : RestKeys) : ByteArray :=
  backMK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q ch.c o ct rest

omit [SampleableType kem.Plaintext] in
/-- The keyed game's world from the tag of those bytes. -/
def backVT (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮))
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length) (names : Role → RSOR.Name) {pk : Key
          kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀
        w₁) .back names pk)
    (o : RSOR.Randomness geom) (ct : kem.Ciphertext) (rest : RestKeys)
    (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  backViewT kem cipher macS kdfS streamS geom hvalid hmactag h16 Q ch.c o ct rest tag

/-- The keyed game of a world of that shape around the honest backward relay's ciphertext. -/
abbrev backSetupK (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮))
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length) (names : Role → RSOR.Name) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool :=
  propSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀ w₁)
      .back names _ ($ᵗ (RSOR.Randomness geom))
    (fun ch o ct t => backViewK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q ch.c o ct t)

/-- The adversary of that keyed game. -/
abbrev backAdvK (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮))
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length) (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    KeyedAdversary (backSetupK kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names)
        :=
  propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.tailPair w₀ w₁)
      .back names _ _ _ A

/-- The good draws of that keyed game. -/
def backGoodK {w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮)}
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length) {names : Role → RSOR.Name}
    {A : (Protocols.RSOR.tailPair w₀ w₁).Adversary}
    (d : KeyedDraw (backAdvK kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names A))
        : Prop :=
  backGoodAtK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q (propChOf d).c d.k.1 d.k.2
      (propOthOf d) d.s

set_option maxHeartbeats 2000000 in
/-- **The MAC step at the honest backward relay.** With uniform keys at the relay, it may
answer the challenge ciphertext under the reply layer's own header only, at the cost of a
forgery against the MAC and of the draws that are not good. -/
theorem back_keyedIdeal_sub_tagged_le (w₀ w₁ : {hon : Protocols.RSOR.Honest 𝒮} →
    Protocols.RSOR.TailChallenge hon
      → ProbComp (Protocols.RSOR.World 𝒮))
    (Q : {hon : Protocols.RSOR.Honest 𝒮} → Protocols.RSOR.TailChallenge hon
      → (q : RSOR.Request kem geom) × Fin q.back.hops.length)
    (hQ : ∀ {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon),
      (Q c).1.back.hops[(Q c).2] = hon .back)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.tailPair w₀ w₁).Adversary) :
    |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom (backAdvK kem cipher macS kdfS streamS
        geom hvalid hmactag h16 w₀ w₁ Q names A))}[x = true]).toReal
      - (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdvK kem cipher macS kdfS
          streamS geom hvalid hmactag h16 w₀ w₁ Q names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (backM kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names))))}[x =
                true]).toReal|
    ≤ (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom (backAdvK
        kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names A)
          (backM kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names)
          (backVT kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names)))}[x =
              true]).toReal
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (backAdvK kem cipher macS kdfS streamS
          geom hvalid hmactag h16 w₀ w₁ Q names A))}[¬ backGoodK kem cipher macS kdfS streamS geom
          hvalid hmactag h16 Q d]).toReal := by
  have hkey : ∀ d : KeyedDraw (backAdvK kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁
      Q names A),
      ((Q (propChOf d).c).1.back.hops[(Q (propChOf d).c).2]).key = d.k.1 := fun d => by
    rw [hQ (propChOf d).c]
    rfl
  exact keyedIdeal_sub_tagged_le cipher macS kdfS streamS geom (backAdvK kem cipher macS kdfS
      streamS geom hvalid hmactag h16 w₀ w₁ Q names A) hmactag
    (backM kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names)
    (backVT kem cipher macS kdfS streamS geom hvalid hmactag h16 w₀ w₁ Q names)
    (backGoodK kem cipher macS kdfS streamS geom hvalid hmactag h16 Q)
    (fun d r hg => (backViewK_tag kem cipher macS kdfS streamS geom hvalid hmactag h16 Q (propChOf
        d).c d.k.1 (hkey d) d.k.2 (propOthOf d)
      d.s hg (withMAC r default)).2)
    (fun d u hg => (backViewK_tag kem cipher macS kdfS streamS geom hvalid hmactag h16 Q (propChOf
        d).c d.k.1 (hkey d) d.k.2 (propOthOf d)
      d.s hg u).1)
    (fun _ _ _ _ _ => rfl)

end TailGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
