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

end TailGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
