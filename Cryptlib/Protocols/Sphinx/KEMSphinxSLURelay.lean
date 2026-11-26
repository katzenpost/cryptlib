/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLUSender

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

/-! # SLU← for KEM Sphinx: the reply's next layer

With the honest relay's keys used up, world 0 of SLU← is compared with the world where the
relay sends on an onion built like a reply layer (`replySwap`). On the backward path the reply's
next layer is a first layer over the rest of the path. -/

section Uniform

/-- **The two parts of a uniform string are uniform.** -/
theorem evalDistEq_split {δ : Type} {a b n : ℕ} (hn : a + b = n)
    (K : ByteArray → ByteArray → ProbComp δ) :
    ($ᵗ (Vector UInt8 n) >>= fun u => K ((ofVector u).extract 0 a) ((ofVector u).extract a n))
      =ᵈ (do
        let x ← $ᵗ (Vector UInt8 a)
        let y ← $ᵗ (Vector UInt8 b)
        K (ofVector x) (ofVector y)) := by
  have e0 : ∀ (x : Vector UInt8 a) (y : Vector UInt8 b),
      (ofVector (padFiller hn (zeroBytes 0) x y)).extract 0 a = ofVector x
        ∧ (ofVector (padFiller hn (zeroBytes 0) x y)).extract a n = ofVector y := by
    intro x y
    rw [ofVector_padFiller, xorBytes_zeroBytes]
    constructor
    · have h1 := Util.Bytes.extract_append_left (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector] at h1
    · have h1 := Util.Bytes.extract_append_right (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector, hn] at h1
  have h := (evalDistEq_pair_of_bijective (padFiller_bijective hn (zeroBytes 0))
    (fun u : Vector UInt8 n => K ((ofVector u).extract 0 a) ((ofVector u).extract a n))).symm
  simpa only [(e0 _ _).1, (e0 _ _).2] using h

/-- **A region of a uniform string as the tail of a keystream.** A keystream whose head is a
uniform string under any mask, and whose tail is `t` bytes of another uniform string under a
fixed mask, is a uniform keystream. -/
theorem evalDistEq_headRegion {δ : Type} {n a t h m : ℕ} (hat : a + t ≤ n) (hm : h + t = m)
    (A : Vector UInt8 n → ByteArray → ByteArray) (B : ByteArray)
    (K : Vector UInt8 m → ProbComp δ) :
    (do
      let P ← $ᵗ (Vector UInt8 n)
      let U ← $ᵗ (Vector UInt8 m)
      K (Util.Bytes.toVecN m
        (xorBytes ((ofVector U).extract 0 h) (A P ((ofVector U).extract h m))
          ++ xorBytes ((ofVector P).extract a (a + t)) B)))
      =ᵈ ($ᵗ (Vector UInt8 m) >>= K) := by
  have hc : a + (n - a) = n := by omega
  have hr : t + (n - a - t) = n - a := by omega
  have e0 : ∀ (x : Vector UInt8 a) (r : Vector UInt8 (n - a)),
      (ofVector (padFiller hc (zeroBytes 0) x r)).extract a (a + t)
        = (ofVector r).extract 0 t := by
    intro x r
    rw [ofVector_padFiller, xorBytes_zeroBytes,
      Util.Bytes.extract_append_of_ge _ _ (by rw [Util.Bytes.size_ofVector]),
      Util.Bytes.size_ofVector, Nat.sub_self, Nat.add_sub_cancel_left]
  -- the head: a uniform string under any mask
  have head : ∀ (P : Vector UInt8 n) (C : ByteArray),
      ($ᵗ (Vector UInt8 m) >>= fun U => K (Util.Bytes.toVecN m
        (xorBytes ((ofVector U).extract 0 h) (A P ((ofVector U).extract h m)) ++ C)))
      =ᵈ ($ᵗ (Vector UInt8 h) >>= fun x => K (Util.Bytes.toVecN m (ofVector x ++ C))) :=
    fun P C => by
    refine EvalDistEq.trans (evalDistEq_split hm fun X Y =>
      K (Util.Bytes.toVecN m (xorBytes X (A P Y) ++ C))) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => ?_)
      (OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 t)) _)
    have h5 := evalDistEq_otp h (A P (ofVector y))
      (fun z => K (Util.Bytes.toVecN m (ofVector z ++ C)))
    simpa only [Util.Bytes.ofVector_toVecN _
      ((size_xorBytes _ _).trans (Util.Bytes.size_ofVector _))] using h5
  -- the region: `t` bytes of a uniform string are uniform
  have region : ∀ J : ByteArray → ProbComp δ,
      ($ᵗ (Vector UInt8 n) >>= fun P => J ((ofVector P).extract a (a + t)))
      =ᵈ ($ᵗ (Vector UInt8 t) >>= fun y => J (ofVector y)) := fun J => by
    refine EvalDistEq.trans (evalDistEq_pair_of_bijective
      (padFiller_bijective hc (zeroBytes 0))
      (fun P : Vector UInt8 n => J ((ofVector P).extract a (a + t)))).symm ?_
    simp only [e0]
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 a)) _) ?_
    refine EvalDistEq.trans (evalDistEq_split hr fun X _ => J X) ?_
    exact EvalDistEq.bind_right _ fun y =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 (n - a - t))) _
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun P => head P _) ?_
  refine EvalDistEq.trans (region fun T =>
    $ᵗ (Vector UInt8 h) >>= fun x => K (Util.Bytes.toVecN m (ofVector x ++ xorBytes T B))) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_pair_of_bijective (padFiller_bijective hm B) K

end Uniform

section Fresh

variable {S : Protocols.RSOR.Scheme} {L : ℕ} (ρ : Protocols.RSOR.Role) (H : S.Header)
  (key : S.Onion → Vector UInt8 L) (step : S.Onion → Vector UInt8 L → Option S.Step)
  (rep : S.Msg → S.Onion → Vector UInt8 L → Option (S.Name × S.Onion))

/-- A patch that first gives the relay `ρ`, under the header `H`, the answer it has when its
payload decrypts by `dec`. -/
def decPatch (dec : Vector UInt8 L → Vector UInt8 L) (patch : Protocols.RSOR.Patch S) :
    Protocols.RSOR.Patch S where
  proc h o out :=
    if h = ρ ∧ o.1 = H then patch.proc h o (step o (dec (key o))) else patch.proc h o out
  reply h m o out :=
    if h = ρ ∧ o.1 = H then patch.reply h m o (rep m o default) else patch.reply h m o out

/-- A patch that first gives the relay `ρ`, under the header `H`, the answer it has when its
payload decrypts to a block drawn then. -/
def drawPatch (patch : Protocols.RSOR.Patch S) : Protocols.RSOR.Patch S where
  proc h o out :=
    if h = ρ ∧ o.1 = H then $ᵗ (Vector UInt8 L) >>= fun g => patch.proc h o (step o g)
    else patch.proc h o out
  reply := (decPatch ρ H key step rep id patch).reply

variable (proc : Protocols.RSOR.Role → S.Onion → Option S.Step)
  (reply : Protocols.RSOR.Role → S.Msg → S.Onion → Option (S.Name × S.Onion))

/-- A relay that decrypts by `dec` under one header is a relay patched with `decPatch`, when
its patched reply under that header does not depend on the decrypted block. -/
theorem withDec_decPatch (dec : Vector UInt8 L → Vector UInt8 L)
    (patch : Protocols.RSOR.Patch S)
    (hrep : ∀ m o x, o.1 = H →
      patch.reply ρ m o (rep m o x) = patch.reply ρ m o (rep m o default)) :
    Protocols.RSOR.withDec ρ H key step rep proc reply dec patch
      = Protocols.RSOR.oracle (fun h o => pure (proc h o)) (fun h m o => pure (reply h m o))
        (decPatch ρ H key step rep dec patch) := by
  refine Protocols.RSOR.oracle_patch_congr patch _ _ _ _ _ (fun h o => ?_) (fun h m o => ?_)
  · by_cases hc : h = ρ ∧ o.1 = H
    · exact (congrArg (patch.proc h o) (ite_eq_left hc)).trans (ite_eq_left hc).symm
    · exact (congrArg (patch.proc h o) (ite_eq_right hc)).trans (ite_eq_right hc).symm
  · by_cases hc : h = ρ ∧ o.1 = H
    · have e : patch.reply h m o (rep m o (dec (key o)))
          = patch.reply h m o (rep m o default) := by
        obtain ⟨rfl, ho⟩ := hc
        exact hrep m o _ ho
      exact (congrArg (patch.reply h m o) (ite_eq_left hc)).trans (e.trans (ite_eq_left hc).symm)
    · exact (congrArg (patch.reply h m o) (ite_eq_right hc)).trans (ite_eq_right hc).symm

/-- **The ideal cipher's one answer under a header is a fresh block.** An honest relay
processes a header once. So a relay whose payload under one header decrypts as the ideal
cipher does after one encryption (to the block `w` for the block `u`, to the block `v` for any
other) is, with `u`, `w` and `v` uniform, a relay whose payload decrypts to one uniform
block. -/
theorem withDec_fresh (patch : Protocols.RSOR.Patch S)
    (hrep : ∀ m o x, o.1 = H →
      patch.reply ρ m o (rep m o x) = patch.reply ρ m o (rep m o default))
    {α : Type} (oa : OracleComp (Protocols.RSOR.oracleSpec S) α) (log : Protocols.RSOR.Log S) :
    (do
      let u ← $ᵗ (Vector UInt8 L)
      let w ← $ᵗ (Vector UInt8 L)
      let v ← $ᵗ (Vector UInt8 L)
      (simulateQ (Protocols.RSOR.withDec ρ H key step rep proc reply
        (fun y => if y = u then w else v) patch) oa).run log)
      =ᵈ ($ᵗ (Vector UInt8 L) >>= fun g =>
        (simulateQ (Protocols.RSOR.withDec ρ H key step rep proc reply (fun _ => g) patch)
          oa).run log) := by
  simp only [withDec_decPatch ρ H key step rep proc reply _ patch hrep]
  have h1 := Protocols.RSOR.oracle_draw ρ H
    (do
      let u ← $ᵗ (Vector UInt8 L)
      let w ← $ᵗ (Vector UInt8 L)
      let v ← $ᵗ (Vector UInt8 L)
      pure (u, w, v))
    (drawPatch ρ H key step rep patch)
    (fun x : Vector UInt8 L × Vector UInt8 L × Vector UInt8 L =>
      decPatch ρ H key step rep (fun y => if y = x.1 then x.2.1 else x.2.2) patch)
    (fun h o => pure (proc h o)) (fun h m o => pure (reply h m o))
    (fun h o out => by
      by_cases hc : h = ρ ∧ o.1 = H
      · have e : (drawPatch ρ H key step rep patch).proc h o out
            = $ᵗ (Vector UInt8 L) >>= fun g => patch.proc h o (step o g) := ite_eq_left hc
        have e2 : ∀ x : Vector UInt8 L × Vector UInt8 L × Vector UInt8 L,
            (decPatch ρ H key step rep (fun y => if y = x.1 then x.2.1 else x.2.2)
              patch).proc h o out
              = patch.proc h o (step o (if key o = x.1 then x.2.1 else x.2.2)) :=
          fun x => ite_eq_left hc
        rw [e]
        simp only [e2, bind_assoc, pure_bind]
        exact (evalDistEq_ite_fresh (key o) fun g => patch.proc h o (step o g)).symm
      · have e : (drawPatch ρ H key step rep patch).proc h o out = patch.proc h o out :=
          ite_eq_right hc
        have e2 : ∀ x : Vector UInt8 L × Vector UInt8 L × Vector UInt8 L,
            (decPatch ρ H key step rep (fun y => if y = x.1 then x.2.1 else x.2.2)
              patch).proc h o out = patch.proc h o out := fun x => ite_eq_right hc
        rw [e]
        simp only [e2]
        exact (OracleComp.EvalDistEq.bind_const _ _).symm)
    (fun g g' h o out hc => (ite_eq_right hc).trans (ite_eq_right hc).symm) (fun g => rfl) oa log
  have h2 := Protocols.RSOR.oracle_draw ρ H ($ᵗ (Vector UInt8 L))
    (drawPatch ρ H key step rep patch)
    (fun g : Vector UInt8 L => decPatch ρ H key step rep (fun _ => g) patch)
    (fun h o => pure (proc h o)) (fun h m o => pure (reply h m o))
    (fun h o out => by
      by_cases hc : h = ρ ∧ o.1 = H
      · have e : (drawPatch ρ H key step rep patch).proc h o out
            = $ᵗ (Vector UInt8 L) >>= fun g => patch.proc h o (step o g) := ite_eq_left hc
        have e2 : ∀ g : Vector UInt8 L,
            (decPatch ρ H key step rep (fun _ => g) patch).proc h o out
              = patch.proc h o (step o g) := fun g => ite_eq_left hc
        rw [e]
        simp only [e2]
        exact EvalDistEq.rfl
      · have e : (drawPatch ρ H key step rep patch).proc h o out = patch.proc h o out :=
          ite_eq_right hc
        have e2 : ∀ g : Vector UInt8 L,
            (decPatch ρ H key step rep (fun _ => g) patch).proc h o out
              = patch.proc h o out := fun g => ite_eq_right hc
        rw [e]
        simp only [e2]
        exact (OracleComp.EvalDistEq.bind_const _ _).symm)
    (fun g g' h o out hc => (ite_eq_right hc).trans (ite_eq_right hc).symm) (fun g => rfl) oa log
  simp only [bind_assoc, pure_bind] at h1
  exact h1.symm.trans h2

end Fresh

section RestOfPath

variable (kem : KEM) (geom : Geometry)

/-- The hops of a route from position `j` on are the hops of the rest of the route. -/
theorem path_extract_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (j : ℕ) (hj : j ≤ R.hops.length) :
    (RSOR.path kem R last).extract j (RSOR.path kem R last).size
      = RSOR.path kem (R.drop j) last := by
  apply Array.ext
  · simp [RSOR.path_size, Protocols.RSOR.Route.drop]
  · intro i h1 h2
    have hi : j + i < R.hops.length := by
      simp [RSOR.path_size] at h1
      omega
    simp only [RSOR.path, Protocols.RSOR.Route.drop, Array.getElem_extract,
      List.getElem_toArray, List.getElem_mapIdx, List.getElem_drop, List.length_drop]
    congr 1
    have e : (j + i + 1 = R.hops.length) = (i + 1 = R.hops.length - j) := by
      apply propext
      omega
    simp only [e]

variable (kdfS : KDF) (streamS : StreamCipher)

/-- **Past the keyed hop the fillers are those of the rest of the path.** If the keyed filler
of the layer after the keyed hop is the filler `filler'`, then the keyed fillers of the layers
from there on are the fillers built on the rest of the path from `filler'`. -/
theorem fillerAtF_drop (hops : Array PathHop) (seeds : Array (Vector UInt8 32))
    (filler filler' : ByteArray) (j : ℕ) (U : ByteArray) (hsz : seeds.size = hops.size)
    (h0 : fillerAtF kem kdfS streamS geom hops seeds filler j U (j + 1) = filler') (i : ℕ)
    (hi : j + 1 + i ≤ hops.size) :
    fillerAtF kem kdfS streamS geom hops seeds filler j U (j + 1 + i)
      = RSOR.fillerAt kem kdfS streamS geom (hops.extract (j + 1) hops.size)
        (seeds.extract (j + 1) seeds.size) filler' i := by
  induction i with
  | zero => exact h0
  | succ i ih =>
    show fillerAtF kem kdfS streamS geom hops seeds filler j U (j + 1 + i + 1) = _
    simp only [fillerAtF, RSOR.fillerAt]
    rw [ih (by omega)]
    unfold tailFillerOf tailFiller
    rw [show ((hops.extract (j + 1) hops.size).extract i (hops.extract (j + 1) hops.size).size).size
      = hops.size - (j + 1 + i) by simp; omega]
    congr 1
    rw [← tailPadOf_kemHopKeys kem kdfS streamS geom]
    apply tailPadOf_congr
    intro m hm
    have hlt : j + 1 + i + m < hops.size := by omega
    have hne : ¬ j + 1 + i + m = j := by omega
    show (if j + 1 + i + m = j then _ else _) = _
    rw [ite_eq_right hne]
    congr 1
    unfold kemHopKeys
    rw [getElem!_extract_from _ i m (by simp; omega),
      getElem!_extract_from _ (j + 1) (i + m) (by omega),
      getElem!_extract_from _ i m (by simp; omega),
      getElem!_extract_from _ (j + 1) (i + m) (by omega),
      show j + 1 + (i + m) = j + 1 + i + m by omega]

/-- **The tail of the keyed hop's keystream sets the next layer's filler.** The keyed filler
of the layer after the keyed hop is the sender's filler and then any `j + 1` blocks `T`, for
the keystream whose tail is `T` under the filler at a zero keystream. The head of the keystream
is not read. -/
theorem fillerAtF_target (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength *
    geom.nrHops)
    (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (j : ℕ)
    (H T : ByteArray) (hH : H.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j +
        1) * geom.perHopRoutingInfoLength) (hT : T.size = (j + 1) * geom.perHopRoutingInfoLength)
    (hlen : hops.size ≤ geom.nrHops) (hj : j + 1 < hops.size)
    (hf : filler.size = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) :
    fillerAtF kem kdfS streamS geom hops seeds filler j
        (H ++ xorBytes T ((fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).extract filler.size
            (filler.size + (j + 1) * geom.perHopRoutingInfoLength))) (j + 1)
      = filler ++ T := by
  have hm : (j + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := by
    have h1 : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.nrHops * geom.perHopRoutingInfoLength
        := Nat.mul_le_mul_right _ (by omega)
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    omega
  have hZsz : (fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).size = filler.size + (j +
      1) * geom.perHopRoutingInfoLength := by
    rw [fillerAtF_size kem kdfS streamS geom hrouting hops seeds filler j _ hlen hf
      (zeroBytes_size _) (j + 1) hj, hf, Nat.add_mul]
  have hZ : (fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes (geom.routingInfoLength
      + geom.perHopRoutingInfoLength)) (j + 1)) = filler ++ (fillerAtF kem kdfS streamS geom hops
      seeds filler j (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j +
      1)).extract filler.size (filler.size + (j + 1) * geom.perHopRoutingInfoLength) := by
    have h := Util.Bytes.append_extract (fillerAtF kem kdfS streamS geom hops seeds filler j
        (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)) filler.size
        (by rw [hZsz]; omega)
    rw [fillerAtF_head geom kem kdfS streamS hrouting hops seeds filler j _ (zeroBytes_size _)
      hlen hf (j + 1) (by omega), hZsz] at h
    exact h.symm
  obtain ⟨Zt, hZt⟩ : ∃ Zt, Zt
      = (fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)) (j + 1)).extract filler.size (filler.size + (j + 1) *
          geom.perHopRoutingInfoLength) := ⟨_, rfl⟩
  have hZts : Zt.size = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [hZt, ByteArray.size_extract, hZsz]
    omega
  rw [← hZt] at hZ ⊢
  have hV : (H ++ xorBytes T Zt).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
      by
    rw [ByteArray.size_append, size_xorBytes, hH, hT]
    omega
  rw [fillerAtF_affine geom kem kdfS streamS hrouting hops seeds filler j _ hV hlen (by omega)
      hf (j + 1) le_rfl, Nat.sub_self, Nat.zero_mul, Nat.sub_zero,
    Util.Bytes.extract_append_of_ge _ _ (by rw [hH]), hH, Nat.sub_self,
    show (geom.routingInfoLength + geom.perHopRoutingInfoLength) - ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) = (j + 1) *
        geom.perHopRoutingInfoLength by omega,
    extract_all _ _ (by rw [size_xorBytes, hT]), hZ,
    xorBytes_append filler Zt _ _ (by rw [zeroBytes_size, hf]),
    xorBytes_zeroBytes, xorBytes_comm_of_size_eq Zt (xorBytes T Zt)
      (by rw [size_xorBytes, hZts, hT]), xorBytes_xorBytes]

omit kem geom kdfS streamS in
/-- Taking a tail of a tail of an array is taking one tail. -/
theorem extract_tail_tail {α : Type} (a : Array α) (j i : ℕ) :
    a.extract (j + i) a.size = (a.extract j a.size).extract i (a.extract j a.size).size := by
  apply Array.ext
  · simp
    omega
  · intro k h1 h2
    simp [Nat.add_assoc]

variable (cipher : WideBlockCipher) (macS : MAC)

/-- **A layer past the keyed hop is a layer over the rest of the path**, when the seeds after
the keyed hop are the rest's seeds and the keyed filler of the layer after the keyed hop is the
rest's padding. -/
theorem layerPast_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (d d' : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (U : ByteArray)
    (hseeds : (d.1.toArray.extract 0 (RSOR.path kem R last).size).extract (j + 1)
        (d.1.toArray.extract 0 (RSOR.path kem R last).size).size
      = d'.1.toArray.extract 0 (RSOR.path kem (R.drop (j + 1)) last).size)
    (hfill : fillerAtF kem kdfS streamS geom (RSOR.path kem R last) (d.1.toArray.extract 0
        (RSOR.path kem R last).size)
        ((ofVector d.2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength))
        j U (j + 1)
      = (ofVector d'.2).extract 0
        ((geom.nrHops - (RSOR.path kem (R.drop (j + 1)) last).size) * geom.perHopRoutingInfoLength))
    (i : ℕ) (hi : j + 1 + i ≤ R.hops.length) :
    layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload j U (j + 1 + i)
      = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) d'
          payload i := by
  have hle := R.length_le
  have hsz : (d.1.toArray.extract 0 (RSOR.path kem R last).size).size = (RSOR.path kem R last).size
      := by
    rw [RSOR.path_size]
    simp
    omega
  unfold layerPast RSOR.layer
  dsimp only
  rw [fillerAtF_drop kem geom kdfS streamS _ _ _ _ j U hsz hfill i
      (by rw [RSOR.path_size]; exact hi),
    extract_tail_tail (d.1.toArray.extract 0 (RSOR.path kem R last).size) (j + 1) i,
    extract_tail_tail (RSOR.path kem R last) (j + 1) i, hseeds,
    path_extract_drop kem geom R last (j + 1) (by omega)]

set_option maxHeartbeats 2000000 in
/-- **A middle hop's header under a shifted keystream.** Two paths of one length, each with a
draw, give the keyed hop two headers. With the head of the keystream shifted by the difference
of the two routing informations, the first gives the second's header bytes, and still its own
next layer. -/
theorem relayFront_headShift (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops hops' : Array PathHop) (d d' : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U U' fwd fwd' : ByteArray) (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hsz : hops'.size = hops.size)
    (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hU' : U'.size =
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hc : c.size = kem.ciphertextSize)
    (hcmd : (hops[j]!).commands = []) (hcmd' : (hops'[j]!).commands = [])
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd)
    (hfwd' : layerPast kem cipher macS kdfS streamS geom hops' d' payload j U' (j + 1) = .ok fwd')
    (htail : (midPad geom kem kdfS streamS hops d j).extract ((geom.nrHops - hops.size) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) +
        j * geom.perHopRoutingInfoLength)
      = (midPad geom kem kdfS streamS hops' d' j).extract ((geom.nrHops - hops'.size) *
          geom.perHopRoutingInfoLength) (((geom.nrHops - hops'.size) *
          geom.perHopRoutingInfoLength) + j * geom.perHopRoutingInfoLength)) :
    (xorBytes (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)))
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size = (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)
    ∧ layerPast kem cipher macS kdfS streamS geom hops d payload j
      (xorBytes (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)))
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1) = .ok fwd
    ∧ relayFront kem cipher macS kdfS streamS geom hops d payload j c
      (xorBytes (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)))
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))
      = relayFront kem cipher macS kdfS streamS geom hops' d' payload j c U' := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hj' : j + 1 < hops'.size := lt_of_lt_of_eq hj hsz.symm
  have hlen' : hops'.size ≤ geom.nrHops := le_of_eq_of_le hsz hlen
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at hjp
  have hUh : (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)).size =
      (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_extract, hU']
    omega
  obtain ⟨X0, hX0⟩ : ∃ X0, X0 = (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)) := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X1, X1 = (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength)) := ⟨_, rfl⟩
  rw [← hX0, ← hX1]
  obtain ⟨V, hV⟩ : ∃ V, V = xorBytes (U'.extract 0 (geom.routingInfoLength - j *
      geom.perHopRoutingInfoLength)) (xorBytes X1 X0)
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength) := ⟨_, rfl⟩
  rw [← hV]
  have hVs : V.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := by
    rw [hV, ByteArray.size_append, size_xorBytes, hUh, ByteArray.size_extract, hU]
    omega
  have hVt : U.extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      = V.extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
          geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
          by
    rw [show (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength = (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
        by rw [Nat.succ_mul]; omega, hV,
      Util.Bytes.extract_append_of_ge _ _ (by rw [size_xorBytes, hUh]), size_xorBytes, hUh,
      Nat.sub_self, show (geom.routingInfoLength + geom.perHopRoutingInfoLength) -
          (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) = (U.extract
          (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)).size by
        rw [ByteArray.size_extract, hU]; omega]
    exact (extract_all _ _ rfl).symm
  have hfV : layerPast kem cipher macS kdfS streamS geom hops d payload j V (j + 1) = .ok fwd :=
    (layerPast_tail geom kem kdfS streamS cipher macS hrouting hops d payload j U V hU hVs hlen
      hj hVt).symm.trans hfwd
  refine ⟨hVs, hfV, ?_⟩
  have hs := relayFront_size geom kem kdfS streamS cipher macS hvalid hmactag hops d payload j c
    V fwd hj hlen hc hfV hcmd
  have hs' := relayFront_size geom kem kdfS streamS cipher macS hvalid hmactag hops' d' payload
    j c U' fwd' hj' hlen' hc hfwd' hcmd'
  have h0 := relayFront_canon geom kem kdfS streamS cipher macS hvalid hmactag hops d payload j
    c V fwd hj hlen hVs hc hfV hs
  have h1 := relayFront_canon geom kem kdfS streamS cipher macS hvalid hmactag hops' d' payload
    j c U' fwd' hj' hlen' hU' hc hfwd' hs'
  rw [← hX0] at h0
  rw [← hX1] at h1
  have hv0 : v0AD.size = 2 := rfl
  have hXs : ∀ (X T W : ByteArray), (v0AD ++ c ++ xorBytes X W ++ T).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength → T.size = j * geom.perHopRoutingInfoLength
          →
      X.size = (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) := fun X T W h hT => by
    simp only [ByteArray.size_append, size_xorBytes, hc, hv0, hT] at h
    omega
  have hTs : ∀ (hp : Array PathHop) (dd : RSOR.Draw geom), hp.size ≤ geom.nrHops →
      j + 1 < hp.size →
      ((midPad geom kem kdfS streamS hp dd j).extract ((geom.nrHops - hp.size) *
          geom.perHopRoutingInfoLength)
        ((geom.nrHops - hp.size) * geom.perHopRoutingInfoLength + j *
            geom.perHopRoutingInfoLength)).size = j * geom.perHopRoutingInfoLength :=
    fun hp dd hl hjj => by
    have hap : (geom.nrHops - hp.size) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    unfold midPad
    rw [ByteArray.size_extract, size_xorBytes,
      fillerAtF_size kem kdfS streamS geom hrouting hp _ _ j _ hl (by
        rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
        omega) (zeroBytes_size _) (j + 1) hjj, Nat.add_mul, Nat.succ_mul]
    omega
  have hX0s := hXs X0 _ _ (h0 ▸ hs) (hTs hops d hlen hj)
  have hX1s := hXs X1 _ _ (h1 ▸ hs') (hTs hops' d' hlen' hj')
  rw [h0, h1, htail, hV, Util.Bytes.extract_append_of_le _ _ (by rw [size_xorBytes, hUh]),
    extract_all _ _ (by rw [size_xorBytes, hUh]),
    xorBytes_shift X0 X1 _ (hX0s.trans hX1s.symm) (hUh.trans hX0s.symm)]

/-- A draw whose seeds after position `j` and whose first `a` bytes of padding are another
draw's. -/
def joinDraw (d d' : RSOR.Draw geom) (j a : ℕ) : RSOR.Draw geom :=
  (Vector.ofFn fun i : Fin geom.nrHops =>
    if i.val ≤ j then d.1[i.val]'i.isLt else d'.1[i.val - (j + 1)]'(by have := i.isLt; omega),
    Vector.ofFn fun i : Fin geom.routingInfoLength =>
      if i.val < a then d'.2[i.val]'i.isLt else d.2[i.val]'i.isLt)

omit kem kdfS streamS cipher macS in
/-- The first `a` bytes of a joined draw's padding are the other draw's. -/
theorem joinDraw_prefix (d d' : RSOR.Draw geom) (j a : ℕ) :
    (ofVector (joinDraw geom d d' j a).2).extract 0 a = (ofVector d'.2).extract 0 a := by
  apply ByteArray.ext_getElem
  · simp [ByteArray.size_extract]
  · intro i h1 h2
    have hi : i < a := by
      simp [ByteArray.size_extract] at h1
      omega
    simp [ofVector, ByteArray.getElem_eq_getElem_data, joinDraw, hi]

omit kem kdfS streamS cipher macS in
/-- The seeds of a joined draw after position `j` are the other draw's first seeds. -/
theorem joinDraw_extract_after (d d' : RSOR.Draw geom) (j a n : ℕ) (hn : n ≤ geom.nrHops) :
    ((joinDraw geom d d' j a).1.toArray.extract 0 n).extract (j + 1)
        ((joinDraw geom d d' j a).1.toArray.extract 0 n).size
      = d'.1.toArray.extract 0 (n - (j + 1)) := by
  apply Array.ext
  · simp
    omega
  · intro i h1 h2
    have hi : j + 1 + i < n := by
      simp at h1
      omega
    simp [joinDraw, show ¬ (j + 1 + i ≤ j) by omega]

/-- What joining two draws leaves over: the first draw's seeds after position `j`, moved to
the front of the second draw's, and the second draw's padding with the first `a` bytes of the
first's. -/
def coJoin (d d' : RSOR.Draw geom) (j a : ℕ) : RSOR.Draw geom :=
  (Vector.ofFn fun i : Fin geom.nrHops =>
    if h : i.val + (j + 1) < geom.nrHops then d.1[i.val + (j + 1)]'h else d'.1[i.val]'i.isLt,
    Vector.ofFn fun i : Fin geom.routingInfoLength =>
      if i.val < a then d.2[i.val]'i.isLt else d'.2[i.val]'i.isLt)

omit kem kdfS streamS cipher macS in
/-- Joining twice gives the first draw back. -/
theorem joinDraw_joinDraw (d d' : RSOR.Draw geom) (j a : ℕ) :
    joinDraw geom (joinDraw geom d d' j a) (coJoin geom d d' j a) j a = d := by
  obtain ⟨s, f⟩ := d
  obtain ⟨s', f'⟩ := d'
  unfold joinDraw coJoin
  refine Prod.ext (Vector.ext fun i hi => ?_) (Vector.ext fun i hi => ?_)
  · by_cases h : i ≤ j
    · simp [h]
    · have h2 : i - (j + 1) + (j + 1) = i := by omega
      simp [h, h2, hi]
  · by_cases h : i < a <;> simp [h]

omit kem kdfS streamS cipher macS in
/-- Joining twice gives the second draw back. -/
theorem coJoin_coJoin (d d' : RSOR.Draw geom) (j a : ℕ) :
    coJoin geom (joinDraw geom d d' j a) (coJoin geom d d' j a) j a = d' := by
  obtain ⟨s, f⟩ := d
  obtain ⟨s', f'⟩ := d'
  unfold joinDraw coJoin
  refine Prod.ext (Vector.ext fun i hi => ?_) (Vector.ext fun i hi => ?_)
  · by_cases h : i + (j + 1) < geom.nrHops
    · simp [h, show ¬ (i + (j + 1) ≤ j) by omega]
    · simp [h]
  · by_cases h : i < a <;> simp [h]

omit kem kdfS streamS cipher macS in
/-- Past its first `a` bytes, the leftover's padding is the second draw's. -/
theorem coJoin_region (d d' : RSOR.Draw geom) (j a t : ℕ) :
    (ofVector (coJoin geom d d' j a).2).extract a (a + t) = (ofVector d'.2).extract a (a + t) := by
  apply ByteArray.ext_getElem
  · simp [ByteArray.size_extract]
  · intro i h1 h2
    simp [ofVector, ByteArray.getElem_eq_getElem_data, coJoin]

/-- World 0's randomness, from the randomness of the world where the relay sends on a reply
layer over the rest of the backward path and the randomness of that layer. -/
def backMix (r r' : RSOR.Randomness geom) (j a : ℕ) : RSOR.Randomness geom :=
  (r.1, joinDraw geom r.2.1 r'.1 j a, r.2.2.1, r'.2.2.2)

/-- What `backMix` leaves over. -/
def backCo (r r' : RSOR.Randomness geom) (j a : ℕ) : RSOR.Randomness geom :=
  (coJoin geom r.2.1 r'.1 j a, r'.2.1, r'.2.2.1, r.2.2.2)

omit kem kdfS streamS cipher macS in
/-- **The mixed randomness is uniform.** A game that reads two uniform draws through `backMix`
and `backCo` reads two uniform draws. -/
theorem evalDistEq_backMix {δ : Type} (j a : ℕ)
    (K : RSOR.Randomness geom → RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let r' ← $ᵗ (RSOR.Randomness geom)
      K (backMix geom r r' j a) (backCo geom r r' j a))
      =ᵈ (do
        let r ← $ᵗ (RSOR.Randomness geom)
        let r' ← $ᵗ (RSOR.Randomness geom)
        K r r') := by
  have hb : Function.Bijective (Function.uncurry fun (r r' : RSOR.Randomness geom) =>
      (backMix geom r r' j a, backCo geom r r' j a)) :=
    Function.Involutive.bijective fun p => by
      obtain ⟨r, r'⟩ := p
      simp only [Function.uncurry, backMix, backCo, joinDraw_joinDraw, coJoin_coJoin]
  have hid : Function.Bijective (Function.uncurry fun (x y : RSOR.Randomness geom) => (x, y)) :=
    Function.bijective_id
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hb fun p => K p.1 p.2) ?_
  exact (evalDistEq_pair_of_bijective hid fun p => K p.1 p.2).symm

omit streamS cipher macS in
/-- The keys of the hops up to position `j` under a joined draw are the first draw's, whatever
the last hop's commands. -/
theorem kemHopKeys_joinDraw (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last last' : List RoutingCommand) (d d' : RSOR.Draw geom) (j a m : ℕ) (hm : m ≤ j)
    (hj : j < R.hops.length) :
    kemHopKeys kem kdfS (RSOR.path kem R last)
        ((joinDraw geom d d' j a).1.toArray.extract 0 (RSOR.path kem R last).size) m
      = kemHopKeys kem kdfS (RSOR.path kem R last') (d.1.toArray.extract 0 (RSOR.path kem R
          last').size) m := by
  have hle := R.length_le
  unfold kemHopKeys
  rw [RSOR.path_getElem! kem R last m (by omega), RSOR.path_getElem! kem R last' m (by omega),
    RSOR.path_size, RSOR.path_size, getElem!_pos _ _ (by simp; omega),
    getElem!_pos _ _ (by simp; omega)]
  simp [joinDraw, hm]

/-- The keystream that makes a hop in the middle of one path, under a joined draw, give the
header bytes it has on a second path of the same length under the first draw, and the layers
of the rest of the path under the second draw. Its head is the second path's keystream shifted
by the difference of the two routing informations; its tail sets the next layer's filler to
the second draw's padding. -/
def backShift (hops hops' : Array PathHop) (d0 d dS : RSOR.Draw geom) (j : ℕ)
    (U fwd fwd' : ByteArray) : ByteArray :=
  (xorBytes (U.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d0 j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength))))
    ++ (xorBytes ((ofVector dS.2).extract ((geom.nrHops - hops.size) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) +
        (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom hops (d0.1.toArray.extract 0 hops.size)
        ((ofVector d0.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)) j
            (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector d0.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)).size
            (((ofVector d0.2).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)).size + (j + 1) * geom.perHopRoutingInfoLength)))

set_option maxHeartbeats 2000000 in
/-- **The backward path at the honest relay, relabelled.** On a path with the joined draw and
the shifted keystream, the keyed hop has the header bytes it has with the first draw and the
keystream `U`, whatever the two last commands, and the layers after it are the layers over the
rest of the path with the second draw. -/
theorem backShift_spec (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (last last' : List RoutingCommand)
    (d dS : RSOR.Draw geom) (payload : ByteArray) (j a : ℕ) (c U fwd fwd' : ByteArray)
    (ha : a = ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength))
    (hj : j + 1 < R.hops.length) (hU : U.size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) (hc : c.size = kem.ciphertextSize)
    (hfwd' : layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last') d payload j U (j +
        1) = .ok fwd')
    (hfwd : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) dS
        payload 0 = .ok fwd) :
    (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw geom
        d dS j a) d dS j U fwd fwd').size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)
    ∧ relayFront kem cipher macS kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j a)
        payload j c
        (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw
            geom d dS j a) d dS j U fwd fwd')
      = relayFront kem cipher macS kdfS streamS geom (RSOR.path kem R last') d payload j c U
    ∧ ∀ i, j + 1 + i ≤ R.hops.length →
      layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j a)
          payload j
          (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw
              geom d dS j a) d dS j U fwd fwd') (j + 1 + i)
        = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) dS
            payload i := by
  subst ha
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hsz0 : (RSOR.path kem R last).size = R.hops.length := RSOR.path_size kem R last
  have hsz1 : (RSOR.path kem R last').size = R.hops.length := RSOR.path_size kem R last'
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
  have hfill : ∀ H : ByteArray, H.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) -
      (j + 1) * geom.perHopRoutingInfoLength →
      fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops -
          (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j
        (H ++ (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))) (j + 1)
      = (ofVector dS.2).extract 0 ((geom.nrHops - (RSOR.path kem (R.drop (j + 1)) last).size) *
          geom.perHopRoutingInfoLength) := fun H hH => by
    rw [fillerAtF_target kem geom kdfS streamS hrouting _ _ _ j H _ hH hT hlen0 hj0 hf,
      joinDraw_prefix, ← hpadS]
    exact extract_adjacent _ 0 _ _ (Nat.zero_le _) (Nat.le_add_right _ _)
      (by rw [Util.Bytes.size_ofVector]; exact hpad)
  have hdrop := fun (H : ByteArray) (hH : H.size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) =>
    layerPast_drop kem geom kdfS streamS cipher macS R last (joinDraw geom d dS j ((geom.nrHops -
        (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) dS payload j
      (H ++ (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))) hseeds (hfill H hH)
  have hZ : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)).size =
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength := by
    rw [zeroBytes_size, Nat.succ_mul]
    rw [Nat.succ_mul] at hjp
    omega
  have hTs : (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength))).size = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [size_xorBytes, hT]
  have hU1 : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes
      ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))).size = (geom.routingInfoLength +
            geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_append, hZ, hTs]
    omega
  have hcmd : ∀ l : List RoutingCommand, ((RSOR.path kem R l)[j]!).commands = [] := fun l => by
    rw [RSOR.path_getElem! kem R l j (by omega), ite_eq_right (by omega)]
  have htail : (midPad geom kem kdfS streamS (RSOR.path kem R last) (joinDraw geom d dS j
      ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j).extract
      ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)
        (((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + j *
            geom.perHopRoutingInfoLength)
      = (midPad geom kem kdfS streamS (RSOR.path kem R last') d j).extract ((geom.nrHops -
          (RSOR.path kem R last').size) * geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path
          kem R last').size) * geom.perHopRoutingInfoLength) + j * geom.perHopRoutingInfoLength) :=
          by
    rw [midPad_front geom kem kdfS streamS hvalid _ _ j hj0 hlen0 j le_rfl,
      midPad_front geom kem kdfS streamS hvalid _ _ j (lt_of_lt_of_eq hj hsz1.symm)
        (le_of_eq_of_le hsz1 hle) j le_rfl]
    exact frontPadOf_congr geom kem kdfS streamS _ _ _ _ j
      (fun m hm => kemHopKeys_joinDraw kem geom kdfS R last last' d dS j _ m (by omega)
        (by omega))
      j le_rfl
  have hs := relayFront_headShift kem geom kdfS streamS cipher macS hvalid hmactag (RSOR.path kem R
      last)
    (RSOR.path kem R last') (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
        geom.perHopRoutingInfoLength)) d payload j c
    (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes ((ofVector
        dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)
        (((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + (j + 1) *
        geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))) U fwd fwd' hj0 hlen0 (hsz1.trans hsz0.symm) hU1 hU hc
    (hcmd last) (hcmd last') ((hdrop _ hZ 0 (by omega)).trans hfwd) hfwd' htail
  have ht : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes
      ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))).extract (geom.routingInfoLength - j *
            geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      = (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength))) := by
    rw [Util.Bytes.extract_append_of_ge _ _ (by rw [zeroBytes_size]), zeroBytes_size,
      Nat.sub_self]
    exact extract_all _ _ (by rw [hTs, Nat.succ_mul]; rw [Nat.succ_mul] at hjp; omega)
  rw [ht] at hs
  have hHs : (xorBytes (U.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem (RSOR.path kem R last') j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + ((RSOR.path kem R last').size - (j + 1)) *
              geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R last') d j).extract 0 ((geom.nrHops -
            (RSOR.path kem R last').size) * geom.perHopRoutingInfoLength))
        (midFrag geom kem (RSOR.path kem R last) j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + ((RSOR.path kem R last).size - (j + 1)) *
              geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R last) (joinDraw geom d dS j ((geom.nrHops
            - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)))).size =
            (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
            geom.perHopRoutingInfoLength := by
    have h := hs.1
    rw [ByteArray.size_append, hTs] at h
    omega
  exact ⟨hs.1, hs.2.2, hdrop _ hHs⟩

omit kem kdfS streamS cipher macS in
theorem backMix_backMix (r r' : RSOR.Randomness geom) (j a : ℕ) :
    backMix geom (backMix geom r r' j a) (backCo geom r r' j a) j a = r := by
  simp only [backMix, backCo, joinDraw_joinDraw]

omit kem kdfS streamS cipher macS in
theorem backCo_backCo (r r' : RSOR.Randomness geom) (j a : ℕ) :
    backCo geom (backMix geom r r' j a) (backCo geom r r' j a) j a = r' := by
  simp only [backMix, backCo, coJoin_coJoin]

set_option maxHeartbeats 4000000 in
/-- **The relabelled draws are uniform, on the backward path.** A game that reads the two
randomness draws through their mix, and the keystream through the shifted keystream, reads one
randomness draw and one keystream. -/
theorem evalDistEq_backShift {δ : Type} (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (payload : ByteArray) (j : ℕ)
    (hj : j + 1 < R.hops.length)
    (K : Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength) → RSOR.Randomness
        geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let r' ← $ᵗ (RSOR.Randomness geom)
      let U ← $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength))
      K (Util.Bytes.toVecN _ (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply
          r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2])
        (backMix geom r r' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.1
            r.2.1 r'.1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply r'.2.2.2])
          r'.1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty)))
        (backMix geom r r' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)))
      =ᵈ (do
        let r ← $ᵗ (RSOR.Randomness geom)
        let U ← $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength))
        K U r) := by
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
  have e := evalDistEq_backMix geom j ((geom.nrHops - R.hops.length) *
      geom.perHopRoutingInfoLength) (fun r₀ r₀' =>
    $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)) >>= fun U =>
      K (Util.Bytes.toVecN _ (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply (backCo
          geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        (RSOR.path kem R [.surbReply (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
        r₀.2.1 (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length)
            * geom.perHopRoutingInfoLength)).1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).1
              payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
            (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty))) r₀)
  simp only [backMix_backMix, backCo_backCo] at e
  refine EvalDistEq.trans e (EvalDistEq.bind_right _ fun r₀ => ?_)
  have hg : Function.Bijective (Function.uncurry fun (P : Vector UInt8 geom.routingInfoLength)
      (q : Vector (Vector UInt8 32) geom.nrHops
        × (RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16)) =>
      (((q.1, P), q.2) : RSOR.Randomness geom)) :=
    ⟨fun x y h => by
      obtain ⟨P, q1, q2⟩ := x
      obtain ⟨P', q1', q2'⟩ := y
      simp only [Function.uncurry, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst h1 h2 h3
      rfl, fun r => ⟨(r.1.2, (r.1.1, r.2)), rfl⟩⟩
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hg fun r₀' =>
    $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)) >>= fun U =>
      K (Util.Bytes.toVecN _ (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply (backCo
          geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        (RSOR.path kem R [.surbReply (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
        r₀.2.1 (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length)
            * geom.perHopRoutingInfoLength)).1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).1
              payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
            (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty))) r₀).symm ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun q => ?_)
    (OracleComp.EvalDistEq.bind_const _ _)
  have key : ∀ (P : Vector UInt8 geom.routingInfoLength) (U : Vector UInt8 (geom.routingInfoLength
      + geom.perHopRoutingInfoLength)),
      (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P), q.2)
          j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        r₀.2.1 (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty))
      = xorBytes ((ofVector U).extract 0 (geom.routingInfoLength - j *
          geom.perHopRoutingInfoLength))
          ((fun (P : Vector UInt8 geom.routingInfoLength) (T : ByteArray) => xorBytes
            (midFrag geom kem (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P), q.2) j
                ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
                layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
                geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
                geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j
                ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 j).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength))
            (midFrag geom kem (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P), q.2) j
                ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
                RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
                [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
                geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) r₀.2.1
            j).extract 0 ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength))) P
            ((ofVector U).extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)))
        ++ xorBytes ((ofVector P).extract ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength) (((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength) + ((j + 1) * geom.perHopRoutingInfoLength)))
          ((fillerAtF kem kdfS streamS geom (RSOR.path kem R [.surbReply r₀.2.2.2])
              (r₀.2.1.1.toArray.extract 0 R.hops.length)
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).size (((ofVector r₀.2.1.2).extract 0 ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)) := fun P U => by
    have htl : layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
        geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops -
        R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j (ofVector U) (j + 1)
        = layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix geom r₀
            ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (ofVector
              U).extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
              (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1) := by
      refine layerPast_tail geom kem kdfS streamS cipher macS hrouting _ _ payload j _ _
        (Util.Bytes.size_ofVector _) ?_ (by rw [RSOR.path_size]; exact hle)
        (by rw [RSOR.path_size]; exact hj) ?_
      · rw [ByteArray.size_append, zeroBytes_size, ByteArray.size_extract,
          Util.Bytes.size_ofVector]
        omega
      · rw [show (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
          geom.perHopRoutingInfoLength = (geom.routingInfoLength - j *
          geom.perHopRoutingInfoLength) by omega,
          Util.Bytes.extract_append_of_ge _ _ (by rw [zeroBytes_size]), zeroBytes_size,
          Nat.sub_self]
        exact (extract_all _ _ (by
          rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
          omega)).symm
    have hreg : (ofVector (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength)).1.2).extract ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength)
        = (ofVector P).extract ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)
            (((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength) + ((j + 1) *
            geom.perHopRoutingInfoLength)) :=
      coJoin_region geom _ _ j _ _
    unfold backShift
    simp only [RSOR.path_size]
    rw [htl, hreg]
    rfl
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun P => EvalDistEq.bind_right _ fun U => ?_)
    (evalDistEq_headRegion hat hm
    (fun (P : Vector UInt8 geom.routingInfoLength) (T : ByteArray) => xorBytes
      (midFrag geom kem (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P), q.2) j
          ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
          layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix geom r₀
          ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
          (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
          geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 j).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength))
      (midFrag geom kem (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P), q.2) j
          ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
          RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) [.surbReply
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
          geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) r₀.2.1
            j).extract 0 ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)))
    ((fillerAtF kem kdfS streamS geom (RSOR.path kem R [.surbReply r₀.2.2.2])
        (r₀.2.1.1.toArray.extract 0 R.hops.length)
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).size (((ofVector r₀.2.1.2).extract 0 ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)) (fun U₀ => K U₀ r₀))
  rw [key P U]

end RestOfPath

end Cryptlib.Protocols.Sphinx.KEMSphinx
