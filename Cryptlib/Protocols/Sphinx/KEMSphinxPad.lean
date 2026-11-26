/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTLU
import Cryptlib.Protocols.Sphinx.KEMSphinxTailChain
import Cryptlib.Protocols.Sphinx.KEMSphinxTailIndist

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common

/-! # The padding as a function of one hop's keystream

A header's padding is built from slices of the hops' keystreams, XORed together. So it depends
on one hop's keystream through one slice, which is XORed on: the padding with the keystream `U`
at a hop is the padding with a zero keystream there, XOR a slice of `U`. -/

section Pad

/-- Arithmetic with multiples of the block length: distribute, then decide. -/
local macro "arith" : tactic =>
  `(tactic| (simp only [Nat.add_mul, Nat.one_mul, Nat.zero_mul, Nat.add_zero] at *; omega))

variable (geom : Geometry)

local notation "𝓃" => geom.routingInfoLength + geom.perHopRoutingInfoLength

local notation "𝓅" => geom.perHopRoutingInfoLength

/-- A slice of zero bytes is zero bytes. -/
theorem extract_zeroBytes (n a b : ℕ) (h : b ≤ n) :
    (zeroBytes n).extract a b = zeroBytes (b - a) := by
  apply ByteArray.ext_getElem
  · simp [ByteArray.size_extract]
    omega
  · intro i h1 h2
    simp [zeroBytes, ByteArray.getElem_eq_getElem_data]

/-- XOR with zero bytes of the same width, on the left. -/
theorem zeroBytes_xorBytes_of_size (a : ByteArray) (m : ℕ) (h : m = a.size) :
    xorBytes (zeroBytes m) a = a := by
  subst h
  exact zeroBytes_xorBytes a

/-- The whole of a string, as a slice. -/
theorem extract_all (b : ByteArray) (n : ℕ) (h : b.size = n) : b.extract 0 n = b := by
  subst h
  exact ByteArray.extract_zero_size

/-- XOR with a mask that starts with enough zero bytes changes nothing. -/
theorem xorBytes_zeroBytes_append (a b : ByteArray) (n : ℕ) (h : a.size ≤ n) :
    xorBytes a (zeroBytes n ++ b) = a := by
  apply ByteArray.ext_getElem
  · simp
  · intro i h1 h2
    rw [xorBytes_getElem a _ i h2]
    split
    · rw [ByteArray.getElem_append_left (by simp; omega)]
      simp [zeroBytes, ByteArray.getElem_eq_getElem_data]
    · simp

/-- **`tailPadOf` is affine in one hop's keystream.** With the keystream `U` at hop `q`, it is
the padding with a zero keystream there, XOR the slice of `U` that hop `q` contributes. -/
theorem tailPadOf_affine (ks : ℕ → ByteArray) (q : ℕ) (U : ByteArray)
    (hU : U.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = geom.routingInfoLength + geom.perHopRoutingInfoLength) (d : ℕ)
    (hle : (q + d + 1) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength + geom.perHopRoutingInfoLength) :
    tailPadOf geom (fun k => if k = q then U else ks k) (q + d)
      = xorBytes
        (tailPadOf geom (fun k => if k = q then
          zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength) else ks k) (q + d))
        (U.extract
          (geom.routingInfoLength + geom.perHopRoutingInfoLength
            - (q + 1) * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength
            - q * geom.perHopRoutingInfoLength)) := by
  induction d with
  | zero =>
    cases q with
    | zero =>
      simp only [tailPadOf, ↓reduceIte]
      rw [extract_zeroBytes _ _ _ (by arith)]
      exact (zeroBytes_xorBytes_of_size _ _ (by
        rw [ByteArray.size_extract, hU]
        arith)).symm
    | succ q =>
      simp only [tailPadOf, ↓reduceIte]
      have hc : tailPadOf geom (fun k => if k = q + 1 then U else ks k) q
          = tailPadOf geom (fun k => if k = q + 1 then zeroBytes 𝓃 else ks k) q :=
        tailPadOf_congr geom _ _ q fun m hm => by simp [show m ≠ q + 1 by arith]
      have hT : (tailPadOf geom (fun k => if k = q + 1 then zeroBytes 𝓃 else ks k) q).size
          = geom.perHopRoutingInfoLength :=
        tailPadOf_size geom _ q (fun m _ => by split <;> simp [hks]) (by arith)
      rw [hc, extract_zeroBytes _ _ _ (by arith), zeroBytes_xorBytes_of_size _ _ (by
        rw [hT]
        arith)]
      exact xorBytes_comm_of_size_eq _ _ (by
        rw [hT, ByteArray.size_extract, hU]
        arith)
  | succ d ih =>
    have ih' := ih (by arith)
    have hT : (tailPadOf geom (fun k => if k = q then zeroBytes 𝓃 else ks k) (q + d)).size
        = geom.perHopRoutingInfoLength :=
      tailPadOf_size geom _ (q + d) (fun m _ => by split <;> simp [hks]) (by arith)
    have hUs : (U.extract (𝓃 - (q + 1) * geom.perHopRoutingInfoLength)
        (𝓃 - q * geom.perHopRoutingInfoLength)).size = geom.perHopRoutingInfoLength := by
      rw [ByteArray.size_extract, hU]
      have : (q + 1) * geom.perHopRoutingInfoLength
          = q * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
      arith
    have hS : ((ks (q + d + 1)).extract
        (𝓃 - (q + d + 1 + 1) * geom.perHopRoutingInfoLength)
        (𝓃 - (q + d + 1) * geom.perHopRoutingInfoLength)).size
          = geom.perHopRoutingInfoLength := by
      rw [ByteArray.size_extract, hks]
      have : (q + d + 1 + 1) * geom.perHopRoutingInfoLength
          = (q + d + 1) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength :=
        Nat.succ_mul _ _
      arith
    show tailPadOf geom _ (q + d + 1) = xorBytes (tailPadOf geom _ (q + d + 1)) _
    simp only [tailPadOf, show q + d + 1 ≠ q by arith, ↓reduceIte]
    rw [ih', xorBytes_comm_of_size_eq _ _ (hT.trans hUs.symm),
      xorBytes_left_comm _ _ _ (hS.trans hUs.symm) (hUs.trans hT.symm),
      xorBytes_comm_of_size_eq _ _ (by rw [size_xorBytes, hS, hUs])]

open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Util.Bytes (ofVector)

variable (kem : KEM) (kdfS : KDF) (streamS : StreamCipher)

/-- **The keyed filler is affine in the keyed hop's keystream.** With the keystream `U` at hop
`j`, the filler of a layer up to the one after hop `j` is the filler with a zero keystream
there, XOR the slice of `U` that the layers so far have folded in. -/
theorem fillerAtF_affine (hrouting : geom.routingInfoLength
      = geom.perHopRoutingInfoLength * geom.nrHops)
    (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (j : ℕ)
    (U : ByteArray) (hU : U.size = 𝓃) (hlen : hops.size ≤ geom.nrHops) (hj : j < hops.size)
    (hf : filler.size = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) (i : ℕ)
    (hi : i ≤ j + 1) :
    fillerAtF kem kdfS streamS geom hops seeds filler j U i
      = xorBytes (fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes 𝓃) i)
        (zeroBytes ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)
          ++ U.extract (𝓃 - (j + 1) * geom.perHopRoutingInfoLength)
            (𝓃 - (j + 1 - i) * geom.perHopRoutingInfoLength)) := by
  induction i with
  | zero =>
    simp only [fillerAtF]
    exact (xorBytes_zeroBytes_append _ _ _ hf.le).symm
  | succ i ih =>
    have ih' := ih (by omega)
    have hks : ∀ k, (headerKeystream streamS geom
        (kemHopKeys kem kdfS hops seeds (i + k))).size = 𝓃 := fun k =>
      streamS.keystream_size _ _ _
    have hfun : ∀ V : ByteArray, (fun k => if i + k = j then V
          else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + k)))
        = fun k => if k = j - i then V
          else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + k)) := fun V => by
      funext k
      have : (i + k = j) ↔ (k = j - i) := by omega
      simp only [this]
    have hpad := tailPadOf_affine geom (fun k => headerKeystream streamS geom
      (kemHopKeys kem kdfS hops seeds (i + k))) (j - i) U hU hks (hops.size - j - 1) (by
        have h1 : j - i + (hops.size - j - 1) + 1 = hops.size - i := by omega
        rw [h1, hrouting]
        have h2 : (hops.size - i) * geom.perHopRoutingInfoLength
            ≤ geom.nrHops * geom.perHopRoutingInfoLength :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.mul_comm geom.perHopRoutingInfoLength]
        omega)
    have hidx : j - i + (hops.size - j - 1) = hops.size - i - 1 := by omega
    rw [hidx] at hpad
    simp only [fillerAtF, tailFillerOf]
    rw [hfun U, hfun (zeroBytes 𝓃), hpad, ih']
    have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
      exact Nat.mul_le_mul_right _ (by omega)
    have hsplit : (j + 1) * geom.perHopRoutingInfoLength
        = (j + 1 - i) * geom.perHopRoutingInfoLength + i * geom.perHopRoutingInfoLength := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hstep : (j + 1 - i) * geom.perHopRoutingInfoLength
        = (j - i) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := by
      rw [show j + 1 - i = j - i + 1 by omega]
      exact Nat.succ_mul _ _
    rw [show j + 1 - (i + 1) = j - i by omega, show j - i + 1 = j + 1 - i by omega]
    by_cases hc : geom.nrHops > hops.size - i
    · simp only [hc, ↓reduceIte]
      rw [← extract_adjacent U (𝓃 - (j + 1) * geom.perHopRoutingInfoLength)
        (𝓃 - (j + 1 - i) * geom.perHopRoutingInfoLength)
        (𝓃 - (j - i) * geom.perHopRoutingInfoLength) (by omega) (by omega) (by omega),
        ← ByteArray.append_assoc]
      refine (xorBytes_append _ _ _ _ ?_).symm
      rw [fillerAtF_size kem kdfS streamS geom hrouting hops seeds filler j _ hlen hf
        (zeroBytes_size _) i (by omega), ByteArray.size_append, zeroBytes_size,
        ByteArray.size_extract, hU, Nat.add_mul]
      omega
    · obtain rfl : i = 0 := by omega
      have hsz : hops.size = geom.nrHops := by omega
      simp only [hsz, gt_iff_lt, lt_self_iff_false, ↓reduceIte, Nat.sub_self, Nat.zero_mul,
        Nat.sub_zero]
      show ByteArray.empty ++ _ = xorBytes (ByteArray.empty ++ _) (ByteArray.empty ++ _)
      simp only [ByteArray.empty_append]

/-- A mask over a fragment and a filler, when the filler already carries the tail of the
mask: the tail cancels, and the head masks the fragment and the front of the filler. -/
theorem xorBytes_mask_split (fr G1 G2 U : ByteArray) (a jp n : ℕ) (h1 : G1.size = a)
    (h2 : G2.size = jp) (hfr : fr.size + a + jp = n) (hU : n ≤ U.size) :
    xorBytes (fr ++ xorBytes (G1 ++ G2) (zeroBytes a ++ U.extract (n - jp) n)) (U.extract 0 n)
      = xorBytes (fr ++ G1) (U.extract 0 (n - jp)) ++ G2 := by
  rw [xorBytes_append G1 G2 (zeroBytes a) _ (by simp [h1]), xorBytes_zeroBytes,
    ← ByteArray.append_assoc, ← extract_adjacent U 0 (n - jp) n (by omega) (by omega) hU,
    xorBytes_append (fr ++ G1) _ _ _ (by
      rw [ByteArray.size_append, ByteArray.size_extract]
      omega),
    xorBytes_xorBytes]

/-- **The keyed filler, block by block.** The filler of layer `k` is the sender's filler, then
one block of padding for each layer before `k`. -/
theorem fillerAtF_block (hrouting : geom.routingInfoLength
      = geom.perHopRoutingInfoLength * geom.nrHops)
    (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (j : ℕ)
    (U : ByteArray) (hU : U.size = 𝓃) (hlen : hops.size ≤ geom.nrHops)
    (hf : filler.size = (geom.nrHops - hops.size) * 𝓅) (k i : ℕ) (hik : i < k)
    (hk : k < hops.size) :
    (fillerAtF kem kdfS streamS geom hops seeds filler j U k).extract
        ((geom.nrHops - hops.size) * 𝓅 + i * 𝓅) ((geom.nrHops - hops.size) * 𝓅 + (i + 1) * 𝓅)
      = tailPadOf geom (fun m => if i + m = j then U
          else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + m)))
        (hops.size - i - 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hpad : ∀ i', i' < hops.size → (tailPadOf geom (fun m => if i' + m = j then U
          else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i' + m)))
        (hops.size - i' - 1)).size = 𝓅 := fun i' hi' =>
      tailPadOf_size geom _ _ (fun m _ => by
        split
        · exact hU
        · exact streamS.keystream_size _ _ _) (by
        rw [show hops.size - i' - 1 + 1 = hops.size - i' by omega, hrouting, Nat.mul_comm 𝓅]
        have h2 : (hops.size - i') * 𝓅 ≤ geom.nrHops * 𝓅 := Nat.mul_le_mul_right _ (by omega)
        omega)
    have hsz := fillerAtF_size kem kdfS streamS geom hrouting hops seeds filler j U hlen hf hU
      k (by omega)
    rw [Nat.add_mul] at hsz
    have hi1 : (i + 1) * 𝓅 = i * 𝓅 + 𝓅 := Nat.succ_mul _ _
    simp only [fillerAtF, tailFillerOf]
    by_cases hc : geom.nrHops > hops.size - k
    · simp only [hc, ↓reduceIte]
      by_cases hik' : i < k
      · have hle : (i + 1) * 𝓅 ≤ k * 𝓅 := Nat.mul_le_mul_right _ (by omega)
        rw [Util.Bytes.extract_append_of_le _ _ (by omega)]
        exact ih hik' (by omega)
      · obtain rfl : i = k := by omega
        rw [Util.Bytes.extract_append_of_ge _ _ (by omega), hsz,
          Nat.sub_self, show (geom.nrHops - hops.size) * 𝓅 + (i + 1) * 𝓅
            - ((geom.nrHops - hops.size) * 𝓅 + i * 𝓅) = 𝓅 by omega]
        exact extract_all _ _ (hpad i (by omega))
    · obtain rfl : k = 0 := by omega
      obtain rfl : i = 0 := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ByteArray.empty_append,
        show (geom.nrHops - hops.size) * 𝓅 + 0 * 𝓅 = 0 by
          rw [show geom.nrHops - hops.size = 0 by omega]
          simp,
        show (geom.nrHops - hops.size) * 𝓅 + (0 + 1) * 𝓅 = 𝓅 by
          rw [show geom.nrHops - hops.size = 0 by omega]
          simp]
      exact extract_all _ _ (hpad 0 (by omega))

/-! ## A header's last bytes are affine in its filler -/

/-- XOR is associative on strings of one width. -/
theorem xorBytes_assoc (a b c : ByteArray) (hab : a.size = b.size) (hbc : b.size = c.size) :
    xorBytes (xorBytes a b) c = xorBytes a (xorBytes b c) := by
  rw [xorBytes_comm_of_size_eq _ c (by rw [size_xorBytes, hab, hbc]),
    xorBytes_left_comm c a b (by omega) hab, xorBytes_comm_of_size_eq c b hbc.symm]

/-- What the hops of a path XOR onto the filler: after the last `t` hops, the slices of their
keystreams that cover it. -/
def traceMask (ks : ℕ → ByteArray) (size f : ℕ) : ℕ → ByteArray
  | 0 => zeroBytes f
  | t + 1 => xorBytes (traceMask ks size f t)
      ((ks (size - 1 - t)).extract ((t + 1) * geom.perHopRoutingInfoLength)
        ((t + 1) * geom.perHopRoutingInfoLength + f))

theorem traceMask_size (ks : ℕ → ByteArray) (size f t : ℕ) :
    (traceMask geom ks size f t).size = f := by
  cases t with
  | zero => exact zeroBytes_size f
  | succ t => rw [traceMask, size_xorBytes, traceMask_size]

/-- **A header's last bytes are its filler XOR a mask that does not depend on the filler.** -/
theorem hdrTrace_tail (hrouting : geom.routingInfoLength
      = geom.perHopRoutingInfoLength * geom.nrHops)
    (hperhop : geom.nextNodeHopLength + kem.ciphertextSize ≤ geom.perHopRoutingInfoLength)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ke : Array ByteArray)
    (filler : ByteArray) (path : Array PathHop) (hple : path.size ≤ geom.nrHops)
    (hF : (if geom.nrHops > path.size then filler else ByteArray.empty).size
      = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ h, (ks h).size = 𝓃) (hkn : ke.size = path.size)
    (hksz : ∀ j (hj : j < ke.size), (ke[j]'hj).size = kem.ciphertextSize) (t : ℕ)
    (ht : t ≤ path.size) (s : ByteArray × ByteArray)
    (hs : hdrTrace kem geom ks tag ke filler path t = .ok s) :
    s.1.size = t * geom.perHopRoutingInfoLength
        + (geom.nrHops - path.size) * geom.perHopRoutingInfoLength ∧
      s.1.extract (t * geom.perHopRoutingInfoLength)
          (t * geom.perHopRoutingInfoLength
            + (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
        = xorBytes (if geom.nrHops > path.size then filler else ByteArray.empty)
          (traceMask geom ks path.size
            ((geom.nrHops - path.size) * geom.perHopRoutingInfoLength) t) := by
  induction t generalizing s with
  | zero =>
    simp only [hdrTrace, Except.ok.injEq] at hs
    subst hs
    refine ⟨by rw [hF]; omega, ?_⟩
    simp only [traceMask, xorBytes_zeroBytes, Nat.zero_mul, Nat.zero_add]
    rw [← hF]
    exact ByteArray.extract_zero_size
  | succ t ih =>
    obtain ⟨s0, frag, hs0, hfrag, rfl⟩ := hdrTrace_succ_ok kem geom ks tag ke filler path t s hs
    obtain ⟨hsz0, hext0⟩ := ih (by omega) s0 hs0
    have hfr := kemRiFragment_size kem geom path ke s0.2 path.size (path.size - 1 - t)
      (by omega) hperhop hnnh hkn hksz frag hfrag
    have h1 : path.size - 1 - t + 1 = path.size - t := by omega
    have h2 : (path.size - t) * 𝓅 + (t + 1) * 𝓅 = (path.size + 1) * 𝓅 := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have h3 : (geom.nrHops - path.size) * 𝓅 + (path.size + 1) * 𝓅 = (geom.nrHops + 1) * 𝓅 := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have h4 : (geom.nrHops + 1) * 𝓅 = 𝓃 := by
      rw [Nat.add_mul, Nat.one_mul, hrouting, Nat.mul_comm]
    have h5 : (t + 1) * 𝓅 = t * 𝓅 + 𝓅 := Nat.succ_mul _ _
    have hK : 𝓃 - (path.size - 1 - t + 1) * 𝓅
        = (t + 1) * 𝓅 + (geom.nrHops - path.size) * 𝓅 := by
      rw [h1]
      omega
    have hsl : ((ks (path.size - 1 - t)).extract ((t + 1) * 𝓅)
        ((t + 1) * 𝓅 + (geom.nrHops - path.size) * 𝓅)).size
        = (geom.nrHops - path.size) * 𝓅 := by
      rw [ByteArray.size_extract, hks]
      omega
    refine ⟨by rw [size_xorBytes, ByteArray.size_append, hfr, hsz0]; omega, ?_⟩
    rw [xorBytes_extract _ _ _ _ (by rw [ByteArray.size_append, hfr, hsz0]; omega)
        (by rw [ByteArray.size_extract, hks]; omega),
      Util.Bytes.extract_append_of_ge frag s0.1 (by rw [hfr]; omega), hfr,
      show (t + 1) * 𝓅 - 𝓅 = t * 𝓅 by omega,
      show (t + 1) * 𝓅 + (geom.nrHops - path.size) * 𝓅 - 𝓅
        = t * 𝓅 + (geom.nrHops - path.size) * 𝓅 by omega,
      hext0, ByteArray.extract_extract, Nat.zero_add, Nat.zero_add,
      Nat.min_eq_left (by omega)]
    simp only [traceMask]
    exact xorBytes_assoc _ _ _ (hF.trans (traceMask_size geom _ _ _ _).symm)
      ((traceMask_size geom _ _ _ _).trans hsl.symm)


/-- `traceMask` reads the keystreams of the hops on the path only. -/
theorem traceMask_congr (ks ks' : ℕ → ByteArray) (size f t : ℕ) (ht : t ≤ size)
    (h : ∀ m, m < size → ks m = ks' m) :
    traceMask geom ks size f t = traceMask geom ks' size f t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [traceMask, ih (by omega), h (size - 1 - t) (by omega)]

/-- **The hops after the keyed one cancel in the padding of the hops before it.** The padding
block of a layer up to the keyed hop's, under the mask of the hops after the keyed hop, is
that block built from the hops up to the keyed hop only. -/
theorem tailPadOf_traceMask (hrouting : geom.routingInfoLength
      = geom.perHopRoutingInfoLength * geom.nrHops)
    (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (hseeds : seeds.size = hops.size)
    (hlen : hops.size ≤ geom.nrHops) (j i : ℕ) (hi : i ≤ j) (hj : j + 1 < hops.size) (t : ℕ)
    (ht : t ≤ hops.size - (j + 1)) :
    xorBytes
        (tailPadOf geom (fun m => if i + m = j then zeroBytes 𝓃
            else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + m)))
          (hops.size - i - 1))
        ((traceMask geom (fun m => headerKeystream streamS geom
            (kemHopKeys kem kdfS (hops.extract (j + 1) hops.size)
              (seeds.extract (j + 1) seeds.size) m))
          (hops.size - (j + 1)) ((geom.nrHops - (hops.size - (j + 1))) * 𝓅) t).extract
          ((geom.nrHops - hops.size) * 𝓅 + i * 𝓅) ((geom.nrHops - hops.size) * 𝓅 + (i + 1) * 𝓅))
      = tailPadOf geom (fun m => if i + m = j then zeroBytes 𝓃
            else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + m)))
          (hops.size - i - 1 - t) := by
  have hi1 : (i + 1) * 𝓅 = i * 𝓅 + 𝓅 := Nat.succ_mul _ _
  have hnm : (geom.nrHops - (hops.size - (j + 1))) * 𝓅
      = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hij : (i + 1) * 𝓅 ≤ (j + 1) * 𝓅 := Nat.mul_le_mul_right _ (by omega)
  have hpsz : ∀ n, n < hops.size - i → (tailPadOf geom (fun m => if i + m = j then zeroBytes 𝓃
        else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + m))) n).size
      = 𝓅 := fun n hn =>
    tailPadOf_size geom _ _ (fun m _ => by
      split
      · exact zeroBytes_size _
      · exact streamS.keystream_size _ _ _) (by
      rw [hrouting, Nat.mul_comm 𝓅]
      have h2 : (n + 1) * 𝓅 ≤ geom.nrHops * 𝓅 := Nat.mul_le_mul_right _ (by omega)
      omega)
  induction t with
  | zero =>
    simp only [traceMask, Nat.sub_zero]
    rw [extract_zeroBytes _ _ _ (by omega), xorBytes_zeroBytes]
  | succ t ih =>
    have ih' := ih (by omega)
    obtain ⟨n', hn'⟩ : ∃ n', hops.size - i - 1 - t = n' + 1 :=
      ⟨hops.size - i - 1 - t - 1, by omega⟩
    have hn'' : hops.size - i - 1 - (t + 1) = n' := by omega
    have hprod : (n' + 1 + 1) * 𝓅 + (geom.nrHops - hops.size) * 𝓅 + (i + t + 1) * 𝓅 = 𝓃 := by
      rw [← Nat.add_mul, ← Nat.add_mul, hrouting, Nat.mul_comm 𝓅,
        show n' + 1 + 1 + (geom.nrHops - hops.size) + (i + t + 1) = geom.nrHops + 1 by omega,
        Nat.add_mul, Nat.one_mul]
    have hit : (i + t + 1) * 𝓅 = (t + 1) * 𝓅 + i * 𝓅 := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hn1 : (n' + 1 + 1) * 𝓅 = (n' + 1) * 𝓅 + 𝓅 := Nat.succ_mul _ _
    have hks : headerKeystream streamS geom
          (kemHopKeys kem kdfS (hops.extract (j + 1) hops.size)
            (seeds.extract (j + 1) seeds.size) (hops.size - (j + 1) - 1 - t))
        = headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + (n' + 1))) := by
      unfold kemHopKeys
      rw [getElem!_extract_from _ _ _ (by omega), getElem!_extract_from _ _ _ (by omega),
        show j + 1 + (hops.size - (j + 1) - 1 - t) = i + (n' + 1) by omega]
    have hksz : (headerKeystream streamS geom
        (kemHopKeys kem kdfS hops seeds (i + (n' + 1)))).size = 𝓃 :=
      streamS.keystream_size _ _ _
    simp only [traceMask]
    rw [xorBytes_extract _ _ _ _ (by rw [traceMask_size]; omega)
        (by rw [ByteArray.size_extract, hks, hksz]; omega),
      ← xorBytes_assoc _ _ _ (by
          rw [hpsz _ (by omega), ByteArray.size_extract, traceMask_size]
          omega) (by
          rw [ByteArray.size_extract, traceMask_size, ByteArray.size_extract,
            ByteArray.size_extract, hks, hksz]
          omega),
      ih', hn', hn'', hks, ByteArray.extract_extract]
    show xorBytes (xorBytes _ (tailPadOf geom _ n')) _ = _
    simp only [show i + (n' + 1) ≠ j by omega, ↓reduceIte]
    rw [show (t + 1) * 𝓅 + ((geom.nrHops - hops.size) * 𝓅 + i * 𝓅)
        = 𝓃 - (n' + 1 + 1) * 𝓅 by omega,
      Nat.min_eq_left (by omega),
      show (t + 1) * 𝓅 + ((geom.nrHops - hops.size) * 𝓅 + (i + 1) * 𝓅)
        = 𝓃 - (n' + 1) * 𝓅 by omega,
      xorBytes_comm_of_size_eq _ (tailPadOf geom _ n') (by
        rw [hpsz _ (by omega), ByteArray.size_extract, hksz]
        omega),
      xorBytes_xorBytes]


open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)

variable (cipher : WideBlockCipher) (macS : MAC)

/-- **A packet's last routing bytes are its filler XOR the mask of its hops' keystreams.** -/
theorem newKEMPacket_tail (hvalid : geom.ValidForKEM kem) (seeds : Array (Vector UInt8 32))
    (filler : ByteArray) (path : Array PathHop) (payload pkt : ByteArray)
    (h : newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload = .ok pkt) :
    pkt.extract (2 + kem.ciphertextSize + path.size * 𝓅)
        (2 + kem.ciphertextSize + geom.routingInfoLength)
      = xorBytes (if geom.nrHops > path.size then filler else ByteArray.empty)
        (traceMask geom (fun m => headerKeystream streamS geom (kemHopKeys kem kdfS path seeds m))
          path.size ((geom.nrHops - path.size) * 𝓅) path.size) := by
  obtain ⟨hnnh, hperhopEq, hrouting, -⟩ := id hvalid
  obtain ⟨-, hdr0, sprp0, _t0, hcreate0, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ h
  obtain ⟨hpos, hgen, hseeds, hfsize, ke, keys, _rks, _rp, _s, hkn, hkeys, -, -, hkc, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ _ _ hcreate0
  rw [newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom seeds filler path
    payload ke keys hpos hgen hseeds hfsize hkn hkeys hkc] at h
  obtain ⟨-, hdr, sprp, t, hcreate, -, -, hpkt⟩ :=
    newKEMPacketFrom_unfold kem cipher macS streamS geom _ _ _ _ _ _ h
  obtain ⟨s, htr, hhdr, -⟩ := createKEMHeaderFrom_hdrTrace kem geom macS streamS ke keys filler
    path hdr sprp hcreate
  have hF : (if geom.nrHops > path.size then filler else ByteArray.empty).size
      = (geom.nrHops - path.size) * 𝓅 := by
    split_ifs with hc
    · exact hfsize hc
    · rw [show geom.nrHops - path.size = 0 by omega, Nat.zero_mul]
      rfl
  have hksz : ∀ j (hj : j < ke.size), (ke[j]'hj).size = kem.ciphertextSize := fun j hj => by
    obtain ⟨ct, ss, henc, hct, -⟩ := hkc j (by omega)
    rw [← getElem!_pos ke j hj, hct]
    exact kemEncap_size kem _ _ ct ss henc
  obtain ⟨hsz, hext⟩ := hdrTrace_tail geom kem hrouting (by omega) hnnh
    (keysKs geom streamS keys) (keysTag macS keys) ke filler path hgen hF
    (fun _ => streamS.keystream_size _ _ _) hkn hksz path.size le_rfl s htr
  have hm : path.size * 𝓅 + (geom.nrHops - path.size) * 𝓅 = geom.routingInfoLength := by
    rw [← Nat.add_mul, hrouting, Nat.mul_comm]
    congr 1
    omega
  have hA : (v0AD ++ ke[0]!).size = 2 + kem.ciphertextSize := by
    rw [ByteArray.size_append, getElem!_pos ke 0 (by omega), hksz 0 (by omega)]
    rfl
  rw [hpkt, hhdr, Util.Bytes.extract_append_of_le _ _ (by
      simp only [ByteArray.size_append, hA, hsz]
      omega),
    Util.Bytes.extract_append_of_le _ _ (by
      simp only [ByteArray.size_append, hA, hsz]
      omega),
    Util.Bytes.extract_append_of_ge _ _ (by rw [hA]; omega), hA,
    show 2 + kem.ciphertextSize + path.size * 𝓅 - (2 + kem.ciphertextSize)
      = path.size * 𝓅 by omega,
    show 2 + kem.ciphertextSize + geom.routingInfoLength - (2 + kem.ciphertextSize)
      = path.size * 𝓅 + (geom.nrHops - path.size) * 𝓅 by omega,
    hext]
  refine congrArg _ (traceMask_congr geom _ _ _ _ _ le_rfl fun m hmlt => ?_)
  obtain ⟨ct, ss, henc, -, hk⟩ := hkc m hmlt
  unfold keysKs headerKeystream kemHopKeys
  rw [hk, henc]

/-! ## The honest relay's header at the end of a path -/

/-- The keyed filler of the keyed hop's own layer, with a zero keystream at that hop. -/
def zeroFiller (hops : Array PathHop) (d : RSOR.Draw geom) (j : ℕ) : ByteArray :=
  fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
    ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
    j (zeroBytes 𝓃) j

/-- The routing fragment of a last hop. -/
def lastFrag (hops : Array PathHop) (j : ℕ) (c : ByteArray) : ByteArray :=
  match kemRiFragment kem geom #[hops[j]!] #[c] ByteArray.empty 1 0 with
  | .ok f => f
  | .error _ => ByteArray.empty

/-- **The last hop's header bytes, in two parts.** When the keyed hop is last and its header
bytes have a header's length, they are its ciphertext, then routing information masked by the
head of its keystream, then padding that does not depend on its keystream. -/
theorem relayFrontLast_canon (hrouting : geom.routingInfoLength
      = geom.perHopRoutingInfoLength * geom.nrHops)
    (hops : Array PathHop) (d : RSOR.Draw geom) (j : ℕ) (c U : ByteArray)
    (hj : j + 1 = hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hc : c.size = kem.ciphertextSize)
    (hs : (relayFrontLast kem kdfS streamS geom hops d j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    relayFrontLast kem kdfS streamS geom hops d j c U
      = v0AD ++ c
        ++ xorBytes (lastFrag geom kem hops j c
            ++ (zeroFiller geom kem kdfS streamS hops d j).extract 0
              ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
          (U.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        ++ (zeroFiller geom kem kdfS streamS hops d j).extract
          ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)
          (zeroFiller geom kem kdfS streamS hops d j).size := by
  have hjs : j < hops.size := by omega
  have hap : (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hf : ((ofVector d.2).extract 0
      ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)).size
      = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have haff := fillerAtF_affine geom kem kdfS streamS hrouting hops
    (d.1.toArray.extract 0 hops.size) _ j U hU hlen hjs hf j (by omega)
  have hGsz := fillerAtF_size kem kdfS streamS geom hrouting hops
    (d.1.toArray.extract 0 hops.size) _ j (zeroBytes 𝓃) hlen hf (zeroBytes_size _) j hjs
  rw [Nat.add_mul] at hGsz
  have e1 : 𝓃 - (j + 1) * geom.perHopRoutingInfoLength
      = geom.routingInfoLength - j * geom.perHopRoutingInfoLength := by arith
  have e2 : 𝓃 - (j + 1 - j) * geom.perHopRoutingInfoLength = geom.routingInfoLength := by
    rw [show j + 1 - j = 1 by omega]
    arith
  rw [e1, e2] at haff
  have hFU : (if geom.nrHops > 1 then
        fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
          ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
          j U j
      else ByteArray.empty)
      = fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
          ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
          j U j := by
    split_ifs with hn
    · rfl
    · obtain rfl : j = 0 := by omega
      exact (eq_empty_of_size_zero _ (by
        simp only [fillerAtF]
        rw [hf, show geom.nrHops - hops.size = 0 by omega, Nat.zero_mul])).symm
  unfold relayFrontLast at hs ⊢
  rw [hFU] at hs ⊢
  rw [haff] at hs ⊢
  simp only [ByteArray.size_append, size_xorBytes, hGsz, hc] at hs
  have hv0 : v0AD.size = 2 := rfl
  obtain ⟨G, hG⟩ : ∃ G, G = zeroFiller geom kem kdfS streamS hops d j := ⟨_, rfl⟩
  have hGsz' : G.size = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength
      + j * geom.perHopRoutingInfoLength := by
    rw [hG]
    exact hGsz
  rw [← hG]
  have hG' : fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
      j (zeroBytes 𝓃) j = G := hG.symm
  rw [hG', show geom.routingInfoLength + geom.perHopRoutingInfoLength
      - (0 + 1) * geom.perHopRoutingInfoLength = geom.routingInfoLength by arith]
  conv_lhs => rw [← Util.Bytes.append_extract G
    ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) (by omega)]
  rw [xorBytes_mask_split _ _ _ U ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)
    (j * geom.perHopRoutingInfoLength) geom.routingInfoLength
    (by rw [ByteArray.size_extract]; omega) (by rw [ByteArray.size_extract]; omega)
    (by omega) (by omega), ← ByteArray.append_assoc]
  rfl

/-! ## The honest relay's header before the end of a path -/

/-- The padding the keyed hop's layer ends with, before the end of the path: the filler of the
next layer with a zero keystream at the keyed hop, under the mask of the hops after it. Its
first bytes are the sender's filler, its last `j` blocks the padding of the hops in front. -/
def midPad (hops : Array PathHop) (d : RSOR.Draw geom) (j : ℕ) : ByteArray :=
  xorBytes
    (fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j (zeroBytes 𝓃) (j + 1))
    (traceMask geom (fun m => headerKeystream streamS geom
        (kemHopKeys kem kdfS (hops.extract (j + 1) hops.size)
          ((d.1.toArray.extract 0 hops.size).extract (j + 1)
            (d.1.toArray.extract 0 hops.size).size) m))
      (hops.size - (j + 1)) ((geom.nrHops - (hops.size - (j + 1))) * 𝓅) (hops.size - (j + 1)))

/-- The routing fragment of a hop before the end of the path, read off what it forwards. -/
def midFrag (hops : Array PathHop) (j : ℕ) (fwd : ByteArray) : ByteArray :=
  match kemRiFragment kem geom (hops.extract j hops.size)
      #[ByteArray.empty, fwd.extract 2 (2 + kem.ciphertextSize)]
      (fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength))
      (hops.extract j hops.size).size 0 with
  | .ok f => f
  | .error _ => ByteArray.empty

/-- **A middle hop's header bytes, in two parts.** When the keyed hop is before the end of the
path and its header bytes have a header's length, they are its ciphertext, then routing
information masked by the head of its keystream, then padding that does not depend on its
keystream. -/
theorem relayFront_canon (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop)
    (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ) (c U fwd : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hc : c.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd)
    (hs : (relayFront kem cipher macS kdfS streamS geom hops d payload j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    relayFront kem cipher macS kdfS streamS geom hops d payload j c U
      = v0AD ++ c
        ++ xorBytes (midFrag geom kem hops j fwd
            ++ fwd.extract (2 + kem.ciphertextSize)
              (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)
            ++ (midPad geom kem kdfS streamS hops d j).extract 0
              ((geom.nrHops - hops.size) * 𝓅))
          (U.extract 0 (geom.routingInfoLength - j * 𝓅))
        ++ (midPad geom kem kdfS streamS hops d j).extract ((geom.nrHops - hops.size) * 𝓅)
          ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hjs : j < hops.size := by omega
  have hap : (geom.nrHops - hops.size) * 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm 𝓅]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hf : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)).size
      = (geom.nrHops - hops.size) * 𝓅 := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have haff := fillerAtF_affine geom kem kdfS streamS hrouting hops
    (d.1.toArray.extract 0 hops.size) _ j U hU hlen hjs hf (j + 1) le_rfl
  have hfwd' : newKEMPacket kem cipher macS kdfS streamS geom
      ((d.1.toArray.extract 0 hops.size).extract (j + 1) (d.1.toArray.extract 0 hops.size).size)
      (fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
        ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j U (j + 1))
      (hops.extract (j + 1) hops.size) payload = .ok fwd := hfwd
  have htail := newKEMPacket_tail geom kem kdfS streamS cipher macS hvalid _ _ _ _ _ hfwd'
  have hm : (hops.extract (j + 1) hops.size).size = hops.size - (j + 1) := by simp
  have hjm : (j + 1) * 𝓅 = j * 𝓅 + 𝓅 := Nat.succ_mul _ _
  have hnm : (geom.nrHops - (hops.size - (j + 1))) * 𝓅
      = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hmp : (hops.size - (j + 1)) * 𝓅 + (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅
      = geom.routingInfoLength := by
    rw [← Nat.add_mul, ← Nat.add_mul, hrouting, Nat.mul_comm]
    congr 1
    omega
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = fillerAtF kem kdfS streamS geom hops
      (d.1.toArray.extract 0 hops.size)
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j (zeroBytes 𝓃) (j + 1) :=
    ⟨_, rfl⟩
  obtain ⟨MK, hMK⟩ : ∃ MK, MK = traceMask geom (fun m => headerKeystream streamS geom
        (kemHopKeys kem kdfS (hops.extract (j + 1) hops.size)
          ((d.1.toArray.extract 0 hops.size).extract (j + 1)
            (d.1.toArray.extract 0 hops.size).size) m))
      (hops.size - (j + 1)) ((geom.nrHops - (hops.size - (j + 1))) * 𝓅)
      (hops.size - (j + 1)) := ⟨_, rfl⟩
  have hΦsz : Φ.size = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [hΦ, fillerAtF_size kem kdfS streamS geom hrouting hops _ _ j _ hlen hf
      (zeroBytes_size _) (j + 1) hj, Nat.add_mul]
  have hMKsz : MK.size = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [hMK, traceMask_size, hnm]
  have hW : midPad geom kem kdfS streamS hops d j = xorBytes Φ MK := by
    rw [hΦ, hMK]
    rfl
  rw [hm, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), haff, ← hΦ, ← hMK,
    show j + 1 - (j + 1) = 0 by omega, Nat.zero_mul, Nat.sub_zero,
    show 𝓃 - (j + 1) * 𝓅 = geom.routingInfoLength - j * 𝓅 by omega] at htail
  have hZsz : (zeroBytes ((geom.nrHops - hops.size) * 𝓅)
      ++ U.extract (geom.routingInfoLength - j * 𝓅) 𝓃).size
      = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [ByteArray.size_append, zeroBytes_size, ByteArray.size_extract, hU]
    omega
  rw [xorBytes_assoc _ _ _ (hΦsz.trans hZsz.symm) (hZsz.trans hMKsz.symm),
    xorBytes_comm_of_size_eq _ MK (hZsz.trans hMKsz.symm),
    ← xorBytes_assoc _ _ _ (hΦsz.trans hMKsz.symm) (hMKsz.trans hZsz.symm), ← hW] at htail
  obtain ⟨W, hWdef⟩ : ∃ W, W = midPad geom kem kdfS streamS hops d j := ⟨_, rfl⟩
  rw [← hWdef] at htail ⊢
  have hWsz : W.size = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [hWdef, hW, size_xorBytes, hΦsz]
  obtain ⟨-, -, -, hhdr, hpacket, -⟩ := id hvalid
  have hfsz : fwd.size = geom.packetLength :=
    newKEMPacket_size kem cipher macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hfwd'
      (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hfwd').1
  have had : adLength = 2 := rfl
  have hE2 : fwd.extract (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)
        (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅)
      = xorBytes (W.extract 0 ((geom.nrHops - hops.size) * 𝓅)
          ++ W.extract ((geom.nrHops - hops.size) * 𝓅)
            ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅))
        (zeroBytes ((geom.nrHops - hops.size) * 𝓅)
          ++ U.extract (geom.routingInfoLength - j * 𝓅) geom.routingInfoLength) := by
    have h1 := congrArg (fun x : ByteArray =>
      x.extract 0 ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅)) htail
    simp only [ByteArray.extract_extract] at h1
    rw [Nat.add_zero, Nat.min_eq_left (by omega),
      xorBytes_extract _ _ _ _ (by omega) (by omega),
      Util.Bytes.extract_append_le _ _ (by rw [zeroBytes_size]; omega), zeroBytes_size,
      Nat.add_sub_cancel_left, ByteArray.extract_extract, Nat.add_zero,
      Nat.min_eq_left (by omega),
      ← extract_adjacent W 0 ((geom.nrHops - hops.size) * 𝓅)
        ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅) (by omega) (by omega) (by omega)] at h1
    rw [show 2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅
        = 2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅
          + ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅) by omega]
    rw [Nat.add_zero, show geom.routingInfoLength - j * 𝓅 + j * 𝓅
      = geom.routingInfoLength by omega] at h1
    exact h1
  unfold relayFront at hs ⊢
  rw [hfwd] at hs ⊢
  dsimp only at hs ⊢
  have hsplit := extract_adjacent fwd (2 + kem.ciphertextSize)
    (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)
    (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅) (by omega) (by omega) (by omega)
  rw [← hsplit, hE2] at hs ⊢
  change (v0AD ++ c ++ xorBytes (midFrag geom kem hops j fwd ++ _) _).size = _ at hs
  show v0AD ++ c ++ xorBytes (midFrag geom kem hops j fwd ++ _) _ = _
  generalize midFrag geom kem hops j fwd = fr at hs ⊢
  have hE : (fwd.extract (2 + kem.ciphertextSize)
      (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)).size
      = (hops.size - (j + 1)) * 𝓅 := by
    rw [ByteArray.size_extract]
    omega
  have hG1 : (W.extract 0 ((geom.nrHops - hops.size) * 𝓅)).size
      = (geom.nrHops - hops.size) * 𝓅 := by
    rw [ByteArray.size_extract]
    omega
  have hG2 : (W.extract ((geom.nrHops - hops.size) * 𝓅)
      ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅)).size = j * 𝓅 := by
    rw [ByteArray.size_extract]
    omega
  have hv0 : v0AD.size = 2 := rfl
  simp only [ByteArray.size_append, size_xorBytes, hE, hG1, hG2, hc, hv0] at hs
  rw [← ByteArray.append_assoc,
    xorBytes_mask_split _ _ _ U ((geom.nrHops - hops.size) * 𝓅) (j * 𝓅)
      geom.routingInfoLength hG1 hG2 (by rw [ByteArray.size_append, hE]; omega) (by omega),
    ← ByteArray.append_assoc]

/-- **The next layer ends with the tail of the keyed hop's keystream.** -/
theorem layerPast_lastBlock (hvalid : geom.ValidForKEM kem) (hops : Array PathHop)
    (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ) (U fwd : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd) :
    fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅)
        (2 + kem.ciphertextSize + geom.routingInfoLength)
      = U.extract geom.routingInfoLength 𝓃 := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hap : (geom.nrHops - hops.size) * 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm 𝓅]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hf : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)).size
      = (geom.nrHops - hops.size) * 𝓅 := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hseeds : (d.1.toArray.extract 0 hops.size).size = hops.size := by
    simp
    omega
  have hfwd' : newKEMPacket kem cipher macS kdfS streamS geom
      ((d.1.toArray.extract 0 hops.size).extract (j + 1) (d.1.toArray.extract 0 hops.size).size)
      (fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
        ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j U (j + 1))
      (hops.extract (j + 1) hops.size) payload = .ok fwd := hfwd
  have htail := newKEMPacket_tail geom kem kdfS streamS cipher macS hvalid _ _ _ _ _ hfwd'
  have hm : (hops.extract (j + 1) hops.size).size = hops.size - (j + 1) := by simp
  have hjm : (j + 1) * 𝓅 = j * 𝓅 + 𝓅 := Nat.succ_mul _ _
  have hnm : (geom.nrHops - (hops.size - (j + 1))) * 𝓅
      = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hmp : (hops.size - (j + 1)) * 𝓅 + (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅
      = geom.routingInfoLength := by
    rw [← Nat.add_mul, ← Nat.add_mul, hrouting, Nat.mul_comm]
    congr 1
    omega
  have hΦsz := fillerAtF_size kem kdfS streamS geom hrouting hops
    (d.1.toArray.extract 0 hops.size) _ j U hlen hf hU (j + 1) hj
  rw [Nat.add_mul] at hΦsz
  rw [hm, ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at htail
  have h1 := congrArg (fun x : ByteArray => x.extract ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅)
    ((geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅)) htail
  simp only [ByteArray.extract_extract] at h1
  rw [Nat.min_eq_left (by omega),
    xorBytes_extract _ _ _ _ (by omega) (by rw [traceMask_size]; omega),
    fillerAtF_block geom kem kdfS streamS hrouting hops _ _ j U hU hlen hf (j + 1) j
      (by omega) hj] at h1
  have hfun : ∀ V : ByteArray, (fun m => if j + m = j then V
        else headerKeystream streamS geom (kemHopKeys kem kdfS hops
          (d.1.toArray.extract 0 hops.size) (j + m)))
      = fun m => if m = 0 then V
        else headerKeystream streamS geom (kemHopKeys kem kdfS hops
          (d.1.toArray.extract 0 hops.size) (j + m)) := fun V => by
    funext m
    have : (j + m = j) ↔ (m = 0) := by omega
    simp only [this]
  have haff := tailPadOf_affine geom (fun m => headerKeystream streamS geom
    (kemHopKeys kem kdfS hops (d.1.toArray.extract 0 hops.size) (j + m))) 0 U hU
    (fun _ => streamS.keystream_size _ _ _) (hops.size - j - 1) (by
      rw [hrouting, Nat.mul_comm 𝓅]
      have h2 : (0 + (hops.size - j - 1) + 1) * 𝓅 ≤ geom.nrHops * 𝓅 :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  have hcan := tailPadOf_traceMask geom kem kdfS streamS hrouting hops
    (d.1.toArray.extract 0 hops.size) hseeds hlen j j le_rfl hj (hops.size - (j + 1)) le_rfl
  rw [hfun (zeroBytes 𝓃)] at hcan
  rw [Nat.zero_add] at haff
  rw [hfun U, haff] at h1
  rw [show hops.size - j - 1 - (hops.size - (j + 1)) = 0 by omega] at hcan
  simp only [tailPadOf, ↓reduceIte] at hcan
  rw [extract_zeroBytes _ _ _ (by omega)] at hcan
  have hP0 : (tailPadOf geom (fun k => if k = 0 then zeroBytes 𝓃
        else headerKeystream streamS geom (kemHopKeys kem kdfS hops
          (d.1.toArray.extract 0 hops.size) (j + k))) (hops.size - j - 1)).size = 𝓅 :=
    tailPadOf_size geom _ _ (fun m _ => by
      split
      · exact zeroBytes_size _
      · exact streamS.keystream_size _ _ _) (by
      rw [hrouting, Nat.mul_comm 𝓅]
      have h2 : (hops.size - j - 1 + 1) * 𝓅 ≤ geom.nrHops * 𝓅 :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  have hUs : (U.extract (𝓃 - (0 + 1) * 𝓅) (𝓃 - 0 * 𝓅)).size = 𝓅 := by
    rw [ByteArray.size_extract, hU]
    omega
  have hMKb : ((traceMask geom (fun m => headerKeystream streamS geom
        (kemHopKeys kem kdfS (hops.extract (j + 1) hops.size)
          ((d.1.toArray.extract 0 hops.size).extract (j + 1)
            (d.1.toArray.extract 0 hops.size).size) m))
      (hops.size - (j + 1)) ((geom.nrHops - (hops.size - (j + 1))) * 𝓅)
      (hops.size - (j + 1))).extract ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅)
      ((geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅)).size = 𝓅 := by
    rw [ByteArray.size_extract, traceMask_size]
    omega
  rw [xorBytes_assoc _ _ _ (hP0.trans hUs.symm) (hUs.trans hMKb.symm),
    xorBytes_comm_of_size_eq _ _ (hUs.trans hMKb.symm),
    ← xorBytes_assoc _ _ _ (hP0.trans hMKb.symm) (hMKb.trans hUs.symm), hcan,
    zeroBytes_xorBytes_of_size _ _ (by rw [hUs]; omega)] at h1
  rw [show 2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅
      = 2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅
        + ((geom.nrHops - hops.size) * 𝓅 + j * 𝓅) by omega,
    show 2 + kem.ciphertextSize + geom.routingInfoLength
      = 2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅
        + ((geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅) by omega, h1]
  congr 1 <;> omega


/-! ## The padding of the hops in front -/

/-- The padding the hops before hop `j` leave at hop `j`: one block for each of the first `k`
of them, from their keystreams only. -/
def frontPadOf (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (j : ℕ) : ℕ → ByteArray
  | 0 => ByteArray.empty
  | k + 1 => frontPadOf hops seeds j k
      ++ tailPadOf geom (fun m => if k + m = j then zeroBytes 𝓃
          else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (k + m))) (j - k)

/-- **Before the end of the path, the keyed hop's padding is the padding of the hops in
front.** -/
theorem midPad_front (hvalid : geom.ValidForKEM kem) (hops : Array PathHop)
    (d : RSOR.Draw geom) (j : ℕ) (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (k : ℕ) (hk : k ≤ j) :
    (midPad geom kem kdfS streamS hops d j).extract ((geom.nrHops - hops.size) * 𝓅)
        ((geom.nrHops - hops.size) * 𝓅 + k * 𝓅)
      = frontPadOf geom kem kdfS streamS hops (d.1.toArray.extract 0 hops.size) j k := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hap : (geom.nrHops - hops.size) * 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm 𝓅]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hf : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)).size
      = (geom.nrHops - hops.size) * 𝓅 := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hseeds : (d.1.toArray.extract 0 hops.size).size = hops.size := by
    simp
    omega
  have hnm : (geom.nrHops - (hops.size - (j + 1))) * 𝓅
      = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hΦsz := fillerAtF_size kem kdfS streamS geom hrouting hops
    (d.1.toArray.extract 0 hops.size) _ j (zeroBytes 𝓃) hlen hf (zeroBytes_size _) (j + 1) hj
  rw [Nat.add_mul] at hΦsz
  induction k with
  | zero =>
    simp only [frontPadOf, Nat.zero_mul, Nat.add_zero]
    exact eq_empty_of_size_zero _ (by simp)
  | succ k ih =>
    have hk1 : (k + 1) * 𝓅 = k * 𝓅 + 𝓅 := Nat.succ_mul _ _
    have hkj : (k + 1) * 𝓅 ≤ (j + 1) * 𝓅 := Nat.mul_le_mul_right _ (by omega)
    have hWsz : (midPad geom kem kdfS streamS hops d j).size
        = (geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅 := by
      unfold midPad
      rw [size_xorBytes, hΦsz]
    rw [← extract_adjacent _ ((geom.nrHops - hops.size) * 𝓅)
      ((geom.nrHops - hops.size) * 𝓅 + k * 𝓅) ((geom.nrHops - hops.size) * 𝓅 + (k + 1) * 𝓅)
      (by omega) (by omega) (by omega), ih (by omega)]
    simp only [frontPadOf]
    congr 1
    unfold midPad
    rw [xorBytes_extract _ _ _ _ (by omega) (by rw [traceMask_size]; omega),
      fillerAtF_block geom kem kdfS streamS hrouting hops _ _ j _ (zeroBytes_size _) hlen hf
        (j + 1) k (by omega) hj]
    have h := tailPadOf_traceMask geom kem kdfS streamS hrouting hops
      (d.1.toArray.extract 0 hops.size) hseeds hlen j k (by omega) hj (hops.size - (j + 1))
      le_rfl
    rw [show hops.size - k - 1 - (hops.size - (j + 1)) = j - k by omega] at h
    exact h

/-- **At the end of the path, the keyed hop's padding is the padding of the hops in front.** -/
theorem zeroFiller_front (hrouting : geom.routingInfoLength
      = geom.perHopRoutingInfoLength * geom.nrHops)
    (hops : Array PathHop) (d : RSOR.Draw geom) (j : ℕ) (hj : j + 1 = hops.size)
    (hlen : hops.size ≤ geom.nrHops) (k : ℕ) (hk : k ≤ j) :
    (zeroFiller geom kem kdfS streamS hops d j).extract ((geom.nrHops - hops.size) * 𝓅)
        ((geom.nrHops - hops.size) * 𝓅 + k * 𝓅)
      = frontPadOf geom kem kdfS streamS hops (d.1.toArray.extract 0 hops.size) j k := by
  have hap : (geom.nrHops - hops.size) * 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm 𝓅]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hf : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)).size
      = (geom.nrHops - hops.size) * 𝓅 := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hsz := fillerAtF_size kem kdfS streamS geom hrouting hops
    (d.1.toArray.extract 0 hops.size) _ j (zeroBytes 𝓃) hlen hf (zeroBytes_size _) j (by omega)
  rw [Nat.add_mul] at hsz
  induction k with
  | zero =>
    simp only [frontPadOf, Nat.zero_mul, Nat.add_zero]
    exact eq_empty_of_size_zero _ (by simp)
  | succ k ih =>
    have hk1 : (k + 1) * 𝓅 = k * 𝓅 + 𝓅 := Nat.succ_mul _ _
    have hkj : (k + 1) * 𝓅 ≤ j * 𝓅 := Nat.mul_le_mul_right _ (by omega)
    rw [← extract_adjacent _ ((geom.nrHops - hops.size) * 𝓅)
      ((geom.nrHops - hops.size) * 𝓅 + k * 𝓅) ((geom.nrHops - hops.size) * 𝓅 + (k + 1) * 𝓅)
      (by omega) (by omega) (by unfold zeroFiller; omega), ih (by omega)]
    simp only [frontPadOf]
    congr 1
    unfold zeroFiller
    rw [fillerAtF_block geom kem kdfS streamS hrouting hops _ _ j _ (zeroBytes_size _) hlen hf
      j k (by omega) (by omega), show hops.size - k - 1 = j - k by omega]

/-- The padding of the hops in front reads their keys only. -/
theorem frontPadOf_congr (hops hops' : Array PathHop) (seeds seeds' : Array (Vector UInt8 32))
    (j : ℕ) (h : ∀ m, m < j → kemHopKeys kem kdfS hops seeds m = kemHopKeys kem kdfS hops' seeds' m)
    (k : ℕ) (hk : k ≤ j) :
    frontPadOf geom kem kdfS streamS hops seeds j k
      = frontPadOf geom kem kdfS streamS hops' seeds' j k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [frontPadOf, ih (by omega)]
    congr 1
    refine tailPadOf_congr geom _ _ _ fun m hm => ?_
    by_cases hkm : k + m = j
    · simp only [hkm, ↓reduceIte]
    · simp only [hkm, ↓reduceIte, h (k + m) (by omega)]

/-! ## The next layer's filler under other hops in front -/

/-- The keyed filler begins with the sender's filler. -/
theorem fillerAtF_head (hrouting : geom.routingInfoLength = 𝓅 * geom.nrHops)
    (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (j : ℕ)
    (U : ByteArray) (hU : U.size = 𝓃) (hlen : hops.size ≤ geom.nrHops)
    (hf : filler.size = (geom.nrHops - hops.size) * 𝓅) (i : ℕ) (hi : i ≤ hops.size) :
    (fillerAtF kem kdfS streamS geom hops seeds filler j U i).extract 0 filler.size = filler := by
  induction i with
  | zero => exact extract_all _ _ rfl
  | succ i ih =>
    rw [fillerAtF, tailFillerOf]
    split_ifs with hc
    · rw [Util.Bytes.extract_append_of_le _ _ (by
        rw [fillerAtF_size kem kdfS streamS geom hrouting hops seeds filler j U hlen hf hU i
          (by omega), hf]
        exact Nat.mul_le_mul_right _ (by omega))]
      exact ih (by omega)
    · have h0 : filler.size = 0 := by
        rw [hf, show geom.nrHops - hops.size = 0 by omega, Nat.zero_mul]
      rw [h0, eq_empty_of_size_zero filler h0]
      exact eq_empty_of_size_zero _ (by rw [ByteArray.size_extract]; omega)

/-- **Other hops in front shift the keyed hop's keystream.** The filler of the layer after the
keyed hop, built with other seeds, is the filler built with the given seeds once the tail of
the keyed hop's keystream is shifted by the difference of the two fillers at a zero
keystream. The head of the keystream is not read. -/
theorem fillerAtF_shift (hrouting : geom.routingInfoLength = 𝓅 * geom.nrHops)
    (hops : Array PathHop) (seeds seeds' : Array (Vector UInt8 32)) (filler : ByteArray) (j : ℕ)
    (U H : ByteArray) (hU : U.size = 𝓃) (hH : H.size = 𝓃 - (j + 1) * 𝓅)
    (hlen : hops.size ≤ geom.nrHops) (hj : j + 1 < hops.size)
    (hf : filler.size = (geom.nrHops - hops.size) * 𝓅) :
    fillerAtF kem kdfS streamS geom hops seeds' filler j
        (H ++ xorBytes (U.extract (𝓃 - (j + 1) * 𝓅) 𝓃)
          (xorBytes
            ((fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes 𝓃) (j + 1)).extract
              filler.size (filler.size + (j + 1) * 𝓅))
            ((fillerAtF kem kdfS streamS geom hops seeds' filler j (zeroBytes 𝓃) (j + 1)).extract
              filler.size (filler.size + (j + 1) * 𝓅)))) (j + 1)
      = fillerAtF kem kdfS streamS geom hops seeds filler j U (j + 1) := by
  have hm : (j + 1) * 𝓅 ≤ 𝓃 := by
    have h1 : (j + 1) * 𝓅 ≤ geom.nrHops * 𝓅 := Nat.mul_le_mul_right _ (by omega)
    rw [hrouting, Nat.mul_comm 𝓅]
    omega
  have hZsz : ∀ sd, (fillerAtF kem kdfS streamS geom hops sd filler j (zeroBytes 𝓃) (j + 1)).size
      = filler.size + (j + 1) * 𝓅 := fun sd => by
    rw [fillerAtF_size kem kdfS streamS geom hrouting hops sd filler j _ hlen hf
      (zeroBytes_size _) (j + 1) hj, hf, Nat.add_mul]
  have hZ : ∀ sd, fillerAtF kem kdfS streamS geom hops sd filler j (zeroBytes 𝓃) (j + 1)
      = filler ++ (fillerAtF kem kdfS streamS geom hops sd filler j (zeroBytes 𝓃)
        (j + 1)).extract filler.size (filler.size + (j + 1) * 𝓅) := fun sd => by
    have h := Util.Bytes.append_extract
      (fillerAtF kem kdfS streamS geom hops sd filler j (zeroBytes 𝓃) (j + 1)) filler.size
      (by rw [hZsz]; omega)
    rw [fillerAtF_head geom kem kdfS streamS hrouting hops sd filler j _ (zeroBytes_size _)
      hlen hf (j + 1) (by omega), hZsz] at h
    exact h.symm
  obtain ⟨Zt, hZt⟩ : ∃ Zt, Zt = (fillerAtF kem kdfS streamS geom hops seeds filler j
      (zeroBytes 𝓃) (j + 1)).extract filler.size (filler.size + (j + 1) * 𝓅) := ⟨_, rfl⟩
  obtain ⟨Zt', hZt'⟩ : ∃ Zt', Zt' = (fillerAtF kem kdfS streamS geom hops seeds' filler j
      (zeroBytes 𝓃) (j + 1)).extract filler.size (filler.size + (j + 1) * 𝓅) := ⟨_, rfl⟩
  have hZts : Zt.size = (j + 1) * 𝓅 := by
    rw [hZt, ByteArray.size_extract, hZsz]
    omega
  have hZts' : Zt'.size = (j + 1) * 𝓅 := by
    rw [hZt', ByteArray.size_extract, hZsz]
    omega
  have hUt : (U.extract (𝓃 - (j + 1) * 𝓅) 𝓃).size = (j + 1) * 𝓅 := by
    rw [ByteArray.size_extract, hU]
    omega
  rw [← hZt, ← hZt']
  have hV : (H
      ++ xorBytes (U.extract (𝓃 - (j + 1) * 𝓅) 𝓃) (xorBytes Zt Zt')).size = 𝓃 := by
    rw [ByteArray.size_append, size_xorBytes, hH, hUt]
    omega
  rw [fillerAtF_affine geom kem kdfS streamS hrouting hops seeds' filler j _ hV hlen (by omega)
      hf (j + 1) le_rfl,
    fillerAtF_affine geom kem kdfS streamS hrouting hops seeds filler j U hU hlen (by omega)
      hf (j + 1) le_rfl, Nat.sub_self, Nat.zero_mul, Nat.sub_zero,
    Util.Bytes.extract_append_of_ge _ _ (by rw [hH]), hH, Nat.sub_self,
    show 𝓃 - (𝓃 - (j + 1) * 𝓅) = (j + 1) * 𝓅 by omega,
    extract_all _ _ (by rw [size_xorBytes, hUt]), hZ seeds, hZ seeds', ← hZt, ← hZt',
    xorBytes_append filler Zt' _ _ (by rw [zeroBytes_size, hf]),
    xorBytes_append filler Zt _ _ (by rw [zeroBytes_size, hf]),
    xorBytes_comm_of_size_eq (U.extract (𝓃 - (j + 1) * 𝓅) 𝓃) (xorBytes Zt Zt')
      (by rw [size_xorBytes, hUt, hZts]),
    ← xorBytes_assoc Zt' (xorBytes Zt Zt') _ (by rw [size_xorBytes, hZts, hZts'])
      (by rw [size_xorBytes, hZts, hUt]),
    xorBytes_comm_of_size_eq Zt' (xorBytes Zt Zt') (by rw [size_xorBytes, hZts, hZts']),
    xorBytes_xorBytes]

/-! ## What a hop does with a masked header -/

/-- A hop's routing information after its keystream is taken off: the masked bytes, then the
tail of the keystream. -/
theorem xorBytes_unmask (X U : ByteArray) (hX : X.size = geom.routingInfoLength)
    (hU : U.size = 𝓃) :
    xorBytes (xorBytes X (U.extract 0 geom.routingInfoLength)
        ++ (⟨Array.replicate 𝓅 0⟩ : ByteArray)) U
      = X ++ U.extract geom.routingInfoLength 𝓃 := by
  have h : xorBytes (xorBytes X (U.extract 0 geom.routingInfoLength)
        ++ (⟨Array.replicate 𝓅 0⟩ : ByteArray))
      (U.extract 0 geom.routingInfoLength ++ U.extract geom.routingInfoLength U.size)
      = X ++ U.extract geom.routingInfoLength U.size := by
    rw [xorBytes_append _ _ _ _ (by
        rw [size_xorBytes, hX, ByteArray.size_extract, hU]
        omega),
      xorBytes_xorBytes,
      xorBytes_zero_left _ _ (by
        rw [ByteArray.size_extract, hU]
        omega)]
  rwa [Util.Bytes.append_extract U geom.routingInfoLength (by omega), hU] at h

/-- **A hop forwards a masked header.** Given its MAC key and keystream `U`, a hop whose
routing information is `X` under the head of `U`, with a valid tag, and whose `X` begins with
commands that name a next hop, forwards: the next ciphertext and the rest of `X`, then the tail
of `U`, the next hop's tag, and the decrypted payload it is given. -/
theorem procKeysD_forward (km : Vector UInt8 32) (U x pkt X : ByteArray)
    (hsz : pkt.size = 2 + kem.ciphertextSize + geom.routingInfoLength + macLength + x.size)
    (hx : 0 < x.size) (hver : pkt.extract 0 2 = v0AD)
    (hmac : pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
      = ofVector (macS.mac (ofVector km)
        (pkt.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength))))
    (hri : pkt.extract (2 + kem.ciphertextSize) (2 + kem.ciphertextSize + geom.routingInfoLength)
      = xorBytes X (U.extract 0 geom.routingInfoLength))
    (hX : X.size = geom.routingInfoLength) (hU : U.size = 𝓃)
    (hp : 𝓅 ≤ geom.routingInfoLength) (hct : kem.ciphertextSize ≤ 𝓅)
    (cmds : List RoutingCommand)
    (hparse : parseAll (X.extract 0 (𝓅 - kem.ciphertextSize)) = .ok cmds)
    (id : Vector UInt8 32) (m : Vector UInt8 32)
    (hnext : cmds.findSome? (fun
      | .nextNodeHop id m => some (id, m)
      | _ => none) = some (id, m)) :
    procKeysD kem macS geom km U x pkt
      = some (none, Cryptlib.Primitives.Hash.Sha512.sha512_256
          (pkt.extract 2 (2 + kem.ciphertextSize)), cmds,
        some (v0AD ++ ofVector (toVecN kem.ciphertextSize
            (X.extract (𝓅 - kem.ciphertextSize) 𝓅))
          ++ (X.extract 𝓅 geom.routingInfoLength ++ U.extract geom.routingInfoLength 𝓃)
          ++ ofVector m ++ x)) := by
  have hb := xorBytes_unmask geom X U hX hU
  unfold procKeysD unwrapKEMKeysD
  dsimp only
  have hUt : (U.extract geom.routingInfoLength 𝓃).size = 𝓅 := by
    rw [ByteArray.size_extract, hU]
    omega
  have he1 : (X ++ U.extract geom.routingInfoLength 𝓃).extract 0 (𝓅 - kem.ciphertextSize)
      = X.extract 0 (𝓅 - kem.ciphertextSize) :=
    Util.Bytes.extract_append_of_le _ _ (by omega)
  have he2 : (X ++ U.extract geom.routingInfoLength 𝓃).extract (𝓅 - kem.ciphertextSize) 𝓅
      = X.extract (𝓅 - kem.ciphertextSize) 𝓅 :=
    Util.Bytes.extract_append_of_le _ _ (by omega)
  have he3 : (X ++ U.extract geom.routingInfoLength 𝓃).extract 𝓅
        (X ++ U.extract geom.routingInfoLength 𝓃).size
      = X.extract 𝓅 geom.routingInfoLength ++ U.extract geom.routingInfoLength 𝓃 := by
    rw [ByteArray.size_append, ← hX]
    exact Util.Bytes.extract_append_ge _ _ (by omega)
  have hraw : (pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
      pkt.size).size = x.size := by
    rw [ByteArray.size_extract]
    omega
  have hlt : ¬ pkt.size < 2 + kem.ciphertextSize + geom.routingInfoLength + macLength := by omega
  simp only [hlt, ↓reduceDIte, hver, hraw.symm]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hmac, hri, hb, he1, he2, he3, hparse, hraw,
    hx]
  dsimp only [Bind.bind, Except.bind, pure, Except.pure]
  generalize hfs : List.findSome? _ cmds = o
  obtain rfl : o = some (id, m) := hfs.symm.trans hnext
  rfl

/-- **A hop at the end of a path, on a masked header.** Given its MAC key and keystream `U`, a
hop whose routing information is `X` under the head of `U`, with a valid tag, and whose `X`
begins with commands that name no next hop and carry no reply block, delivers the decrypted
payload it is given when that begins with the zero tag, and rejects the packet otherwise. -/
theorem procKeysD_last (km : Vector UInt8 32) (U x pkt X : ByteArray)
    (hsz : pkt.size = 2 + kem.ciphertextSize + geom.routingInfoLength + macLength + x.size)
    (hx : 0 < x.size) (hxt : geom.payloadTagLength ≤ x.size) (hver : pkt.extract 0 2 = v0AD)
    (hmac : pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
      = ofVector (macS.mac (ofVector km)
        (pkt.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength))))
    (hri : pkt.extract (2 + kem.ciphertextSize) (2 + kem.ciphertextSize + geom.routingInfoLength)
      = xorBytes X (U.extract 0 geom.routingInfoLength))
    (hX : X.size = geom.routingInfoLength) (hU : U.size = 𝓃)
    (hp : 𝓅 ≤ geom.routingInfoLength) (hct : kem.ciphertextSize ≤ 𝓅)
    (cmds : List RoutingCommand)
    (hparse : parseAll (X.extract 0 (𝓅 - kem.ciphertextSize)) = .ok cmds)
    (hnext : cmds.findSome? (fun
      | .nextNodeHop id m => some (id, m)
      | _ => none) = none)
    (hsurb : cmds.any (fun
      | .surbReply _ => true
      | _ => false) = false) :
    procKeysD kem macS geom km U x pkt
      = if (x.extract 0 geom.payloadTagLength).data.all (· == 0) then
          some (some (x.extract geom.payloadTagLength x.size),
            Cryptlib.Primitives.Hash.Sha512.sha512_256
              (pkt.extract 2 (2 + kem.ciphertextSize)), cmds, none)
        else none := by
  have hb := xorBytes_unmask geom X U hX hU
  unfold procKeysD unwrapKEMKeysD
  dsimp only
  have hUt : (U.extract geom.routingInfoLength 𝓃).size = 𝓅 := by
    rw [ByteArray.size_extract, hU]
    omega
  have he1 : (X ++ U.extract geom.routingInfoLength 𝓃).extract 0 (𝓅 - kem.ciphertextSize)
      = X.extract 0 (𝓅 - kem.ciphertextSize) :=
    Util.Bytes.extract_append_of_le _ _ (by omega)
  have he2 : (X ++ U.extract geom.routingInfoLength 𝓃).extract (𝓅 - kem.ciphertextSize) 𝓅
      = X.extract (𝓅 - kem.ciphertextSize) 𝓅 :=
    Util.Bytes.extract_append_of_le _ _ (by omega)
  have he3 : (X ++ U.extract geom.routingInfoLength 𝓃).extract 𝓅
        (X ++ U.extract geom.routingInfoLength 𝓃).size
      = X.extract 𝓅 geom.routingInfoLength ++ U.extract geom.routingInfoLength 𝓃 := by
    rw [ByteArray.size_append, ← hX]
    exact Util.Bytes.extract_append_ge _ _ (by omega)
  have hraw : (pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
      pkt.size).size = x.size := by
    rw [ByteArray.size_extract]
    omega
  have hlt : ¬ pkt.size < 2 + kem.ciphertextSize + geom.routingInfoLength + macLength := by omega
  simp only [hlt, ↓reduceDIte, hver, hraw.symm]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hmac, hri, hb, he1, he2, he3, hparse, hraw,
    hx]
  dsimp only [Bind.bind, Except.bind, pure, Except.pure]
  generalize hfs : List.findSome? _ cmds = o
  obtain rfl : o = none := hfs.symm.trans hnext
  dsimp only
  simp only [show ¬ x.size < geom.payloadTagLength by omega, ↓reduceIte]
  generalize hsr : List.any cmds _ = sr
  obtain rfl : sr = false := hsr.symm.trans hsurb
  by_cases ht : ((x.extract 0 geom.payloadTagLength).data.all fun a => a == 0) = true
  · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [ht, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    rfl

/-! ## The honest relay's answer to its own header -/

/-- A built packet begins with the packet version. -/
theorem newKEMPacket_version (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload pkt : ByteArray)
    (h : newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload = .ok pkt) :
    pkt.extract 0 2 = v0AD := by
  obtain ⟨-, hdr0, sprp0, _t0, hcreate0, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ h
  obtain ⟨hpos, hgen, hseeds, hfsize, ke, keys, _rks, _rp, _s, hkn, hkeys, -, -, hkc, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ _ _ hcreate0
  rw [newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom seeds filler path
    payload ke keys hpos hgen hseeds hfsize hkn hkeys hkc] at h
  obtain ⟨-, hdr, sprp, t, hcreate, -, -, hpkt⟩ :=
    newKEMPacketFrom_unfold kem cipher macS streamS geom _ _ _ _ _ _ h
  obtain ⟨s, -, hhdr, -⟩ := createKEMHeaderFrom_hdrTrace kem geom macS streamS ke keys filler
    path hdr sprp hcreate
  rw [hpkt, hhdr, ByteArray.append_assoc, ByteArray.append_assoc, ByteArray.append_assoc]
  exact Util.Bytes.extract_append_left v0AD _

set_option maxHeartbeats 1000000 in
/-- **The keyed hop forwards the next layer, for any keystream.** Before the end of the path,
given its MAC key, any keystream `U` and any decrypted payload `x`, the hop takes its own
header with a valid tag to the header of the next layer with the payload `x`. -/
theorem procKeysD_relayFront (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U fwd : ByteArray) (km : Vector UInt8 32) (x y : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hc : c.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd)
    (hs : (relayFront kem cipher macS kdfS streamS geom hops d payload j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hx : 0 < x.size) (hxy : y.size = x.size)
    (hcmdnn : ∀ k ∈ (hops[j]!).commands, k ≠ RoutingCommand.null)
    (hcmdnh : ∀ k ∈ (hops[j]!).commands, ∀ id m, k ≠ RoutingCommand.nextNodeHop id m) :
    procKeysD kem macS geom km U x
        (relayFront kem cipher macS kdfS streamS geom hops d payload j c U
          ++ ofVector (macS.mac (ofVector km)
            (relayFront kem cipher macS kdfS streamS geom hops d payload j c U))
          ++ y)
      = some (none, Cryptlib.Primitives.Hash.Sha512.sha512_256 c,
          (hops[j]!).commands ++ [RoutingCommand.nextNodeHop (hops[j + 1]!).id
            (toVec32 (fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
              (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)))],
          some (fwd.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
            ++ x)) := by
  obtain ⟨hnnh, hperhopEq, hrouting, hhdr, hpacket, -⟩ := id hvalid
  have hnnpos : 0 < Constants.nextNodeHopLength := by decide
  have hfwd' : newKEMPacket kem cipher macS kdfS streamS geom
      ((d.1.toArray.extract 0 hops.size).extract (j + 1) (d.1.toArray.extract 0 hops.size).size)
      (fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
        ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j U (j + 1))
      (hops.extract (j + 1) hops.size) payload = .ok fwd := hfwd
  have hfsz : fwd.size = geom.packetLength :=
    newKEMPacket_size kem cipher macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hfwd'
      (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hfwd').1
  have hver := newKEMPacket_version geom kem kdfS streamS cipher macS _ _ _ _ _ hfwd'
  have hlast := layerPast_lastBlock geom kem kdfS streamS cipher macS hvalid hops d payload j U
    fwd hj hlen hU hfwd
  have had : adLength = 2 := rfl
  have hmL : macLength = 32 := rfl
  have hpR : 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting]
    exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨M, hM⟩ : ∃ M, M = relayFront kem cipher macS kdfS streamS geom hops d payload j c U :=
    ⟨_, rfl⟩
  rw [← hM] at hs ⊢
  unfold relayFront at hM
  rw [hfwd] at hM
  dsimp only at hM
  have hv0 : v0AD.size = 2 := rfl
  have hE : (fwd.extract (2 + kem.ciphertextSize)
      (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅)).size
      = geom.routingInfoLength - 𝓅 := by
    rw [ByteArray.size_extract]
    omega
  have hpsz : (hops.extract j hops.size).size = hops.size - j := by simp
  cases hfr : kemRiFragment kem geom (hops.extract j hops.size)
      #[ByteArray.empty, fwd.extract 2 (2 + kem.ciphertextSize)]
      (fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength))
      (hops.extract j hops.size).size 0 with
  | error e =>
    rw [hfr] at hM
    rw [hM] at hs
    simp only [ByteArray.size_append, size_xorBytes, hE, hc, hv0] at hs
    have : ByteArray.empty.size = 0 := rfl
    omega
  | ok frag =>
    rw [hfr] at hM
    dsimp only at hM
    have hke1 : (Array.replicate (hops.size - j) (fwd.extract 2 (2 + kem.ciphertextSize)))[1]!
        = fwd.extract 2 (2 + kem.ciphertextSize) := by
      rw [getElem!_pos _ 1 (by simp; omega)]
      simp
    have hfr' : kemRiFragment kem geom (hops.extract j hops.size)
        (Array.replicate (hops.size - j) (fwd.extract 2 (2 + kem.ciphertextSize)))
        (fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
          (2 + kem.ciphertextSize + geom.routingInfoLength + macLength))
        (hops.extract j hops.size).size 0 = .ok frag := by
      rw [kemRiFragment_zero_congr, hke1]
      exact hfr
    have hksz : ∀ i (hi : i < (Array.replicate (hops.size - j)
          (fwd.extract 2 (2 + kem.ciphertextSize))).size),
        ((Array.replicate (hops.size - j) (fwd.extract 2 (2 + kem.ciphertextSize)))[i]'hi).size
          = kem.ciphertextSize := fun i hi => by
      simp only [Array.getElem_replicate, ByteArray.size_extract]
      omega
    have h0 : (hops.extract j hops.size)[0]! = hops[j]! := by
      have := getElem!_extract_from hops j 0 (by omega)
      rwa [Nat.add_zero] at this
    have h1 : (hops.extract j hops.size)[0 + 1]! = hops[j + 1]! :=
      getElem!_extract_from hops j 1 (by omega)
    have hfsz' := kemRiFragment_size kem geom _ _ _ _ 0 (by omega) (by omega) hnnh
      (by simp) hksz frag hfr'
    obtain ⟨hpar, hnc⟩ := kemRiFragment_content_nonterminal kem geom _ _ _ _ 0 (by omega)
      (by omega) (by omega) hnnh (by simp) hksz (by rw [h0]; exact hcmdnn) frag hfr'
    rw [h0, h1] at hpar
    rw [hke1] at hnc
    obtain ⟨X, hX⟩ : ∃ X, X = frag ++ fwd.extract (2 + kem.ciphertextSize)
        (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅) := ⟨_, rfl⟩
    rw [← hX] at hM
    have hXsz : X.size = geom.routingInfoLength := by
      rw [hX, ByteArray.size_append, hfsz', hE]
      omega
    obtain ⟨T, hT⟩ : ∃ T, T = ofVector (macS.mac (ofVector km) M) := ⟨_, rfl⟩
    rw [← hT]
    have hTsz : T.size = macLength := by
      rw [hT, Util.Bytes.size_ofVector, hmactag]
    obtain ⟨p1, p2, -⟩ := three_parts M T y
    rw [hs] at p1 p2
    rw [hTsz] at p2
    have hpre : ∀ a b, b ≤ 2 + kem.ciphertextSize + geom.routingInfoLength →
        (M ++ T ++ y).extract a b = M.extract a b := fun a b hb => by
      rw [Util.Bytes.extract_append_of_le _ _ (by rw [ByteArray.size_append]; omega),
        Util.Bytes.extract_append_of_le _ _ (by omega)]
    have hMc : M.extract 2 (2 + kem.ciphertextSize) = c := by
      rw [hM, Util.Bytes.extract_append_of_le _ _ (by rw [ByteArray.size_append]; omega)]
      have := Util.Bytes.extract_append_right v0AD c
      rwa [hc] at this
    have hMr : M.extract (2 + kem.ciphertextSize) (2 + kem.ciphertextSize + geom.routingInfoLength)
        = xorBytes X (U.extract 0 geom.routingInfoLength) := by
      rw [hM, Util.Bytes.extract_append_of_ge _ _ (by rw [ByteArray.size_append]; omega),
        ByteArray.size_append, hc, hv0, Nat.sub_self,
        show 2 + kem.ciphertextSize + geom.routingInfoLength - (2 + kem.ciphertextSize)
          = geom.routingInfoLength by omega]
      exact extract_all _ _ (by rw [size_xorBytes, hXsz])
    have hMv : M.extract 0 2 = v0AD := by
      rw [hM, ByteArray.append_assoc]
      exact Util.Bytes.extract_append_left v0AD _
    have hn1 : (hops[j]!).commands.findSome? (fun
        | .nextNodeHop id m => some (id, m)
        | _ => none) = none := by
      rw [List.findSome?_eq_none_iff]
      intro k hk
      cases k <;> first | rfl | exact absurd rfl (hcmdnh _ hk _ _)
    rw [procKeysD_forward geom kem macS km U x (M ++ T ++ y) X
      (by simp only [ByteArray.size_append, hs, hTsz, hxy])
      hx ((hpre 0 2 (by omega)).trans hMv)
      (by rw [p2, p1, hT])
      ((hpre _ _ le_rfl).trans hMr) hXsz hU hpR (by omega) _
      (by
        rw [hX, Util.Bytes.extract_append_of_le _ _ (by omega)]
        exact hpar)
      (hops[j + 1]!).id (toVec32 (fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)))
      (by simp [List.findSome?_append, hn1])]
    have hXa : X.extract (𝓅 - kem.ciphertextSize) 𝓅 = fwd.extract 2 (2 + kem.ciphertextSize) := by
      rw [hX, Util.Bytes.extract_append_of_le _ _ (by omega)]
      exact hnc
    have hXb : X.extract 𝓅 geom.routingInfoLength = fwd.extract (2 + kem.ciphertextSize)
        (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅) := by
      rw [hX, Util.Bytes.extract_append_of_ge _ _ (by omega), hfsz', Nat.sub_self]
      exact extract_all _ _ (by rw [hE])
    rw [hpre 2 _ (by omega), hMc, hXa, hXb, ← hlast,
      ofVector_toVecN _ (by rw [ByteArray.size_extract]; omega),
      ofVector_toVec32 _ (by rw [ByteArray.size_extract]; omega), ← hver,
      extract_split fwd (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength) (by omega) (by omega),
      extract_split fwd (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅)
        (2 + kem.ciphertextSize + geom.routingInfoLength) (by omega) (by omega),
      extract_split fwd (2 + kem.ciphertextSize)
        (2 + kem.ciphertextSize + geom.routingInfoLength - 𝓅) (by omega) (by omega),
      extract_split fwd 2 (2 + kem.ciphertextSize) (by omega) (by omega)]
    simp only [ByteArray.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **The keyed hop at the end of the path, for any keystream.** Given its MAC key, any
keystream `U` and any decrypted payload `x`, the last hop on its own header with a valid tag
delivers `x` behind the zero tag when `x` begins with it, and rejects the packet otherwise. -/
theorem procKeysD_relayFrontLast (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength) (hops : Array PathHop) (d : RSOR.Draw geom) (j : ℕ)
    (c U : ByteArray) (km : Vector UInt8 32) (x y : ByteArray)
    (hj : j + 1 = hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hc : c.size = kem.ciphertextSize)
    (hs : (relayFrontLast kem kdfS streamS geom hops d j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hx : 0 < x.size) (hxt : geom.payloadTagLength ≤ x.size) (hxy : y.size = x.size)
    (hcmdnn : ∀ k ∈ (hops[j]!).commands, k ≠ RoutingCommand.null)
    (hnext : (hops[j]!).commands.findSome? (fun
      | .nextNodeHop id m => some (id, m)
      | _ => none) = none)
    (hsurb : (hops[j]!).commands.any (fun
      | .surbReply _ => true
      | _ => false) = false) :
    procKeysD kem macS geom km U x
        (relayFrontLast kem kdfS streamS geom hops d j c U
          ++ ofVector (macS.mac (ofVector km) (relayFrontLast kem kdfS streamS geom hops d j c U))
          ++ y)
      = if (x.extract 0 geom.payloadTagLength).data.all (· == 0) then
          some (some (x.extract geom.payloadTagLength x.size),
            Cryptlib.Primitives.Hash.Sha512.sha512_256 c, (hops[j]!).commands, none)
        else none := by
  obtain ⟨hnnh, hperhopEq, hrouting, -⟩ := id hvalid
  have hnnpos : 0 < Constants.nextNodeHopLength := by decide
  have hv0 : v0AD.size = 2 := rfl
  have hpR : 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting]
    exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨M, hM⟩ : ∃ M, M = relayFrontLast kem kdfS streamS geom hops d j c U := ⟨_, rfl⟩
  rw [← hM] at hs ⊢
  unfold relayFrontLast at hM
  rw [show 𝓃 - (0 + 1) * 𝓅 = geom.routingInfoLength by omega] at hM
  obtain ⟨F, hF⟩ : ∃ F, F = (if geom.nrHops > 1 then fillerAtF kem kdfS streamS geom hops
      (d.1.toArray.extract 0 hops.size)
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j U j
    else ByteArray.empty) := ⟨_, rfl⟩
  rw [← hF] at hM
  cases hfr : kemRiFragment kem geom #[hops[j]!] #[c] ByteArray.empty 1 0 with
  | error e =>
    rw [hfr] at hM
    exfalso
    have hFsz : F.size + 𝓅 ≤ geom.routingInfoLength := by
      rw [hF]
      split_ifs with hn
      · have hap : (geom.nrHops - hops.size) * 𝓅 ≤ geom.routingInfoLength := by
          rw [hrouting, Nat.mul_comm 𝓅]
          exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        rw [fillerAtF_size kem kdfS streamS geom hrouting hops _ _ j U hlen (by
            rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
            omega) hU j (by omega), hrouting, Nat.mul_comm 𝓅, ← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (by omega)
      · simpa using hpR
    rw [hM] at hs
    simp only [ByteArray.size_append, size_xorBytes, hc, hv0] at hs
    have : ByteArray.empty.size = 0 := rfl
    omega
  | ok frag =>
    rw [hfr] at hM
    dsimp only at hM
    have hksz : ∀ i (hi : i < (#[c] : Array ByteArray).size),
        ((#[c] : Array ByteArray)[i]'hi).size = kem.ciphertextSize := fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      exact hc
    have hfsz' := kemRiFragment_size kem geom #[hops[j]!] #[c] ByteArray.empty 1 0
      Nat.one_pos (by omega) hnnh rfl hksz frag hfr
    obtain ⟨hpar, -⟩ := kemRiFragment_content_terminal kem geom #[hops[j]!] #[c]
      ByteArray.empty 1 0 Nat.one_pos rfl (by omega) hcmdnn frag hfr
    obtain ⟨X, hX⟩ : ∃ X, X = frag ++ F := ⟨_, rfl⟩
    rw [← hX] at hM
    have hXsz : X.size = geom.routingInfoLength := by
      rw [hM] at hs
      simp only [ByteArray.size_append, size_xorBytes, hc, hv0] at hs
      omega
    obtain ⟨T, hT⟩ : ∃ T, T = ofVector (macS.mac (ofVector km) M) := ⟨_, rfl⟩
    rw [← hT]
    have hTsz : T.size = macLength := by
      rw [hT, Util.Bytes.size_ofVector, hmactag]
    obtain ⟨p1, p2, -⟩ := three_parts M T y
    rw [hs] at p1 p2
    rw [hTsz] at p2
    have hpre : ∀ a b, b ≤ 2 + kem.ciphertextSize + geom.routingInfoLength →
        (M ++ T ++ y).extract a b = M.extract a b := fun a b hb => by
      rw [Util.Bytes.extract_append_of_le _ _ (by rw [ByteArray.size_append]; omega),
        Util.Bytes.extract_append_of_le _ _ (by omega)]
    have hMc : M.extract 2 (2 + kem.ciphertextSize) = c := by
      rw [hM, Util.Bytes.extract_append_of_le _ _ (by rw [ByteArray.size_append]; omega)]
      have := Util.Bytes.extract_append_right v0AD c
      rwa [hc] at this
    have hMr : M.extract (2 + kem.ciphertextSize) (2 + kem.ciphertextSize + geom.routingInfoLength)
        = xorBytes X (U.extract 0 geom.routingInfoLength) := by
      rw [hM, Util.Bytes.extract_append_of_ge _ _ (by rw [ByteArray.size_append]; omega),
        ByteArray.size_append, hc, hv0, Nat.sub_self,
        show 2 + kem.ciphertextSize + geom.routingInfoLength - (2 + kem.ciphertextSize)
          = geom.routingInfoLength by omega]
      exact extract_all _ _ (by rw [size_xorBytes, hXsz])
    have hMv : M.extract 0 2 = v0AD := by
      rw [hM, ByteArray.append_assoc]
      exact Util.Bytes.extract_append_left v0AD _
    rw [procKeysD_last geom kem macS km U x (M ++ T ++ y) X
      (by simp only [ByteArray.size_append, hs, hTsz, hxy])
      hx hxt ((hpre 0 2 (by omega)).trans hMv)
      (by rw [p2, p1, hT])
      ((hpre _ _ le_rfl).trans hMr) hXsz hU hpR (by omega) _
      (by
        rw [hX, Util.Bytes.extract_append_of_le _ _ (by omega)]
        exact hpar)
      hnext hsurb, hpre 2 _ (by omega), hMc]

/-- **The next layer under other hops in front.** The layer after the keyed hop, built from
another draw with the same seeds after the keyed hop and the same filler, is the layer built
from the given draw once the tail of the keyed hop's keystream is shifted. -/
theorem layerPast_shift (hrouting : geom.routingInfoLength = 𝓅 * geom.nrHops)
    (hops : Array PathHop) (d d' : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (U H : ByteArray) (hU : U.size = 𝓃) (hH : H.size = 𝓃 - (j + 1) * 𝓅)
    (hlen : hops.size ≤ geom.nrHops) (hj : j + 1 < hops.size) (h2 : d'.2 = d.2)
    (hs : (d'.1.toArray.extract 0 hops.size).extract (j + 1) (d'.1.toArray.extract 0 hops.size).size
      = (d.1.toArray.extract 0 hops.size).extract (j + 1) (d.1.toArray.extract 0 hops.size).size) :
    layerPast kem cipher macS kdfS streamS geom hops d' payload j
        (H ++ xorBytes (U.extract (𝓃 - (j + 1) * 𝓅) 𝓃)
          (xorBytes
            ((fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
              ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j (zeroBytes 𝓃)
              (j + 1)).extract ((geom.nrHops - hops.size) * 𝓅)
                ((geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅))
            ((fillerAtF kem kdfS streamS geom hops (d'.1.toArray.extract 0 hops.size)
              ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)) j (zeroBytes 𝓃)
              (j + 1)).extract ((geom.nrHops - hops.size) * 𝓅)
                ((geom.nrHops - hops.size) * 𝓅 + (j + 1) * 𝓅)))) (j + 1)
      = layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) := by
  have hf : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * 𝓅)).size
      = (geom.nrHops - hops.size) * 𝓅 := by
    have hap : (geom.nrHops - hops.size) * 𝓅 ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm 𝓅]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have h := fillerAtF_shift geom kem kdfS streamS hrouting hops
    (d.1.toArray.extract 0 hops.size) (d'.1.toArray.extract 0 hops.size) _ j U H hU hH hlen hj hf
  rw [hf] at h
  unfold layerPast
  dsimp only
  rw [h2, hs, h]

/-! ## The layers in front of the keyed hop -/

omit kdfS streamS cipher macS in
/-- The first hop's routing fragment reads the first hop, the second hop's name, and whether
the path ends. -/
theorem kemRiFragment_path_congr (path path' : Array PathHop) (ke : Array ByteArray)
    (mac : ByteArray) (n n' : ℕ) (h0 : path[0]! = path'[0]!)
    (h1 : (path[1]!).id = (path'[1]!).id)
    (hn : (0 == n - 1) = (0 == n' - 1)) :
    kemRiFragment kem geom path ke mac n 0 = kemRiFragment kem geom path' ke mac n' 0 := by
  unfold kemRiFragment
  simp only [h0, h1, hn, Nat.zero_add]

/-- **The layers in front read the hops in front.** Wrapping a layer in the layers of hops
`i` to `i + n` gives the same bytes on two paths with two draws that agree on those hops, on
the name of the hop after each, and on their seeds. -/
theorem wrapUp_congr (hops hops' : Array PathHop) (d d' : RSOR.Draw geom)
    (hlen : hops.size ≤ geom.nrHops) (hlen' : hops'.size ≤ geom.nrHops) (i n : ℕ)
    (L : ByteArray)
    (h : ∀ k, i ≤ k → k < i + n → k + 1 < hops.size ∧ k + 1 < hops'.size
      ∧ hops[k]! = hops'[k]! ∧ (hops[k + 1]!).id = (hops'[k + 1]!).id
      ∧ d.1.toArray[k]! = d'.1.toArray[k]!) :
    wrapUp kem cipher macS kdfS streamS geom hops d i n L
      = wrapUp kem cipher macS kdfS streamS geom hops' d' i n L := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hk, hk', e0, e1, es⟩ := h i le_rfl (by omega)
    have hS : (d.1.toArray.extract 0 hops.size).size = hops.size := by simp; omega
    have hS' : (d'.1.toArray.extract 0 hops'.size).size = hops'.size := by simp; omega
    have p0 : (hops.extract i hops.size)[0]! = (hops'.extract i hops'.size)[0]! := by
      rw [getElem!_extract_from hops i 0 (by omega), getElem!_extract_from hops' i 0 (by omega)]
      exact e0
    have p1 : ((hops.extract i hops.size)[1]!).id = ((hops'.extract i hops'.size)[1]!).id := by
      rw [getElem!_extract_from hops i 1 (by omega), getElem!_extract_from hops' i 1 (by omega)]
      exact e1
    have s0 : ((d.1.toArray.extract 0 hops.size).extract i
          (d.1.toArray.extract 0 hops.size).size)[0]!
        = ((d'.1.toArray.extract 0 hops'.size).extract i
          (d'.1.toArray.extract 0 hops'.size).size)[0]! := by
      have hx : ∀ (a : Array (Vector UInt8 32)) (m : ℕ), i < m → m ≤ a.size →
          (a.extract 0 m)[i + 0]! = a[i]! := fun a m h1 h2 => by
        rw [Nat.add_zero, getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
        simp
      rw [getElem!_extract_from _ i 0 (by omega), getElem!_extract_from _ i 0 (by omega),
        hx _ _ (by omega) (by simp; omega), hx _ _ (by omega) (by simp; omega)]
      exact es
    unfold wrapUp
    rw [ih (i + 1) fun k hk1 hk2 => h k (by omega) (by omega)]
    unfold wrapHop kemHopCt kemHopKeys
    rw [p0, s0, kemRiFragment_path_congr geom kem _ (hops'.extract i hops'.size) _ _ _
      (hops'.extract i hops'.size).size p0 p1 (by simp; omega)]

/-! ## The same header in both worlds -/

/-- A mask shifted by the difference of two strings takes one to the other's masking. -/
theorem xorBytes_shift (X X' M : ByteArray) (h : X.size = X'.size) (hM : M.size = X.size) :
    xorBytes X (xorBytes M (xorBytes X' X)) = xorBytes X' M := by
  rw [xorBytes_comm_of_size_eq M (xorBytes X' X) (by rw [size_xorBytes, hM, h]),
    ← xorBytes_assoc X (xorBytes X' X) M (by rw [size_xorBytes, h])
      (by rw [size_xorBytes, hM, h]),
    xorBytes_comm_of_size_eq X (xorBytes X' X) (by rw [size_xorBytes, h]), xorBytes_xorBytes]

set_option maxHeartbeats 1000000 in
/-- **A middle hop's header is a last hop's header under a shifted keystream.** The keyed hop's
header bytes on a path that goes on, with the head of its keystream shifted by the difference
of the two routing informations, are its header bytes on a path that ends at it with the same
hop keys in front. -/
theorem relayFront_eq_last (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops hops' : Array PathHop) (d d' : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U T fwd : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops) (hj' : j + 1 = hops'.size)
    (hU : U.size = 𝓃) (hT : T.size = (j + 1) * 𝓅) (hc : c.size = kem.ciphertextSize)
    (hkeys : ∀ m, m < j → kemHopKeys kem kdfS hops (d.1.toArray.extract 0 hops.size) m
      = kemHopKeys kem kdfS hops' (d'.1.toArray.extract 0 hops'.size) m)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j
      (xorBytes (U.extract 0 (geom.routingInfoLength - j * 𝓅))
          (xorBytes
            (lastFrag geom kem hops' j c
              ++ (zeroFiller geom kem kdfS streamS hops' d' j).extract 0
                ((geom.nrHops - hops'.size) * 𝓅))
            (midFrag geom kem hops j fwd
              ++ fwd.extract (2 + kem.ciphertextSize)
                (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)
              ++ (midPad geom kem kdfS streamS hops d j).extract 0
                ((geom.nrHops - hops.size) * 𝓅)))
        ++ T) (j + 1) = .ok fwd)
    (hs : (relayFront kem cipher macS kdfS streamS geom hops d payload j c
      (xorBytes (U.extract 0 (geom.routingInfoLength - j * 𝓅))
          (xorBytes
            (lastFrag geom kem hops' j c
              ++ (zeroFiller geom kem kdfS streamS hops' d' j).extract 0
                ((geom.nrHops - hops'.size) * 𝓅))
            (midFrag geom kem hops j fwd
              ++ fwd.extract (2 + kem.ciphertextSize)
                (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)
              ++ (midPad geom kem kdfS streamS hops d j).extract 0
                ((geom.nrHops - hops.size) * 𝓅)))
        ++ T)).size = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hs' : (relayFrontLast kem kdfS streamS geom hops' d' j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    relayFront kem cipher macS kdfS streamS geom hops d payload j c
      (xorBytes (U.extract 0 (geom.routingInfoLength - j * 𝓅))
          (xorBytes
            (lastFrag geom kem hops' j c
              ++ (zeroFiller geom kem kdfS streamS hops' d' j).extract 0
                ((geom.nrHops - hops'.size) * 𝓅))
            (midFrag geom kem hops j fwd
              ++ fwd.extract (2 + kem.ciphertextSize)
                (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)
              ++ (midPad geom kem kdfS streamS hops d j).extract 0
                ((geom.nrHops - hops.size) * 𝓅)))
        ++ T)
      = relayFrontLast kem kdfS streamS geom hops' d' j c U := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  obtain ⟨X1, hX1⟩ : ∃ X1, X1 = lastFrag geom kem hops' j c
      ++ (zeroFiller geom kem kdfS streamS hops' d' j).extract 0
        ((geom.nrHops - hops'.size) * 𝓅) := ⟨_, rfl⟩
  obtain ⟨X0, hX0⟩ : ∃ X0, X0 = midFrag geom kem hops j fwd
      ++ fwd.extract (2 + kem.ciphertextSize)
        (2 + kem.ciphertextSize + (hops.size - (j + 1)) * 𝓅)
      ++ (midPad geom kem kdfS streamS hops d j).extract 0
        ((geom.nrHops - hops.size) * 𝓅) := ⟨_, rfl⟩
  rw [← hX1, ← hX0] at hfwd hs ⊢
  obtain ⟨V, hV⟩ : ∃ V, V = xorBytes (U.extract 0 (geom.routingInfoLength - j * 𝓅))
      (xorBytes X1 X0) ++ T := ⟨_, rfl⟩
  rw [← hV] at hfwd hs ⊢
  have hjp : j * 𝓅 + 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm 𝓅, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hUh : (U.extract 0 (geom.routingInfoLength - j * 𝓅)).size
      = geom.routingInfoLength - j * 𝓅 := by
    rw [ByteArray.size_extract, hU]
    omega
  have hVs : V.size = 𝓃 := by
    rw [hV, ByteArray.size_append, size_xorBytes, hUh, hT, Nat.succ_mul]
    omega
  have h0 := relayFront_canon geom kem kdfS streamS cipher macS hvalid hmactag hops d payload j
    c V fwd hj hlen hVs hc hfwd hs
  have h1 := relayFrontLast_canon geom kem kdfS streamS hrouting hops' d' j c U hj' (by omega)
    hU hc hs'
  rw [← hX0] at h0
  rw [← hX1] at h1
  have hv0 : v0AD.size = 2 := rfl
  have hap : (geom.nrHops - hops'.size) * 𝓅 ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm 𝓅]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hzs : (zeroFiller geom kem kdfS streamS hops' d' j).size
      = (geom.nrHops - hops'.size) * 𝓅 + j * 𝓅 := by
    unfold zeroFiller
    rw [fillerAtF_size kem kdfS streamS geom hrouting hops' _ _ j _ (by omega) (by
        rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
        omega) (zeroBytes_size _) j (by omega), Nat.add_mul]
  have hp1 := zeroFiller_front geom kem kdfS streamS hrouting hops' d' j hj' (by omega) j le_rfl
  have hp0 := midPad_front geom kem kdfS streamS hvalid hops d j hj hlen j le_rfl
  rw [hzs, hp1] at h1
  rw [hp0, frontPadOf_congr geom kem kdfS streamS hops hops' _ _ j hkeys j le_rfl] at h0
  have hFP : (frontPadOf geom kem kdfS streamS hops' (d'.1.toArray.extract 0 hops'.size) j
      j).size = j * 𝓅 := by
    rw [← hp1, ByteArray.size_extract, hzs]
    omega
  have hX1s : X1.size = geom.routingInfoLength - j * 𝓅 := by
    rw [h1] at hs'
    simp only [ByteArray.size_append, size_xorBytes, hc, hv0, hFP] at hs'
    omega
  have hX0s : X0.size = geom.routingInfoLength - j * 𝓅 := by
    rw [h0] at hs
    simp only [ByteArray.size_append, size_xorBytes, hc, hv0, hFP] at hs
    omega
  rw [h0, h1, hV, Util.Bytes.extract_append_of_le _ _ (by rw [size_xorBytes, hUh]),
    extract_all _ _ (by rw [size_xorBytes, hUh]),
    xorBytes_shift X0 X1 _ (hX0s.trans hX1s.symm) (hUh.trans hX0s.symm)]

/-! ## The honest relay's answers as steps of the game -/

/-- **The keyed hop's step before the end of the path.** On its own header with a valid tag
and any payload, with any keystream and any decryption `x` of the payload, a hop with no
commands of its own forwards the next layer's header with `x` to the next hop. -/
theorem stepOf_relayFront (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U fwd : ByteArray) (km : Vector UInt8 32)
    (x y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hc : c.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd)
    (hs : (relayFront kem cipher macS kdfS streamS geom hops d payload j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength)
    (hcmd : (hops[j]!).commands = []) :
    RSOR.stepOf geom (procKeysD kem macS geom km U (ofVector x)
        (RSOR.join (Util.Bytes.toVecN geom.headerLength
          (relayFront kem cipher macS kdfS streamS geom hops d payload j c U
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem cipher macS kdfS streamS geom hops d payload j c U))), y)))
      = some (.forward (hops[j + 1]!).id (RSOR.split geom
          (fwd.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
            ++ ofVector x))) := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  unfold RSOR.join
  dsimp only
  rw [Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hs, Util.Bytes.size_ofVector, hmactag, hhdr, had]),
    procKeysD_relayFront geom kem kdfS streamS cipher macS hvalid hmactag hops d payload j c U
      fwd km (ofVector x) (ofVector y) hj hlen hU hc hfwd hs
      (by rw [Util.Bytes.size_ofVector]; exact hx)
      (by rw [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector])
      (by rw [hcmd]; simp) (by rw [hcmd]; simp), hcmd]
  rfl

/-- Before the end of the path the keyed hop does not reply. -/
theorem replyOf_relayFront (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U fwd : ByteArray) (km : Vector UInt8 32)
    (x y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hc : c.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd)
    (hs : (relayFront kem cipher macS kdfS streamS geom hops d payload j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength)
    (hcmd : (hops[j]!).commands = []) (m : RSOR.Msg geom) :
    RSOR.replyOf cipher geom m (procKeysD kem macS geom km U (ofVector x)
        (RSOR.join (Util.Bytes.toVecN geom.headerLength
          (relayFront kem cipher macS kdfS streamS geom hops d payload j c U
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem cipher macS kdfS streamS geom hops d payload j c U))), y)))
      = none := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  unfold RSOR.join
  dsimp only
  rw [Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hs, Util.Bytes.size_ofVector, hmactag, hhdr, had]),
    procKeysD_relayFront geom kem kdfS streamS cipher macS hvalid hmactag hops d payload j c U
      fwd km (ofVector x) (ofVector y) hj hlen hU hc hfwd hs
      (by rw [Util.Bytes.size_ofVector]; exact hx)
      (by rw [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector])
      (by rw [hcmd]; simp) (by rw [hcmd]; simp)]
  rfl

/-- **The keyed hop's step at the end of the path.** On its own header with a valid tag and
any payload, with any keystream and any decryption `x` of the payload, the last hop delivers
what is behind the zero tag of `x` to its recipient, and nothing when `x` has no zero tag. -/
theorem stepOf_relayFrontLast (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength) (hops : Array PathHop) (d : RSOR.Draw geom) (j : ℕ)
    (c U : ByteArray) (km : Vector UInt8 32)
    (x y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : j + 1 = hops.size) (hlen : hops.size ≤ geom.nrHops) (hU : U.size = 𝓃)
    (hc : c.size = kem.ciphertextSize)
    (hs : (relayFrontLast kem kdfS streamS geom hops d j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength)
    (rc : Vector UInt8 32) (hcmd : (hops[j]!).commands = [.recipient rc]) :
    RSOR.stepOf geom (procKeysD kem macS geom km U (ofVector x)
        (RSOR.join (Util.Bytes.toVecN geom.headerLength
          (relayFrontLast kem kdfS streamS geom hops d j c U
            ++ ofVector (macS.mac (ofVector km)
              (relayFrontLast kem kdfS streamS geom hops d j c U))), y)))
      = if ((ofVector x).extract 0 geom.payloadTagLength).data.all (· == 0) then
          some (.deliver (RSOR.msgOf geom
            ((ofVector x).extract geom.payloadTagLength (ofVector x).size)) rc)
        else none := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  unfold RSOR.join
  dsimp only
  rw [Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hs, Util.Bytes.size_ofVector, hmactag, hhdr, had]),
    procKeysD_relayFrontLast geom kem kdfS streamS macS hvalid hmactag hops d j c U km
      (ofVector x) (ofVector y) hj hlen hU hc hs
      (by rw [Util.Bytes.size_ofVector]; exact hx)
      (by rw [Util.Bytes.size_ofVector]; omega)
      (by rw [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector])
      (by rw [hcmd]; simp) (by rw [hcmd]; rfl) (by rw [hcmd]; rfl), hcmd]
  split_ifs <;> rfl

end Pad

end Cryptlib.Protocols.Sphinx.KEMSphinx
