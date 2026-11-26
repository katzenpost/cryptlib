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

end Pad

end Cryptlib.Protocols.Sphinx.KEMSphinx
