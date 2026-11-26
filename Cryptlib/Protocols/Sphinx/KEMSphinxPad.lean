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
  rw [hm, if_pos (by omega), haff, ← hΦ, ← hMK,
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

end Pad

end Cryptlib.Protocols.Sphinx.KEMSphinx
