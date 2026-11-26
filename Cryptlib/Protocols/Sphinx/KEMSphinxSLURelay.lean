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

/-- A draw whose seeds after position `j` and whose padding are another draw's. -/
def joinDraw (d d' : RSOR.Draw geom) (j : ℕ) : RSOR.Draw geom :=
  (Vector.ofFn fun i : Fin geom.nrHops =>
    if i.val ≤ j then d.1[i.val]'i.isLt else d'.1[i.val - (j + 1)]'(by have := i.isLt; omega),
    d'.2)

omit kem kdfS streamS cipher macS in
/-- The seeds of a joined draw after position `j` are the other draw's first seeds. -/
theorem joinDraw_extract_after (d d' : RSOR.Draw geom) (j n : ℕ) (hn : n ≤ geom.nrHops) :
    ((joinDraw geom d d' j).1.toArray.extract 0 n).extract (j + 1)
        ((joinDraw geom d d' j).1.toArray.extract 0 n).size
      = d'.1.toArray.extract 0 (n - (j + 1)) := by
  apply Array.ext
  · simp
    omega
  · intro i h1 h2
    have hi : j + 1 + i < n := by
      simp at h1
      omega
    simp [joinDraw, show ¬ (j + 1 + i ≤ j) by omega]

omit streamS cipher macS in
/-- The keys of the hops up to position `j` under a joined draw are the first draw's, whatever
the last hop's commands. -/
theorem kemHopKeys_joinDraw (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last last' : List RoutingCommand) (d d' : RSOR.Draw geom) (j m : ℕ) (hm : m ≤ j)
    (hj : j < R.hops.length) :
    kemHopKeys kem kdfS (RSOR.path kem R last)
        ((joinDraw geom d d' j).1.toArray.extract 0 (RSOR.path kem R last).size) m
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
def backShift (hops hops' : Array PathHop) (d0 d : RSOR.Draw geom) (j : ℕ)
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
    ++ (xorBytes ((ofVector d0.2).extract ((geom.nrHops - hops.size) *
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
    (d dS : RSOR.Draw geom) (payload : ByteArray) (j : ℕ) (c U fwd fwd' : ByteArray)
    (hj : j + 1 < R.hops.length) (hU : U.size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) (hc : c.size = kem.ciphertextSize)
    (hfwd' : layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last') d payload j U (j +
        1) = .ok fwd')
    (hfwd : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) dS
        payload 0 = .ok fwd) :
    (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw geom
        d dS j) d j U fwd fwd').size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)
    ∧ relayFront kem cipher macS kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j)
        payload j c
        (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw
            geom d dS j) d j U fwd fwd')
      = relayFront kem cipher macS kdfS streamS geom (RSOR.path kem R last') d payload j c U
    ∧ ∀ i, j + 1 + i ≤ R.hops.length →
      layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j)
          payload j
          (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw
              geom d dS j) d j U fwd fwd') (j + 1 + i)
        = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) dS
            payload i := by
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
  have hf : ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R
      last).size) * geom.perHopRoutingInfoLength)).size = ((geom.nrHops - (RSOR.path kem R
      last).size) * geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hT : ((ofVector (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem R
      last).size) * geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength)).size
      = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hseeds := joinDraw_extract_after geom d dS j (RSOR.path kem R last).size hlen0
  rw [show (RSOR.path kem R last).size - (j + 1) = (RSOR.path kem (R.drop (j + 1)) last).size by rw
      [hszS, hsz0]] at hseeds
  have hfill : ∀ H : ByteArray, H.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) -
      (j + 1) * geom.perHopRoutingInfoLength →
      fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j
        (H ++ (xorBytes ((ofVector (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem
            R last).size) * geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j).2).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).size + (j
            + 1) * geom.perHopRoutingInfoLength)))) (j + 1)
      = (ofVector dS.2).extract 0 ((geom.nrHops - (RSOR.path kem (R.drop (j + 1)) last).size) *
          geom.perHopRoutingInfoLength) := fun H hH => by
    rw [fillerAtF_target kem geom kdfS streamS hrouting _ _ _ j H _ hH hT hlen0 hj0 hf, ← hpadS]
    exact extract_adjacent _ 0 _ _ (Nat.zero_le _) (Nat.le_add_right _ _)
      (by rw [Util.Bytes.size_ofVector]; exact hpad)
  have hdrop := fun (H : ByteArray) (hH : H.size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) =>
    layerPast_drop kem geom kdfS streamS cipher macS R last (joinDraw geom d dS j) dS payload j
      (H ++ (xorBytes ((ofVector (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem R
          last).size) * geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size)
          * geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j).2).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).size + (j
            + 1) * geom.perHopRoutingInfoLength)))) hseeds (hfill H hH)
  have hZ : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)).size =
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength := by
    rw [zeroBytes_size, Nat.succ_mul]
    rw [Nat.succ_mul] at hjp
    omega
  have hTs : (xorBytes ((ofVector (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem
      R last).size) * geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j).2).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).size + (j
            + 1) * geom.perHopRoutingInfoLength))).size = (j + 1) * geom.perHopRoutingInfoLength :=
            by
    rw [size_xorBytes, hT]
  have hU1 : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes
      ((ofVector (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j).2).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).size + (j
            + 1) * geom.perHopRoutingInfoLength)))).size = (geom.routingInfoLength +
            geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_append, hZ, hTs]
    omega
  have hcmd : ∀ l : List RoutingCommand, ((RSOR.path kem R l)[j]!).commands = [] := fun l => by
    rw [RSOR.path_getElem! kem R l j (by omega), ite_eq_right (by omega)]
  have htail : (midPad geom kem kdfS streamS (RSOR.path kem R last) (joinDraw geom d dS j)
      j).extract ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)
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
      (fun m hm => kemHopKeys_joinDraw kem geom kdfS R last last' d dS j m (by omega) (by omega))
      j le_rfl
  have hs := relayFront_headShift kem geom kdfS streamS cipher macS hvalid hmactag (RSOR.path kem R
      last)
    (RSOR.path kem R last') (joinDraw geom d dS j) d payload j c
    (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes ((ofVector
        (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
        geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j).2).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).size + (j
            + 1) * geom.perHopRoutingInfoLength)))) U fwd fwd' hj0 hlen0 (hsz1.trans hsz0.symm) hU1
            hU hc
    (hcmd last) (hcmd last') ((hdrop _ hZ 0 (by omega)).trans hfwd) hfwd' htail
  have ht : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes
      ((ofVector (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j).2).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).size + (j
            + 1) * geom.perHopRoutingInfoLength)))).extract (geom.routingInfoLength - j *
            geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      = (xorBytes ((ofVector (joinDraw geom d dS j).2).extract ((geom.nrHops - (RSOR.path kem R
          last).size) * geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size)
          * geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS
          j).1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size)
            * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j).2).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).size + (j
            + 1) * geom.perHopRoutingInfoLength))) := by
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
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R last) (joinDraw geom d dS j) j).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)))).size =
            (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
            geom.perHopRoutingInfoLength := by
    have h := hs.1
    rw [ByteArray.size_append, hTs] at h
    omega
  exact ⟨hs.1, hs.2.2, hdrop _ hHs⟩

end RestOfPath

end Cryptlib.Protocols.Sphinx.KEMSphinx
