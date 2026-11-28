/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUSwap

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Common (commandsToBytes zeroPadTo toVec32 xorBytes)
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult relayImpl keysKs keysTag keysEnc)
open Cryptlib.Protocols.Sphinx.Common (v0AD)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # A header over a path, from a hop on, as a header over the rest of the path

The layers of a header from hop `j + 1` on are the layers of a header over the rest of the
path, whose filler is the long header's filler followed by the front of its padding. -/

section Shift

variable (geom : Geometry)

open Cryptlib.Protocols.Sphinx.KEMSphinx (padAt)

omit geom in
theorem extract_append_mid (a b : ByteArray) (lo hi : ℕ) (h1 : lo ≤ a.size)
    (h2 : hi = a.size + b.size) : (a ++ b).extract lo hi = a.extract lo a.size ++ b := by
  subst h2
  exact Util.Bytes.extract_append_ge a b h1

/-- **The padding after a later hop, past the first `j + 1` hops' length, is the padding of
the hops from `j + 1` on by themselves.** -/
theorem padAt_drop (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (j m : ℕ)
    (hm : (j + 1 + m + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) :
    (padAt geom ks (j + 1 + m)).extract ((j + 1) * geom.perHopRoutingInfoLength) ((j + 1 + m + 1) *
        geom.perHopRoutingInfoLength)
      = padAt geom (fun i => ks (j + 1 + i)) m := by
  induction m with
  | zero =>
    have e0 : (j + 1 + 0 + 1) * geom.perHopRoutingInfoLength = (j + 1) *
        geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have e1 : (0 + 1) * geom.perHopRoutingInfoLength = geom.perHopRoutingInfoLength := by rw
        [Nat.zero_add, Nat.one_mul]
    have e2 : (j + 1 + 1) * geom.perHopRoutingInfoLength = (j + 1) * geom.perHopRoutingInfoLength +
        geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have hs : (padAt geom ks j).size = (j + 1) * geom.perHopRoutingInfoLength :=
      padAt_size geom ks hks j (by omega)
    have hk := hks (j + 1)
    show (padAt geom ks (j + 1)).extract _ _ = (ks (j + 1 + 0)).extract _ _
    rw [padAt, Util.Bytes.extract_append_of_ge _ _ (by
      rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract,
        ByteArray.size_extract, hs, hk]
      omega)]
    simp only [ByteArray.extract_extract, ByteArray.size_extract,
      Cryptlib.Protocols.Sphinx.Common.size_xorBytes, hs, hk]
    congr 1 <;> omega
  | succ m ih =>
    have ea : (j + 1 + (m + 1) + 1) * geom.perHopRoutingInfoLength = (j + 1 + m + 1) *
        geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have eb : (j + 1 + m + 1) * geom.perHopRoutingInfoLength = (j + 1) *
        geom.perHopRoutingInfoLength + (m + 1) * geom.perHopRoutingInfoLength := by
      rw [show j + 1 + m + 1 = (j + 1) + (m + 1) by omega, Nat.add_mul]
    have ec : (m + 1 + 1) * geom.perHopRoutingInfoLength = (m + 1) * geom.perHopRoutingInfoLength +
        geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have ed : (j + 1 + m + 1 + 1) * geom.perHopRoutingInfoLength = (j + 1 + m + 1) *
        geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have ee : (j + 1 + (m + 1) + 1) * geom.perHopRoutingInfoLength = (j + 1 + m + 1 + 1) *
        geom.perHopRoutingInfoLength := rfl
    have hm' : (j + 1 + m + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := by omega
    have hs : (padAt geom ks (j + 1 + m)).size = (j + 1 + m + 1) * geom.perHopRoutingInfoLength :=
      padAt_size geom ks hks (j + 1 + m) (by omega)
    have hs' : (padAt geom (fun i => ks (j + 1 + i)) m).size = (m + 1) *
        geom.perHopRoutingInfoLength :=
      padAt_size geom (fun i => ks (j + 1 + i)) (fun k => hks _) m (by omega)
    have hk : (ks (j + 1 + m + 1)).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)
        := hks _
    have hk2 : (ks (j + 1 + (m + 1))).size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := hks _
    have ih' := ih hm'
    show (padAt geom ks (j + 1 + m + 1)).extract _ _ = padAt geom (fun i => ks (j + 1 + i)) (m + 1)
    rw [padAt, padAt, extract_append_mid _ _ _ _ (by
        rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract,
          ByteArray.size_extract, hs, hk]
        omega) (by
        rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract, hs, hk]
        omega),
      Cryptlib.Protocols.Sphinx.Common.size_xorBytes,
      KEMSphinx.xorBytes_extract _ _ _ _ (le_refl _) (by
        rw [ByteArray.size_extract, ByteArray.size_extract, hs, hk]
        omega)]
    simp only [ByteArray.extract_extract, ByteArray.size_extract, hs, hs', hk]
    refine congrArg₂ (· ++ ·) (congrArg₂ xorBytes ?_ ?_) ?_
    · congr 1 <;> omega
    · rw [← ih']
      congr 1
      omega
    · congr 1 <;> omega

/-- The front of the padding after hop `i`: its first `j + 1` hops' length. -/
def frontPad (ks : ℕ → ByteArray) (j i : ℕ) : ByteArray :=
  (padAt geom ks i).extract 0 ((j + 1) * geom.perHopRoutingInfoLength)

/-- **The front of the padding after a hop** is the front of the padding after the hop before,
masked by that many bytes of the hop's keystream from where its tail begins. -/
theorem frontPad_succ (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (j i : ℕ)
    (hi : j ≤ i) (hb : (i + 1 + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) :
    frontPad geom ks j (i + 1)
      = xorBytes ((ks (i + 1)).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
          (i + 1 + 1) * geom.perHopRoutingInfoLength)
          ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1 + 1) *
              geom.perHopRoutingInfoLength + (j + 1) * geom.perHopRoutingInfoLength))
        (frontPad geom ks j i) := by
  have e1 : (i + 1 + 1) * geom.perHopRoutingInfoLength = (i + 1) * geom.perHopRoutingInfoLength +
      geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  have e2 : (j + 1) * geom.perHopRoutingInfoLength ≤ (i + 1) * geom.perHopRoutingInfoLength :=
      Nat.mul_le_mul_right _ (by omega)
  have hs : (padAt geom ks i).size = (i + 1) * geom.perHopRoutingInfoLength := padAt_size geom ks
      hks i (by omega)
  have hk := hks (i + 1)
  unfold frontPad
  rw [padAt, Util.Bytes.extract_append_of_le _ _ (by
      rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract,
        ByteArray.size_extract, hs, hk]
      omega),
    KEMSphinx.xorBytes_extract _ _ _ _ (by
      rw [ByteArray.size_extract, ByteArray.size_extract, hs, hk]
      omega) (by
      rw [hs]
      exact e2)]
  simp only [ByteArray.extract_extract, hs]
  congr 1
  congr 1
  omega

/-- So masking it again gives back the front of the padding after the hop before. -/
theorem frontPad_unmask (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (j i : ℕ)
    (hi : j ≤ i) (hb : (i + 1 + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) :
    xorBytes (frontPad geom ks j (i + 1)) ((ks (i + 1)).extract ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (i + 1 + 1) * geom.perHopRoutingInfoLength)
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1 + 1) *
            geom.perHopRoutingInfoLength + (j + 1) * geom.perHopRoutingInfoLength))
      = frontPad geom ks j i := by
  have e1 : (i + 1 + 1) * geom.perHopRoutingInfoLength = (i + 1) * geom.perHopRoutingInfoLength +
      geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  have e2 : (j + 1) * geom.perHopRoutingInfoLength ≤ (i + 1) * geom.perHopRoutingInfoLength :=
      Nat.mul_le_mul_right _ (by omega)
  have hs : (padAt geom ks i).size = (i + 1) * geom.perHopRoutingInfoLength := padAt_size geom ks
      hks i (by omega)
  have hsz : ((ks (i + 1)).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i +
      1 + 1) * geom.perHopRoutingInfoLength)
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1 + 1) *
          geom.perHopRoutingInfoLength + (j + 1) * geom.perHopRoutingInfoLength)).size = (frontPad
          geom ks j i).size := by
    unfold frontPad
    rw [ByteArray.size_extract, ByteArray.size_extract, hs, hks]
    omega
  rw [frontPad_succ geom ks hks j i hi hb,
    Cryptlib.Protocols.Sphinx.Common.xorBytes_comm_of_size_eq _ _ hsz]
  exact Cryptlib.Protocols.Sphinx.Common.xorBytes_xorBytes _ _

omit geom in
/-- A mask over two parts is a mask over each. -/
theorem xorBytes_split (X Q K : ByteArray) (a q : ℕ) (hX : X.size = a) (hK : a + q ≤ K.size) :
    xorBytes (X ++ Q) (K.extract 0 (a + q))
      = xorBytes X (K.extract 0 a) ++ xorBytes Q (K.extract a (a + q)) := by
  have hsplit : K.extract 0 (a + q) = K.extract 0 a ++ K.extract a (a + q) := by
    apply ByteArray.ext_getElem
    · simp only [ByteArray.size_append, ByteArray.size_extract]
      omega
    · intro i h1 h2
      simp only [ByteArray.size_extract] at h1
      rw [ByteArray.getElem_extract]
      by_cases hi : i < a
      · rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_extract]; omega),
          ByteArray.getElem_extract]
      · rw [ByteArray.getElem_append_right (by simp only [ByteArray.size_extract]; omega),
          ByteArray.getElem_extract]
        simp only [ByteArray.size_extract]
        congr 1
        omega
  rw [hsplit]
  exact KEMSphinx.xorBytes_append _ _ _ _ (by
    rw [hX, ByteArray.size_extract]
    omega)

end Shift

end Cryptlib.Protocols.Sphinx.NIKESphinx
