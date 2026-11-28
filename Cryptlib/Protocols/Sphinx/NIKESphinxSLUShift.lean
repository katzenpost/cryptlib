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
/-- A stretch of bytes is its first part and the rest. -/
theorem extract_split (K : ByteArray) (a q : ℕ) (hK : a + q ≤ K.size) :
    K.extract 0 (a + q) = K.extract 0 a ++ K.extract a (a + q) := by
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

omit geom in
/-- A mask over two parts is a mask over each. -/
theorem xorBytes_split (X Q K : ByteArray) (a q : ℕ) (hX : X.size = a) (hK : a + q ≤ K.size) :
    xorBytes (X ++ Q) (K.extract 0 (a + q))
      = xorBytes X (K.extract 0 a) ++ xorBytes Q (K.extract a (a + q)) := by
  rw [extract_split K a q hK]
  exact KEMSphinx.xorBytes_append _ _ _ _ (by
    rw [hX, ByteArray.size_extract]
    omega)

/-- **One step of a header over the rest of a path.** At hop `j + r + 1` of the long path,
which is hop `r` of the rest: masking the routing information with the front of the padding
behind it by the hop's longer stretch of keystream gives the long header's routing
information with the front of the padding of the hop before; and that front, followed by the
rest's own padding, is the long header's padding. -/
theorem drop_step (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (j r : ℕ)
    (X : ByteArray) (hb : (j + r + 1 + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength
        + geom.perHopRoutingInfoLength))
    (hX : X.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + r + 1 + 1) *
        geom.perHopRoutingInfoLength) :
    xorBytes (X ++ frontPad geom ks j (j + r + 1))
        ((ks (j + r + 1)).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (r +
            1) * geom.perHopRoutingInfoLength))
      = xorBytes X ((ks (j + r + 1)).extract 0 ((geom.routingInfoLength +
          geom.perHopRoutingInfoLength) - (j + r + 1 + 1) * geom.perHopRoutingInfoLength))
        ++ frontPad geom ks j (j + r)
    ∧ frontPad geom ks j (j + r)
        ++ (if r > 0 then padAt geom (fun i => ks (j + 1 + i)) (r - 1) else ByteArray.empty)
      = padAt geom ks (j + r) := by
  have e1 : (j + r + 1 + 1) * geom.perHopRoutingInfoLength = (r + 1) * geom.perHopRoutingInfoLength
      + (j + 1) * geom.perHopRoutingInfoLength := by
    rw [show j + r + 1 + 1 = (r + 1) + (j + 1) by omega, Nat.add_mul]
  have e2 : (j + r + 1 + 1) * geom.perHopRoutingInfoLength = (j + r + 1) *
      geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  have hs : (padAt geom ks (j + r)).size = (j + r + 1) * geom.perHopRoutingInfoLength :=
    padAt_size geom ks hks (j + r) (by omega)
  have hk := hks (j + r + 1)
  refine ⟨?_, ?_⟩
  · rw [show (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (r + 1) *
      geom.perHopRoutingInfoLength = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j
      + r + 1 + 1) * geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength by
      omega,
      xorBytes_split X _ _ _ _ hX (by rw [hk]; omega),
      frontPad_unmask geom ks hks j (j + r) (Nat.le_add_right j r) hb]
  · unfold frontPad
    cases r with
    | zero =>
      rw [ite_eq_right (lt_irrefl 0), ByteArray.append_empty]
      exact KEMSphinx.extract_all _ _ hs
    | succ m =>
      have e3 : (j + (m + 1) + 1) * geom.perHopRoutingInfoLength = (j + 1) *
          geom.perHopRoutingInfoLength + (m + 1) * geom.perHopRoutingInfoLength := by
        rw [show j + (m + 1) + 1 = (j + 1) + (m + 1) by omega, Nat.add_mul]
      have hd := padAt_drop geom ks hks j m (by
        rw [show j + 1 + m + 1 = j + (m + 1) + 1 by omega]
        omega)
      rw [show j + 1 + m = j + (m + 1) by omega, e3] at hd
      rw [ite_eq_left (Nat.succ_pos m), Nat.add_sub_cancel, ← hd,
        ← extract_split _ _ _ (by rw [hs]; omega)]
      exact KEMSphinx.extract_all _ _ (by rw [hs]; omega)

/-- **A hop's fragment on the rest of a path is its fragment on the path.** -/
theorem nikeFragment_drop (path path' : Array PathHop) (j : ℕ)
    (hsz : path'.size + (j + 1) = path.size) (mac : ByteArray) (r : ℕ) (hr : r < path'.size)
    (hc : path'[r]!.commands = path[j + r + 1]!.commands)
    (hid : r + 1 < path'.size → path'[r + 1]!.id = path[j + r + 1 + 1]!.id) :
    nikeFragment geom path' mac r = nikeFragment geom path mac (j + r + 1) := by
  have hb : (r == path'.size - 1) = (j + r + 1 == path.size - 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    omega
  unfold nikeFragment
  rw [hb, hc]
  cases hbb : (j + r + 1 == path.size - 1) with
  | true => rfl
  | false =>
    have hne := beq_eq_false_iff_ne.mp hbb
    rw [hid (by omega)]

set_option maxHeartbeats 1000000 in
/-- **A header over the rest of a path.** Built from the last hop back, the header over the
hops after hop `j`, with the long filler followed by the front of the padding as its filler,
has at each step the long header's routing information followed by the front of the padding
that far, and the long header's tag. -/
theorem nikeHdrTrace_drop (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path path' : Array PathHop) (j : ℕ)
    (hsz : path'.size + (j + 1) = path.size) (hn : path.size ≤ geom.nrHops)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (htag : ∀ i
        m, (tag i m).size = macLength)
    (hc : ∀ m, m < path'.size → path'[m]!.commands = path[j + m + 1]!.commands)
    (hid : ∀ m, m + 1 < path'.size → path'[m + 1]!.id = path[j + m + 1 + 1]!.id)
    (t : ℕ) (ht : t ≤ path'.size) :
    nikeHdrTrace geom (fun m => ks (j + m + 1)) (fun m => tag (j + m + 1))
        (fun m => ge (j + m + 1)) (fil ++ frontPad geom ks j (path.size - 1)) path' t
      = (nikeHdrTrace geom ks tag ge fil path t).map
        (fun s => (s.1 ++ frontPad geom ks j (path.size - 1 - t), s.2)) := by
  induction t with
  | zero =>
    have hgt : geom.nrHops > path'.size := by omega
    have hfe : (if geom.nrHops > path.size then fil else ByteArray.empty) = fil := by
      by_cases h : geom.nrHops > path.size
      · exact ite_eq_left h
      · rw [ite_eq_right h]
        have h0 : fil.size = 0 := by
          rw [hfill, show geom.nrHops - path.size = 0 by omega, Nat.zero_mul]
        exact (ByteArray.ext (Array.eq_empty_of_size_eq_zero h0)).symm
    show some ((if geom.nrHops > path'.size then _ else ByteArray.empty), ByteArray.empty)
      = Option.map _ (some ((if geom.nrHops > path.size then fil else ByteArray.empty),
        ByteArray.empty))
    rw [ite_eq_left hgt, hfe]
    rfl
  | succ t ih =>
    obtain ⟨k, hk⟩ : ∃ k, geom.nrHops = path.size + k := ⟨geom.nrHops - path.size, by omega⟩
    obtain ⟨r, hr⟩ : ∃ r, path'.size = t + 1 + r := ⟨path'.size - (t + 1), by omega⟩
    have hps : path.size = t + 1 + r + (j + 1) := by omega
    have hi : path.size - 1 - t = j + r + 1 := by omega
    have hm : path'.size - 1 - t = r := by omega
    have hi1 : path.size - 1 - (t + 1) = j + r := by omega
    have f1 : geom.perHopRoutingInfoLength + (k + t) * geom.perHopRoutingInfoLength + (j + r + 1 +
        1) * geom.perHopRoutingInfoLength = (geom.routingInfoLength + geom.perHopRoutingInfoLength)
        := by
      rw [hrouting, hk, hps]
      ring
    have hb : (j + r + 1 + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := by omega
    have hfm : ∀ m : ℕ, (fun m => ks (j + m + 1)) m = ks (j + m + 1) := fun _ => rfl
    have hpad : padAt geom (fun m => ks (j + m + 1)) = padAt geom (fun i => ks (j + 1 + i)) :=
      congrArg (padAt geom) (funext fun m => by rw [Nat.add_right_comm])
    rw [nikeHdrTrace, nikeHdrTrace, ih (by omega)]
    cases hl : nikeHdrTrace geom ks tag ge fil path t with
    | none => rfl
    | some s =>
      have hs1 := (nikeHdrTrace_size geom ks tag ge fil path hnnh hle hfill htag t s hl).1
      rw [show geom.nrHops - path.size = k by omega] at hs1
      have hfr := nikeFragment_drop geom path path' j hsz s.2 r (by omega)
        (hc r (by omega)) (fun h => hid r h)
      simp only [Option.map_some, hi, hm, hi1, hfr, hpad]
      cases hf : nikeFragment geom path s.2 (j + r + 1) with
      | error e => rfl
      | ok frag =>
        have hfs := nikeFragment_size geom path s.2 (j + r + 1) hnnh hle frag hf
        have hX : (frag ++ s.1).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j
            + r + 1 + 1) * geom.perHopRoutingInfoLength := by
          rw [ByteArray.size_append, hfs, hs1]
          omega
        obtain ⟨d1, d2⟩ := drop_step geom ks hks j r (frag ++ s.1) hb hX
        rw [ByteArray.append_assoc] at d1
        simp only [Option.map_some, d1, ite_eq_left (Nat.succ_pos (j + r)), Nat.add_sub_cancel]
        refine congrArg some (Prod.ext rfl ?_)
        show tag (j + r + 1) _ = tag (j + r + 1) _
        rw [← ByteArray.append_assoc (c := frontPad geom ks j (j + r)),
          ByteArray.append_assoc (b := frontPad geom ks j (j + r)), d2]

set_option maxHeartbeats 1000000 in
/-- **The bytes under a hop's tag in a header over the rest of a path** are those under its
tag in the long header. -/
theorem hdrMsg_drop (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path path' : Array PathHop) (j : ℕ)
    (hsz : path'.size + (j + 1) = path.size) (hn : path.size ≤ geom.nrHops)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (htag : ∀ i
        m, (tag i m).size = macLength)
    (hc : ∀ m, m < path'.size → path'[m]!.commands = path[j + m + 1]!.commands)
    (hid : ∀ m, m + 1 < path'.size → path'[m + 1]!.id = path[j + m + 1 + 1]!.id)
    (r : ℕ) (hr : r < path'.size) :
    hdrMsg geom (fun m => ks (j + m + 1)) (fun m => tag (j + m + 1))
        (fun m => ge (j + m + 1)) (fil ++ frontPad geom ks j (path.size - 1)) path' r
      = hdrMsg geom ks tag ge fil path (j + r + 1) := by
  obtain ⟨k, hk⟩ : ∃ k, geom.nrHops = path.size + k := ⟨geom.nrHops - path.size, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, path'.size = t + 1 + r := ⟨path'.size - (r + 1), by omega⟩
  have hps : path.size = t + 1 + r + (j + 1) := by omega
  have hi : path.size - 1 - t = j + r + 1 := by omega
  have ht1 : path'.size - 1 - r = t := by omega
  have ht2 : path.size - 1 - (j + r + 1) = t := by omega
  have f1 : geom.perHopRoutingInfoLength + (k + t) * geom.perHopRoutingInfoLength + (j + r + 1 + 1)
      * geom.perHopRoutingInfoLength = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := by
    rw [hrouting, hk, hps]
    ring
  have hb : (j + r + 1 + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := by omega
  have hpad : padAt geom (fun m => ks (j + m + 1)) = padAt geom (fun i => ks (j + 1 + i)) :=
    congrArg (padAt geom) (funext fun m => by rw [Nat.add_right_comm])
  unfold hdrMsg
  rw [ht1, ht2, nikeHdrTrace_drop geom ks tag ge fil path path' j hsz hn hnnh hle hrouting hfill
      hks htag hc hid t (by omega)]
  cases hl : nikeHdrTrace geom ks tag ge fil path t with
  | none => rfl
  | some s =>
    have hs1 := (nikeHdrTrace_size geom ks tag ge fil path hnnh hle hfill htag t s hl).1
    rw [show geom.nrHops - path.size = k by omega] at hs1
    have hfr := nikeFragment_drop geom path path' j hsz s.2 r hr (hc r hr) (fun h => hid r h)
    simp only [Option.map_some, hi, hfr, hpad]
    cases hf : nikeFragment geom path s.2 (j + r + 1) with
    | error e => rfl
    | ok frag =>
      have hfs := nikeFragment_size geom path s.2 (j + r + 1) hnnh hle frag hf
      have hX : (frag ++ s.1).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j +
          r + 1 + 1) * geom.perHopRoutingInfoLength := by
        rw [ByteArray.size_append, hfs, hs1]
        omega
      obtain ⟨d1, d2⟩ := drop_step geom ks hks j r (frag ++ s.1) hb hX
      rw [ByteArray.append_assoc] at d1
      simp only [d1, ite_eq_left (Nat.succ_pos (j + r)), Nat.add_sub_cancel]
      rw [← ByteArray.append_assoc (c := frontPad geom ks j (j + r)),
        ByteArray.append_assoc (b := frontPad geom ks j (j + r)), d2]

/-- **The header of a layer of a header over the rest of a path** is the header of that layer
of the long header. -/
theorem layerHdr_drop (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path path' : Array PathHop) (j : ℕ)
    (hsz : path'.size + (j + 1) = path.size) (hn : path.size ≤ geom.nrHops)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (htag : ∀ i
        m, (tag i m).size = macLength)
    (hc : ∀ m, m < path'.size → path'[m]!.commands = path[j + m + 1]!.commands)
    (hid : ∀ m, m + 1 < path'.size → path'[m + 1]!.id = path[j + m + 1 + 1]!.id)
    (r : ℕ) (hr : r < path'.size) :
    layerHdr geom (fun m => ks (j + m + 1)) (fun m => tag (j + m + 1))
        (fun m => ge (j + m + 1)) (fil ++ frontPad geom ks j (path.size - 1)) path' r
      = layerHdr geom ks tag ge fil path (j + r + 1) := by
  unfold layerHdr
  rw [hdrMsg_drop geom ks tag ge fil path path' j hsz hn hnnh hle hrouting hfill hks htag hc hid r
      hr]

/-- **A header over the rest of a path builds when the long header builds.** -/
theorem nikeHdrTrace_drop_isSome (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path path' : Array PathHop) (j : ℕ)
    (hsz : path'.size + (j + 1) = path.size) (hn : path.size ≤ geom.nrHops)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (htag : ∀ i
        m, (tag i m).size = macLength)
    (hc : ∀ m, m < path'.size → path'[m]!.commands = path[j + m + 1]!.commands)
    (hid : ∀ m, m + 1 < path'.size → path'[m + 1]!.id = path[j + m + 1 + 1]!.id)
    (h : (nikeHdrTrace geom ks tag ge fil path path.size).isSome) :
    (nikeHdrTrace geom (fun m => ks (j + m + 1)) (fun m => tag (j + m + 1))
        (fun m => ge (j + m + 1)) (fil ++ frontPad geom ks j (path.size - 1)) path'
            path'.size).isSome := by
  rw [nikeHdrTrace_drop geom ks tag ge fil path path' j hsz hn hnnh hle hrouting hfill hks htag hc
      hid path'.size le_rfl]
  have h' := nikeHdrTrace_isSome_of_le geom ks tag ge fil path path'.size (j + 1) (by
    rw [hsz]
    exact h)
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h'
  rw [hs]
  rfl

end Shift

section Front

variable (nike : NIKE) (geom : Geometry)

open Cryptlib.Protocols.Sphinx.KEMSphinx (padAt)

/-- **Two headers whose bytes under hop `j`'s tag agree are the same up to hop `j`**, when the
hops in front are the same and hop `j` has the same tagging function: the headers of their
layers up to `j`, and whether and how they build. Their paths may differ after `j`. -/
theorem layerHdr_front (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path path' : Array PathHop)
    (j : ℕ) (hj : j < path.size) (hj' : j < path'.size)
    (h : ∀ i < j, ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i
      ∧ path[i]!.commands = path'[i]!.commands ∧ path[i + 1]!.id = path'[i + 1]!.id)
    (hM : hdrMsg geom ks tag ge filler path j = hdrMsg geom ks' tag' ge' filler' path' j)
    (htj : tag j = tag' j)
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - j)).isSome)
    (hT' : (nikeHdrTrace geom ks' tag' ge' filler' path' (path'.size - j)).isSome)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hn : path.size ≤ geom.nrHops) (hn' : path'.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hfill' : filler'.size = (geom.nrHops - path'.size) * geom.perHopRoutingInfoLength)
    (htag : ∀ i m, (tag i m).size = macLength) (htag' : ∀ i m, (tag' i m).size = macLength)
    (hgej : (ge j).size = nike.publicKeySize) (hgej' : (ge' j).size = nike.publicKeySize) :
    nikeHdrTrace geom ks tag ge filler path path.size
        = nikeHdrTrace geom ks' tag' ge' filler' path' path'.size
      ∧ ∀ i, i ≤ j → layerHdr geom ks tag ge filler path i
        = layerHdr geom ks' tag' ge' filler' path' i := by
  obtain ⟨s, hs0⟩ := Option.isSome_iff_exists.mp hT
  obtain ⟨s', hs1⟩ := Option.isSome_iff_exists.mp hT'
  obtain ⟨a1, a2⟩ := nikeHdrTrace_at_msg nike geom ks tag ge filler path j hj hgej s hs0
  obtain ⟨b1, b2⟩ := nikeHdrTrace_at_msg nike geom ks' tag' ge' filler' path' j hj' hgej' s' hs1
  have hsize : s.1.size = s'.1.size := by
    rw [(nikeHdrTrace_size geom ks tag ge filler path hnnh hle hfill htag _ s hs0).1,
      (nikeHdrTrace_size geom ks' tag' ge' filler' path' hnnh hle hfill' htag' _ s' hs1).1]
    congr 1
    omega
  have hst : nikeHdrTrace geom ks tag ge filler path (path.size - j)
      = nikeHdrTrace geom ks' tag' ge' filler' path' (path'.size - j) := by
    rw [hs0, hs1]
    exact congrArg some (Prod.ext (by rw [a1, b1, hM, hsize]) (by rw [a2, b2, hM, htj]))
  have hfr := nikeHdrTrace_front geom ks ks' tag tag' ge ge' filler filler' path path' j hj hj'
    h hst
  refine ⟨?_, fun i hi => ?_⟩
  · have := hfr j le_rfl
    rwa [show path.size - j + j = path.size by omega,
      show path'.size - j + j = path'.size by omega] at this
  · by_cases hij : i = j
    · rw [hij]
      unfold layerHdr
      rw [hM, htj]
    · have hlt : i < j := by omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := h i hlt
      have ht := hfr (j - 1 - i) (by omega)
      rw [show path.size - j + (j - 1 - i) = path.size - 1 - i by omega,
        show path'.size - j + (j - 1 - i) = path'.size - 1 - i by omega] at ht
      have hm : hdrMsg geom ks tag ge filler path i
          = hdrMsg geom ks' tag' ge' filler' path' i := by
        unfold hdrMsg
        rw [ht]
        simp only [h1, h3, nikeFragment_congr_path geom path path' _ i (by omega) (by omega) h4
          h5, KEMSphinx.padAt_congr geom ks ks' (i - 1) fun m hm => (h m (by omega)).1]
      unfold layerHdr
      rw [hm, h2]

end Front

end Cryptlib.Protocols.Sphinx.NIKESphinx
