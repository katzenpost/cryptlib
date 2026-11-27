/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxGame

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.KEMSphinx (keysEnc keysKs padAt)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Util.Bytes (ofVector)

/-! # Peeling a packet whose header has a header's length

A relay's `peel` reads its header key and IV through one keystream, and its payload key through
one decryption. On a packet built by `nikePktFn` that decryption undoes the hop's encryption,
so a later layer's payload is the block the hops after it left. -/

section Peel

variable (nike : NIKE) (cipher : WideBlockCipher) (streamS : StreamCipher) (geom : Geometry)

/-- The header a relay sends on, from the header `H` it got, its header keystream `U` and its
blinding factor. -/
def peelHdr (U bf H : ByteArray) : ByteArray :=
  let b := xorBytes (H.extract (2 + nike.publicKeySize)
      (2 + nike.publicKeySize + geom.routingInfoLength)
    ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩) U
  let mac : Vector UInt8 32 := match parseAll (b.extract 0 geom.perHopRoutingInfoLength) with
    | .ok cmds => ((cmds.findSome? RSOR.nextHop).map (·.2)).getD default
    | .error _ => default
  v0AD ++ nikeBlind nike (H.extract 2 (2 + nike.publicKeySize)) bf
    ++ b.extract geom.perHopRoutingInfoLength b.size ++ ofVector mac

omit streamS in
theorem peelHdr_size (U bf H : ByteArray)
    (hH : H.size = 2 + nike.publicKeySize + geom.routingInfoLength + macLength) :
    (peelHdr nike geom U bf H).size
      = 2 + nike.publicKeySize + geom.routingInfoLength + macLength := by
  have hz : (⟨Array.replicate geom.perHopRoutingInfoLength (0 : UInt8)⟩ : ByteArray).size
      = geom.perHopRoutingInfoLength := Array.size_replicate
  have hv : v0AD.size = 2 := rfl
  have hm : macLength = 32 := rfl
  unfold peelHdr
  simp only [ByteArray.size_append, ByteArray.size_extract, size_nikeBlind, size_xorBytes,
    Util.Bytes.size_ofVector, hz, hv]
  omega

/-- **A relay's `peel` on a header and a payload**: the header from the relay's keystream and
blinding factor, the payload decrypted. -/
theorem peel_append (k : HopKeys) (H P : ByteArray)
    (hH : H.size = 2 + nike.publicKeySize + geom.routingInfoLength + macLength)
    (hP : 0 < P.size) :
    RSOR.peel nike cipher streamS geom k (H ++ P)
      = peelHdr nike geom (streamS.keystream (ofVector k.headerEncryption)
          (ofVector k.headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)) k.blindingFactor H
        ++ cipher.decrypt k.payloadEncryption.toArray (ofVector k.headerEncryptionIV) P := by
  have hz : (⟨Array.replicate geom.perHopRoutingInfoLength (0 : UInt8)⟩ : ByteArray).size
      = geom.perHopRoutingInfoLength := Array.size_replicate
  have e1 : (H ++ P).extract (2 + nike.publicKeySize)
        (2 + nike.publicKeySize + geom.routingInfoLength)
      = H.extract (2 + nike.publicKeySize) (2 + nike.publicKeySize + geom.routingInfoLength) :=
    Util.Bytes.extract_append_of_le H P (by omega)
  have e2 : (H ++ P).extract 2 (2 + nike.publicKeySize) = H.extract 2 (2 + nike.publicKeySize) :=
    Util.Bytes.extract_append_of_le H P (by omega)
  have e3 : (H ++ P).extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength)
      (H ++ P).size = P := by
    rw [ByteArray.size_append, ← hH]
    exact Util.Bytes.extract_append_right H P
  have e4 : (H.extract (2 + nike.publicKeySize) (2 + nike.publicKeySize + geom.routingInfoLength)
      ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)).size
      = geom.routingInfoLength + geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_append, ByteArray.size_extract, hz]
    omega
  have hd : 0 < (cipher.decrypt k.payloadEncryption.toArray (ofVector k.headerEncryptionIV)
      P).size := by
    rw [cipher.decrypt_size]
    exact hP
  unfold RSOR.peel peelHdr
  dsimp only
  rw [e1, e2, e3, e4, ite_eq_left hP, ite_eq_left hd]
  rfl

/-- The header after the first `i` hops peeled it. -/
def hdrPeels (ks : List HopKeys) (i : ℕ) (H : ByteArray) : ByteArray :=
  (ks.take i).foldl (fun h k => peelHdr nike geom (streamS.keystream (ofVector k.headerEncryption)
    (ofVector k.headerEncryptionIV) (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    k.blindingFactor h) H

omit cipher in
theorem hdrPeels_succ (ks : List HopKeys) (i : ℕ) (H : ByteArray) (hi : i < ks.length) :
    hdrPeels nike streamS geom ks (i + 1) H
      = peelHdr nike geom (keysKs geom streamS ks.toArray i) (ks.toArray[i]!).blindingFactor
        (hdrPeels nike streamS geom ks i H) := by
  unfold hdrPeels keysKs
  rw [toArray_getElem!_of_getElem? _ _ _ (List.getElem?_eq_getElem hi),
    List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

omit nike streamS geom in
theorem encTrace_keysEnc_size (K : Array HopKeys) (n : ℕ) (init : ByteArray) (m : ℕ) :
    (encTrace (keysEnc cipher K) n init m).size = init.size := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [encTrace_succ]
    exact (cipher.encrypt_size _ _ _).trans ih

/-- **A layer of a packet is its header peeled, and the block the hops after it left**, for
any encryptions that are the keys' at the hops peeled. Each such hop's decryption undoes its
encryption. -/
theorem peels_enc (ks : List HopKeys) (enc : ℕ → ByteArray → ByteArray) (n : ℕ)
    (init H : ByteArray)
    (hH : H.size = 2 + nike.publicKeySize + geom.routingInfoLength + macLength) (i : ℕ)
    (hin : i ≤ n) (hik : i ≤ ks.length) (henc : ∀ m < i, enc m = keysEnc cipher ks.toArray m)
    (h16 : ∀ m < i, 16 ≤ (encTrace enc n init (n - (m + 1))).size) :
    (hdrPeels nike streamS geom ks i H).size
        = 2 + nike.publicKeySize + geom.routingInfoLength + macLength ∧
      peels nike cipher streamS geom ks i (H ++ encTrace enc n init n)
        = hdrPeels nike streamS geom ks i H ++ encTrace enc n init (n - i) := by
  induction i with
  | zero => exact ⟨hH, rfl⟩
  | succ i ih =>
    obtain ⟨ihs, ihp⟩ := ih (by omega) (by omega) (fun m hm => henc m (by omega))
      (fun m hm => h16 m (by omega))
    have hi : i < ks.length := hik
    have hk : ks.toArray[i]! = ks[i] :=
      toArray_getElem!_of_getElem? _ _ _ (List.getElem?_eq_getElem hi)
    have hs : peels nike cipher streamS geom ks (i + 1) (H ++ encTrace enc n init n)
        = RSOR.peel nike cipher streamS geom ks[i] (peels nike cipher streamS geom ks i
          (H ++ encTrace enc n init n)) := by
      unfold peels
      rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
      rfl
    have hh : hdrPeels nike streamS geom ks (i + 1) H
        = peelHdr nike geom (streamS.keystream (ofVector ks[i].headerEncryption)
            (ofVector ks[i].headerEncryptionIV)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)) ks[i].blindingFactor
          (hdrPeels nike streamS geom ks i H) := by
      unfold hdrPeels
      rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
      rfl
    have he : encTrace enc n init (n - i)
        = cipher.encrypt ks[i].payloadEncryption.toArray (ofVector ks[i].headerEncryptionIV)
          (encTrace enc n init (n - (i + 1))) := by
      rw [show n - i = n - (i + 1) + 1 by omega, encTrace_succ,
        show n - 1 - (n - (i + 1)) = i by omega, henc i (Nat.lt_succ_self i)]
      unfold keysEnc
      rw [hk]
    have hsz := h16 i (Nat.lt_succ_self i)
    refine ⟨by rw [hh]; exact peelHdr_size nike geom _ _ _ ihs, ?_⟩
    rw [hs, ihp, he, peel_append nike cipher streamS geom _ _ _ ihs
      (by rw [cipher.encrypt_size]; omega), cipher.roundTrip _ _ _ hsz, hh]

/-- The same for the keys' own encryptions. -/
theorem peels_append (ks : List HopKeys) (n : ℕ) (init H : ByteArray)
    (hH : H.size = 2 + nike.publicKeySize + geom.routingInfoLength + macLength)
    (h16 : 16 ≤ init.size) (i : ℕ) (hin : i ≤ n) (hik : i ≤ ks.length) :
    (hdrPeels nike streamS geom ks i H).size
        = 2 + nike.publicKeySize + geom.routingInfoLength + macLength ∧
      peels nike cipher streamS geom ks i (H ++ encTrace (keysEnc cipher ks.toArray) n init n)
        = hdrPeels nike streamS geom ks i H
          ++ encTrace (keysEnc cipher ks.toArray) n init (n - i) :=
  peels_enc nike cipher streamS geom ks _ n init H hH i hin hik (fun _ _ => rfl) fun m _ => by
    rw [encTrace_keysEnc_size]
    exact h16

end Peel

/-! ## One peel undoes one step of the header -/

section PeelStep

variable (nike : NIKE) (geom : Geometry)

/-- The bytes of a header that holds a hop's fragment `F` and the next layer's routing
information `B`, masked by the head of the hop's keystream `U`, then the padding `Pd` of the
hops in front: its element, its routing information, and that with the keystream taken off. -/
theorem peel_bytes (U a F B Pd g : ByteArray) (h : ℕ)
    (hU : U.size = h + Pd.size + geom.perHopRoutingInfoLength) (hFB : F.size + B.size = h)
    (hR : h + Pd.size = geom.routingInfoLength) (ha : a.size = nike.publicKeySize) :
    (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd) ++ g).extract 0 2 = v0AD
      ∧ (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd) ++ g).extract 2 (2 +
          nike.publicKeySize) = a
      ∧ (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd) ++ g).extract (2 +
          nike.publicKeySize) (2 + nike.publicKeySize + geom.routingInfoLength)
        = xorBytes (F ++ B) (U.extract 0 h) ++ Pd
      ∧ xorBytes (xorBytes (F ++ B) (U.extract 0 h) ++ Pd
          ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)) U
        = (F ++ B) ++ (xorBytes ((U.extract h U.size).extract 0 Pd.size) Pd
          ++ (U.extract h U.size).extract Pd.size (U.extract h U.size).size)
      ∧ (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd) ++ g).extract 0 (2 +
          nike.publicKeySize + geom.routingInfoLength)
        = v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd)
      ∧ (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd) ++ g).extract (2 +
          nike.publicKeySize + geom.routingInfoLength)
          (2 + nike.publicKeySize + geom.routingInfoLength + g.size) = g
      ∧ (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd)).size
        = 2 + nike.publicKeySize + geom.routingInfoLength := by
  have hv : v0AD.size = 2 := rfl
  have hM : (xorBytes (F ++ B) (U.extract 0 h) ++ Pd).size = geom.routingInfoLength := by
    rw [ByteArray.size_append, size_xorBytes, ByteArray.size_append]
    omega
  have hva : (v0AD ++ a).size = 2 + nike.publicKeySize := by
    rw [ByteArray.size_append, hv, ha]
  have hvaM : (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd)).size
      = 2 + nike.publicKeySize + geom.routingInfoLength := by
    rw [ByteArray.size_append, hva, hM]
  obtain ⟨c1, c2⟩ := cascading_xor_step U F B Pd h geom.perHopRoutingInfoLength hU hFB
  have hz : (⟨Array.replicate geom.perHopRoutingInfoLength (0 : UInt8)⟩ : ByteArray).size =
      geom.perHopRoutingInfoLength := Array.size_replicate
  have hbs : (xorBytes (xorBytes (F ++ B) (U.extract 0 h) ++ Pd
      ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)) U).size = h + Pd.size +
          geom.perHopRoutingInfoLength := by
    rw [size_xorBytes, ByteArray.size_append, hM, hz]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hvaM⟩
  · rw [Util.Bytes.extract_append_of_le _ g (by rw [hvaM]; omega),
      Util.Bytes.extract_append_of_le _ _ (by rw [hva]; omega)]
    exact Util.Bytes.extract_append_left v0AD a
  · rw [Util.Bytes.extract_append_of_le _ g (by rw [hvaM]; omega),
      Util.Bytes.extract_append_of_le _ _ (by rw [hva])]
    have := Util.Bytes.extract_append_right v0AD a
    rwa [hv, ha] at this
  · rw [Util.Bytes.extract_append_of_le _ g (by rw [hvaM])]
    have := Util.Bytes.extract_append_right (v0AD ++ a)
      (xorBytes (F ++ B) (U.extract 0 h) ++ Pd)
    rwa [hva, hM] at this
  · have := Util.Bytes.append_extract (xorBytes (xorBytes (F ++ B) (U.extract 0 h) ++ Pd
      ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)) U) h (by rw [hbs]; omega)
    rw [hbs, c1, c2] at this
    exact this.symm
  · have := Util.Bytes.extract_append_left
      (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd)) g
    rwa [hvaM] at this
  · have := Util.Bytes.extract_append_right
      (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd)) g
    rwa [hvaM] at this

/-- The commands a relay reads from such a header are the hop's fragment. -/
theorem peel_cmdBuf (U a F B Pd g : ByteArray) (h : ℕ)
    (hU : U.size = h + Pd.size + geom.perHopRoutingInfoLength) (hFB : F.size + B.size = h) (hF :
        F.size = geom.perHopRoutingInfoLength)
    (hR : h + Pd.size = geom.routingInfoLength) (ha : a.size = nike.publicKeySize) :
    (xorBytes ((v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd) ++ g).extract (2 +
        nike.publicKeySize)
        (2 + nike.publicKeySize + geom.routingInfoLength)
      ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)) U).extract 0
          geom.perHopRoutingInfoLength = F := by
  obtain ⟨-, -, e_r, hb, -, -, -⟩ := peel_bytes nike geom U a F B Pd g h hU hFB hR ha
  rw [e_r, hb, Util.Bytes.extract_append_of_le _ _ (by rw [ByteArray.size_append]; omega), ← hF]
  exact Util.Bytes.extract_append_left F B

/-- **A relay's peel of a header undoes the sender's step for that hop.** Peeled, the header is
the next element, `B` with the next padding, and the tag the fragment names. -/
theorem peelHdr_step (U bf a F B Pd g : ByteArray) (h : ℕ)
    (hU : U.size = h + Pd.size + geom.perHopRoutingInfoLength) (hFB : F.size + B.size = h) (hF :
        F.size = geom.perHopRoutingInfoLength)
    (hR : h + Pd.size = geom.routingInfoLength) (ha : a.size = nike.publicKeySize) :
    peelHdr nike geom U bf (v0AD ++ a ++ (xorBytes (F ++ B) (U.extract 0 h) ++ Pd) ++ g)
      = v0AD ++ nikeBlind nike a bf
        ++ (B ++ (xorBytes ((U.extract h U.size).extract 0 Pd.size) Pd
          ++ (U.extract h U.size).extract Pd.size (U.extract h U.size).size))
        ++ ofVector (match parseAll F with
          | .ok cmds => ((cmds.findSome? RSOR.nextHop).map (·.2)).getD default
          | .error _ => (default : Vector UInt8 32)) := by
  obtain ⟨-, e_a, e_r, hb, -, -, -⟩ := peel_bytes nike geom U a F B Pd g h hU hFB hR ha
  have e1 : ∀ X : ByteArray, ((F ++ B) ++ X).extract 0 geom.perHopRoutingInfoLength = F := fun X =>
      by
    rw [Util.Bytes.extract_append_of_le _ X (by rw [ByteArray.size_append]; omega), ← hF]
    exact Util.Bytes.extract_append_left F B
  have e2 : ∀ X : ByteArray, ((F ++ B) ++ X).extract geom.perHopRoutingInfoLength ((F ++ B) ++
      X).size = B ++ X :=
    fun X => by
      rw [ByteArray.append_assoc, ByteArray.size_append, ← hF]
      exact Util.Bytes.extract_append_right F (B ++ X)
  unfold peelHdr
  dsimp only
  rw [e_a, e_r, hb, e1, e2]

end PeelStep

/-! ## The length of a header -/

section HeaderSize

variable (geom : Geometry)

/-- A hop's routing fragment has a hop's length. -/
theorem nikeFragment_size (path : Array PathHop) (mac : ByteArray) (i : ℕ)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (frag : ByteArray)
    (h : nikeFragment geom path mac i = .ok frag) :
    frag.size = geom.perHopRoutingInfoLength := by
  unfold nikeFragment at h
  obtain ⟨f0, hf0, h⟩ := Except.eq_ok_of_bind_eq_ok h
  have hsz := commandsToBytes_size_le hf0
  obtain rfl := Except.ok.inj h
  by_cases hl : (i == path.size - 1) = true
  · simp only [hl, ↓reduceIte] at hsz ⊢
    exact zeroPadTo_size hsz
  · have hb : (i == path.size - 1) = false := Bool.not_eq_true _ ▸ hl
    rw [hb] at hsz ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hsz ⊢
    refine zeroPadTo_size ?_
    rw [ByteArray.size_append, RoutingCommand.nextNodeHop_toBytes_size]
    omega

/-- **The routing information after `j` steps of the header has the filler's length and `j`
hops', and the tag a tag's.** -/
theorem nikeHdrTrace_size (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (htag : ∀ i m, (tag i m).size = macLength) (j : ℕ) (s : ByteArray × ByteArray)
    (h : nikeHdrTrace geom ks tag ge filler path j = some s) :
    s.1.size = (geom.nrHops - path.size + j) * geom.perHopRoutingInfoLength
      ∧ (0 < j → s.2.size = macLength) := by
  induction j generalizing s with
  | zero =>
    obtain rfl := Option.some.inj h
    refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    by_cases hn : geom.nrHops > path.size
    · exact (congrArg ByteArray.size (ite_eq_left hn)).trans hfill
    · refine (congrArg ByteArray.size (ite_eq_right hn)).trans ?_
      rw [show geom.nrHops - path.size + 0 = 0 by omega, Nat.zero_mul]
      rfl
  | succ j ih =>
    rw [nikeHdrTrace] at h
    cases h0 : nikeHdrTrace geom ks tag ge filler path j with
    | none => rw [h0] at h; cases h
    | some s0 =>
      rw [h0] at h
      dsimp only at h
      cases hf : nikeFragment geom path s0.2 (path.size - 1 - j) with
      | error e => rw [hf] at h; cases h
      | ok frag =>
        rw [hf] at h
        obtain rfl := Option.some.inj h
        refine ⟨?_, fun _ => htag _ _⟩
        rw [size_xorBytes, ByteArray.size_append, nikeFragment_size geom path _ _ hnnh hle frag hf,
          (ih s0 h0).1, show geom.nrHops - path.size + (j + 1) = geom.nrHops - path.size + j + 1
            from rfl, Nat.succ_mul]
        omega

/-- **A header that builds has a header's length**, when the tags have a tag's length and the
first element a key's. -/
theorem hdr_size (pk : ℕ) (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops) (hpos : 0 < path.size)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (htag : ∀ i m, (tag i m).size = macLength) (hge : (ge 0).size = pk)
    (s : ByteArray × ByteArray)
    (h : nikeHdrTrace geom ks tag ge filler path path.size = some s) :
    (v0AD ++ ge 0 ++ s.1 ++ s.2).size = 2 + pk + geom.routingInfoLength + macLength := by
  obtain ⟨h1, h2⟩ := nikeHdrTrace_size geom ks tag ge filler path hnnh hle hfill htag _ s h
  have hv : v0AD.size = 2 := rfl
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, hv, hge, h1, h2 hpos,
    show geom.nrHops - path.size + path.size = geom.nrHops by omega, hrouting, Nat.mul_comm]

end HeaderSize

/-! ## A layer's header, and the next -/

section Layer

variable (nike : NIKE) (geom : Geometry)

omit nike in
/-- The padding after hop `m` has `m + 1` hops' length. -/
theorem padAt_size (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (m : ℕ)
    (hm : (m + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) : (padAt geom ks m).size = (m + 1) *
        geom.perHopRoutingInfoLength := by
  induction m with
  | zero =>
    rw [padAt, ByteArray.size_extract, hks]
    omega
  | succ m ih =>
    have e : (m + 1 + 1) * geom.perHopRoutingInfoLength
        = (m + 1) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength :=
      Nat.succ_mul (m + 1) geom.perHopRoutingInfoLength
    have ih := ih (by omega)
    rw [padAt]
    simp only [ByteArray.size_append, size_xorBytes, ByteArray.size_extract, ih, hks]
    omega

omit nike in
/-- The padding after hop `i` is the tail of its keystream, the padding of the hops in front
folded into its head. -/
theorem padAt_step (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (i : ℕ) :
    padAt geom ks i
      = xorBytes (((ks i).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i +
          1) * geom.perHopRoutingInfoLength) (ks i).size).extract 0
          (if i > 0 then padAt geom ks (i - 1) else ByteArray.empty).size)
          (if i > 0 then padAt geom ks (i - 1) else ByteArray.empty)
        ++ ((ks i).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
            geom.perHopRoutingInfoLength) (ks i).size).extract
          (if i > 0 then padAt geom ks (i - 1) else ByteArray.empty).size
          ((ks i).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
              geom.perHopRoutingInfoLength) (ks i).size).size := by
  cases i with
  | zero =>
    rw [ite_eq_right (lt_irrefl 0), hks]
    have h0 : ∀ E : ByteArray, xorBytes (E.extract 0 ByteArray.empty.size) ByteArray.empty
        = ByteArray.empty := fun E => by
      apply ByteArray.ext
      simp [xorBytes]
    have h1 : ∀ E : ByteArray, E.extract ByteArray.empty.size E.size = E := fun E => by
      have := Util.Bytes.extract_append_left E ByteArray.empty
      rwa [ByteArray.append_empty] at this
    rw [h0, h1, ByteArray.empty_append]
    rfl
  | succ i =>
    rw [ite_eq_left (Nat.succ_pos i), hks]
    rfl

omit nike in
/-- A hop before the last, with no commands of its own, names the next hop and its tag. -/
theorem nikeFragment_parse (path : Array PathHop) (mac : ByteArray) (i : ℕ)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hcmd : path[i]!.commands = [])
        (F : ByteArray)
    (h : nikeFragment geom path mac i = .ok F) :
    parseAll F = .ok [RoutingCommand.nextNodeHop path[i + 1]!.id (toVec32 mac)] := by
  unfold nikeFragment at h
  have hb : (i == path.size - 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  rw [hcmd, hb] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨f0, hf0, h⟩ := Except.eq_ok_of_bind_eq_ok h
  obtain rfl := Except.ok.inj h
  have hsz := commandsToBytes_size_le hf0
  have hc := RoutingCommand.nextNodeHop_toBytes_size path[i + 1]!.id (toVec32 mac)
  have hcb := commandsToBytes_append_singleton (budget := geom.perHopRoutingInfoLength) hf0
    (RoutingCommand.nextNodeHop path[i + 1]!.id (toVec32 mac)) (by omega)
  exact parseAll_commandsToBytes geom.perHopRoutingInfoLength geom.perHopRoutingInfoLength _ (fun c
      hc => by
    simp only [List.mem_singleton] at hc
    rw [hc]
    intro hcon
    injection hcon) _ hcb (by rw [ByteArray.size_append]; omega)

/-- The header of layer `i`: the bytes its tag covers, then the tag. -/
def layerHdr (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ) : ByteArray :=
  hdrMsg geom ks tag ge filler path i ++ tag i (hdrMsg geom ks tag ge filler path i)

private theorem peel_arith (N n i p R : ℕ) (hR : R = p * N) (hn : n ≤ N) (hi : i + 1 < n) :
    R + p - (i + 1) * p = p + (p + (N - n + (n - 1 - (i + 1))) * p)
      ∧ R + p - (i + 1) * p + i * p = R := by
  obtain ⟨k, rfl⟩ : ∃ k, N = i + 2 + k := ⟨N - (i + 2), by omega⟩
  have e : i + 2 + k - n + (n - 1 - (i + 1)) = k := by omega
  subst hR
  rw [e]
  have h1 : p * (i + 2 + k) = i * p + 2 * p + k * p := by ring
  have h2 : (i + 1) * p = i * p + p := by ring
  omega

omit nike in
set_option maxHeartbeats 1000000 in
/-- **The bytes under the tag of a layer before the last**: the element, then the hop's
fragment `F` and the next layer's routing information `B` masked by the head of the hop's
keystream, then the padding of the hops in front. The fragment names the next hop and the next
layer's tag. -/
theorem hdrMsg_struct (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength) (hks : ∀ k,
        (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hcmd : path[i]!.commands = [])
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - i)).isSome) :
    ∃ F B : ByteArray,
      hdrMsg geom ks tag ge filler path i = v0AD ++ ge i ++ (xorBytes (F ++ B) ((ks i).extract 0
          ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
          geom.perHopRoutingInfoLength)) ++ (if i > 0 then padAt geom ks (i - 1) else
          ByteArray.empty))
      ∧ hdrMsg geom ks tag ge filler path (i + 1) = v0AD ++ ge (i + 1) ++ B ++ padAt geom ks i
      ∧ F.size = geom.perHopRoutingInfoLength ∧ F.size + B.size = ((geom.routingInfoLength +
          geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength)
      ∧ (ks i).size = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
          geom.perHopRoutingInfoLength) + (if i > 0 then padAt geom ks (i - 1) else
          ByteArray.empty).size + geom.perHopRoutingInfoLength
      ∧ ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
          geom.perHopRoutingInfoLength) + (if i > 0 then padAt geom ks (i - 1) else
          ByteArray.empty).size = geom.routingInfoLength
      ∧ parseAll F = .ok [RoutingCommand.nextNodeHop path[i + 1]!.id
        (toVec32 (tag (i + 1) (hdrMsg geom ks tag ge filler path (i + 1))))]
      ∧ nikeFragment geom path (tag (i + 1) (hdrMsg geom ks tag ge filler path (i + 1))) i
        = .ok F := by
  have ei : path.size - 1 - (path.size - 1 - i) = i := by omega
  have ei2 : path.size - 1 - (path.size - 1 - (i + 1)) = i + 1 := by omega
  have hpad : (if i + 1 > 0 then padAt geom ks (i + 1 - 1) else ByteArray.empty)
      = padAt geom ks i := ite_eq_left (Nat.succ_pos i)
  rw [show path.size - i = (path.size - 1 - i) + 1 by omega, nikeHdrTrace] at hT
  cases h1 : nikeHdrTrace geom ks tag ge filler path (path.size - 1 - i) with
  | none => rw [h1] at hT; cases hT
  | some s1 =>
    rw [h1, ei] at hT
    dsimp only at hT
    cases hf : nikeFragment geom path s1.2 i with
    | error e => rw [hf] at hT; cases hT
    | ok F =>
      have h1' := h1
      rw [show path.size - 1 - i = (path.size - 1 - (i + 1)) + 1 by omega, nikeHdrTrace] at h1
      cases h2 : nikeHdrTrace geom ks tag ge filler path (path.size - 1 - (i + 1)) with
      | none => rw [h2] at h1; cases h1
      | some s2 =>
        rw [h2, ei2] at h1
        dsimp only at h1
        cases hf2 : nikeFragment geom path s2.2 (i + 1) with
        | error e => rw [hf2] at h1; cases h1
        | ok F2 =>
          rw [hf2, hpad] at h1
          obtain rfl := Option.some.inj h1
          dsimp only at hf
          have hm1 : hdrMsg geom ks tag ge filler path (i + 1)
              = v0AD ++ ge (i + 1) ++ xorBytes (F2 ++ s2.1) ((ks (i + 1)).extract 0
                ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1 + 1) *
                    geom.perHopRoutingInfoLength)) ++ padAt geom ks i := by
            unfold hdrMsg
            rw [h2]
            dsimp only
            rw [hf2]
            dsimp only
            rw [hpad]
          have hm0 : hdrMsg geom ks tag ge filler path i
              = v0AD ++ ge i ++ (xorBytes (F ++ xorBytes (F2 ++ s2.1) ((ks (i + 1)).extract 0
                  ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1 + 1) *
                      geom.perHopRoutingInfoLength))) ((ks i).extract 0 ((geom.routingInfoLength +
                      geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength)) ++
                      (if i > 0 then padAt geom ks (i - 1) else ByteArray.empty)) := by
            unfold hdrMsg
            rw [h1']
            dsimp only
            rw [hf]
            exact ByteArray.append_assoc
          obtain ⟨a1, a2⟩ := peel_arith geom.nrHops path.size i geom.perHopRoutingInfoLength
              geom.routingInfoLength
            hrouting hn hi
          have hs2 := (nikeHdrTrace_size geom ks tag ge filler path hnnh hle hfill htag _ s2
            h2).1
          have hF := nikeFragment_size geom path _ i hnnh hle F hf
          have hF2 := nikeFragment_size geom path _ (i + 1) hnnh hle F2 hf2
          have hPd : (if i > 0 then padAt geom ks (i - 1) else ByteArray.empty).size = i *
              geom.perHopRoutingInfoLength := by
            cases i with
            | zero => rw [ite_eq_right (lt_irrefl 0), Nat.zero_mul]; rfl
            | succ i =>
              rw [ite_eq_left (Nat.succ_pos i)]
              exact padAt_size geom ks hks i (by omega)
          refine ⟨F, _, hm0, hm1, hF,
            by rw [hF, size_xorBytes, ByteArray.size_append, hF2, hs2]; omega,
            by rw [hks, hPd]; omega, by rw [hPd]; omega, ?_, ?_⟩
          · rw [nikeFragment_parse geom path _ i hi hnnh hle hcmd F hf, hm1]
          · rw [hm1]
            exact hf

/-- **Peeling the header of a layer gives the header of the next**, for any keystreams, tags
and elements: the hop's keystream, and the element blinded to the next. -/
theorem peelHdr_layerHdr (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (bf : ByteArray) (i : ℕ)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength) (hks : ∀ k,
        (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (hblind : nikeBlind nike (ge i) bf = ge (i + 1)) (hcmd : path[i]!.commands = [])
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - i)).isSome) :
    peelHdr nike geom (ks i) bf (layerHdr geom ks tag ge filler path i)
      = layerHdr geom ks tag ge filler path (i + 1) := by
  obtain ⟨F, B, hm0, hm1, hF, hFB, hU, hR, hp, -⟩ := hdrMsg_struct geom ks tag ge filler path i hi
    hnnh hle hrouting hn hfill hks htag hcmd hT
  have hmac : (match parseAll F with
      | .ok cmds => ((cmds.findSome? RSOR.nextHop).map (·.2)).getD default
      | .error _ => (default : Vector UInt8 32))
      = toVec32 (tag (i + 1) (hdrMsg geom ks tag ge filler path (i + 1))) := by
    rw [hp]
    rfl
  unfold layerHdr
  rw [hm0, peelHdr_step nike geom (ks i) bf (ge i) F B _ _ _ hU hFB hF hR hge, hblind, hmac,
    ofVector_toVec32 _ (htag _ _), ← padAt_step geom ks hks i, hm1, ← ByteArray.append_assoc]

omit nike in
/-- A header that builds, builds up to every step. -/
theorem nikeHdrTrace_isSome_of_le (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (m k : ℕ)
    (h : (nikeHdrTrace geom ks tag ge filler path (m + k)).isSome) : (nikeHdrTrace geom ks tag ge
        filler path m).isSome := by
  induction k with
  | zero => exact h
  | succ k ih =>
    refine ih ?_
    rw [show m + (k + 1) = (m + k) + 1 from rfl, nikeHdrTrace] at h
    cases h0 : nikeHdrTrace geom ks tag ge filler path (m + k) with
    | none => rw [h0] at h; cases h
    | some s => rfl

omit nike in
/-- The header of a packet is the header of its first layer. -/
theorem layerHdr_zero (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (s : ByteArray × ByteArray)
    (hpos : 0 < path.size) (h : nikeHdrTrace geom ks tag ge filler path path.size = some s) :
    v0AD ++ ge 0 ++ s.1 ++ s.2 = layerHdr geom ks tag ge filler path 0 := by
  have e0 : path.size - 1 - (path.size - 1 - 0) = 0 := by omega
  have h' : nikeHdrTrace geom ks tag ge filler path ((path.size - 1 - 0) + 1) = some s := by
    rwa [show (path.size - 1 - 0) + 1 = path.size by omega]
  rw [nikeHdrTrace] at h'
  cases h1 : nikeHdrTrace geom ks tag ge filler path (path.size - 1 - 0) with
  | none => rw [h1] at h'; cases h'
  | some s1 =>
    rw [h1, e0] at h'
    dsimp only at h'
    cases hf : nikeFragment geom path s1.2 0 with
    | error e => rw [hf] at h'; cases h'
    | ok F =>
      rw [hf] at h'
      obtain rfl := Option.some.inj h'
      unfold layerHdr hdrMsg
      rw [h1]
      dsimp only
      rw [hf]
      dsimp only
      rw [ite_eq_right (lt_irrefl 0), ByteArray.append_empty]

/-- **The header after the first `j` hops peeled it is the header of layer `j`**, when those
hops' keystreams and blinding factors are the keys'. -/
theorem hdrPeels_layerHdr (streamS : StreamCipher) (K : List HopKeys) (ks : ℕ → ByteArray)
    (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (filler : ByteArray)
    (path : Array PathHop) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength) (hks : ∀ k,
        (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge0 : (ge 0).size = nike.publicKeySize)
    (hcmd : ∀ i, i + 1 < path.size → path[i]!.commands = [])
    (hT : (nikeHdrTrace geom ks tag ge filler path path.size).isSome) (j : ℕ) (hj : j < path.size)
        (hjk : j ≤ K.length)
    (hksK : ∀ i < j, keysKs geom streamS K.toArray i = ks i)
    (hgeK : ∀ i < j, nikeBlind nike (ge i) (K.toArray[i]!).blindingFactor = ge (i + 1)) :
    hdrPeels nike streamS geom K j (layerHdr geom ks tag ge filler path 0)
        = layerHdr geom ks tag ge filler path j
      ∧ (ge j).size = nike.publicKeySize := by
  induction j with
  | zero => exact ⟨rfl, hge0⟩
  | succ j ih =>
    obtain ⟨ihp, ihs⟩ := ih (by omega) (by omega) (fun i hi => hksK i (by omega))
      (fun i hi => hgeK i (by omega))
    refine ⟨?_, by rw [← hgeK j (Nat.lt_succ_self j), size_nikeBlind]; exact ihs⟩
    rw [hdrPeels_succ nike streamS geom K j _ hjk, ihp, hksK j (Nat.lt_succ_self j)]
    exact peelHdr_layerHdr nike geom ks tag ge filler path _ j hj hnnh hle hrouting hn hfill hks
      htag ihs (hgeK j (Nat.lt_succ_self j)) (hcmd j hj)
      (nikeHdrTrace_isSome_of_le geom ks tag ge filler path (path.size - j) j
        (by rwa [show path.size - j + j = path.size by omega]))

omit nike in
/-- The padding after a later hop is that after hop `j`, folded through the keystreams of the
hops between. -/
theorem padAt_congr_from (ks ks' : ℕ → ByteArray) (j : ℕ) (h : ∀ i, j < i → ks i = ks' i)
    (hp : padAt geom ks j = padAt geom ks' j) (m : ℕ) (hm : j ≤ m) :
    padAt geom ks m = padAt geom ks' m := by
  induction m, hm using Nat.le_induction with
  | base => exact hp
  | succ m hm ih => rw [padAt, padAt, ih, h (m + 1) (by omega)]

omit nike in
/-- **The header's steps for the hops after `j` read the hops up to `j` through the padding
after hop `j` only.** -/
theorem nikeHdrTrace_congr_tail (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (j : ℕ)
    (h : ∀ i, j < i → ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i)
    (hp : padAt geom ks j = padAt geom ks' j) (t : ℕ) (ht : t + j + 1 ≤ path.size) :
    nikeHdrTrace geom ks tag ge filler path t = nikeHdrTrace geom ks' tag' ge' filler path t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [nikeHdrTrace, nikeHdrTrace, ih (by omega)]
    simp only [(h (path.size - 1 - t) (by omega)).1, (h (path.size - 1 - t) (by omega)).2.1,
      (h (path.size - 1 - t) (by omega)).2.2,
      padAt_congr_from geom ks ks' j (fun i hi => (h i hi).1) hp (path.size - 1 - t - 1)
        (by omega)]

omit nike in
/-- **The header of the layer after hop `j` reads the hops up to `j` through the padding after
hop `j` only.** -/
theorem layerHdr_congr_tail (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (j : ℕ)
    (hj : j + 1 < path.size)
    (h : ∀ i, j < i → ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i)
    (hp : padAt geom ks j = padAt geom ks' j) :
    layerHdr geom ks tag ge filler path (j + 1) = layerHdr geom ks' tag' ge' filler path (j + 1) :=
        by
  have hpad : ∀ k : ℕ → ByteArray, (if j + 1 > 0 then padAt geom k (j + 1 - 1)
      else ByteArray.empty) = padAt geom k j := fun k => ite_eq_left (Nat.succ_pos j)
  unfold layerHdr hdrMsg
  rw [nikeHdrTrace_congr_tail geom ks ks' tag tag' ge ge' filler path j h hp
    (path.size - 1 - (j + 1)) (by omega), hpad, hpad, hp]
  simp only [(h (j + 1) (by omega)).1, (h (j + 1) (by omega)).2.1, (h (j + 1) (by omega)).2.2]

omit nike in
/-- A hop's fragment reads the path for whether the hop is last, its commands, and the next
hop's name. -/
theorem nikeFragment_congr_path (path path' : Array PathHop) (mac : ByteArray) (i : ℕ)
    (hi : i + 1 < path.size) (hi' : i + 1 < path'.size)
    (hc : path[i]!.commands = path'[i]!.commands) (hid : path[i + 1]!.id = path'[i + 1]!.id) :
    nikeFragment geom path mac i = nikeFragment geom path' mac i := by
  have hb : (i == path.size - 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hb' : (i == path'.size - 1) = false := beq_eq_false_iff_ne.mpr (by omega)
  unfold nikeFragment
  rw [hb, hb', hc, hid]

omit nike in
/-- **Two headers that agree at hop `j` agree at the hops in front**, when those hops have the
same keystreams, tags, elements, commands and next names. The paths may differ after `j`. -/
theorem nikeHdrTrace_front (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path path' : Array PathHop) (j : ℕ)
    (hj : j < path.size) (hj' : j < path'.size)
    (h : ∀ i < j, ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i
      ∧ path[i]!.commands = path'[i]!.commands ∧ path[i + 1]!.id = path'[i + 1]!.id)
    (hs : nikeHdrTrace geom ks tag ge filler path (path.size - j)
      = nikeHdrTrace geom ks' tag' ge' filler' path' (path'.size - j)) (k : ℕ) (hk : k ≤ j) :
    nikeHdrTrace geom ks tag ge filler path (path.size - j + k)
      = nikeHdrTrace geom ks' tag' ge' filler' path' (path'.size - j + k) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    have e : path.size - 1 - (path.size - j + k) = j - 1 - k := by omega
    have e' : path'.size - 1 - (path'.size - j + k) = j - 1 - k := by omega
    obtain ⟨h1, h2, h3, h4, h5⟩ := h (j - 1 - k) (by omega)
    rw [show path.size - j + (k + 1) = (path.size - j + k) + 1 from rfl,
      show path'.size - j + (k + 1) = (path'.size - j + k) + 1 from rfl, nikeHdrTrace,
      nikeHdrTrace, ih (by omega), e, e']
    simp only [h1, h2, h3, nikeFragment_congr_path geom path path' _ (j - 1 - k) (by omega)
      (by omega) h4 h5, KEMSphinx.padAt_congr geom ks ks' (j - 1 - k - 1) fun m hm =>
        (h m (by omega)).1]

omit nike in
/-- The payload after the hops down to `j` encrypted it, when hop `j` returns `e`. -/
theorem encTrace_const (enc : ℕ → ByteArray → ByteArray) (n : ℕ) (init e : ByteArray) (j : ℕ)
    (hj : j < n) (he : ∀ b, enc j b = e) : encTrace enc n init (n - j) = e := by
  rw [show n - j = (n - 1 - j) + 1 by omega, encTrace_succ,
    show n - 1 - (n - 1 - j) = j by omega]
  exact he _

omit nike in
/-- **Two payloads that agree at hop `j` agree at the hops in front**, when those hops encrypt
alike. -/
theorem encTrace_front (enc enc' : ℕ → ByteArray → ByteArray) (n n' : ℕ)
    (init init' : ByteArray) (j : ℕ) (hj : j < n) (hj' : j < n')
    (h : ∀ i < j, enc i = enc' i)
    (hs : encTrace enc n init (n - j) = encTrace enc' n' init' (n' - j)) (k : ℕ) (hk : k ≤ j) :
    encTrace enc n init (n - j + k) = encTrace enc' n' init' (n' - j + k) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [show n - j + (k + 1) = (n - j + k) + 1 from rfl,
      show n' - j + (k + 1) = (n' - j + k) + 1 from rfl, encTrace_succ, encTrace_succ,
      ih (by omega), show n - 1 - (n - j + k) = j - 1 - k by omega,
      show n' - 1 - (n' - j + k) = j - 1 - k by omega, h (j - 1 - k) (by omega)]

omit nike in
/-- **Two packets that agree at hop `j` are the same packet**, when the hops in front have the
same keystreams, tags, encryptions, elements, commands and next names, and hop `j` puts the
same block `e` in the payload. The paths may differ after `j`. -/
theorem nikePktFn_front (ks ks' : ℕ → ByteArray) (tag tag' enc enc' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path path' : Array PathHop)
    (payload payload' : ByteArray) (j : ℕ) (hj : j < path.size) (hj' : j < path'.size)
    (h : ∀ i < j, ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i ∧ enc i = enc' i
      ∧ path[i]!.commands = path'[i]!.commands ∧ path[i + 1]!.id = path'[i + 1]!.id)
    (hge0 : ge 0 = ge' 0)
    (hs : nikeHdrTrace geom ks tag ge filler path (path.size - j)
      = nikeHdrTrace geom ks' tag' ge' filler' path' (path'.size - j))
    (e : ByteArray) (he : ∀ b, enc j b = e) (he' : ∀ b, enc' j b = e)
    (hp : payload.size = geom.forwardPayloadLength)
    (hp' : payload'.size = geom.forwardPayloadLength) :
    nikePktFn geom ks tag enc ge filler path payload
      = nikePktFn geom ks' tag' enc' ge' filler' path' payload' := by
  have hT := nikeHdrTrace_front geom ks ks' tag tag' ge ge' filler filler' path path' j hj hj'
    (fun i hi => ⟨(h i hi).1, (h i hi).2.1, (h i hi).2.2.1, (h i hi).2.2.2.2.1,
      (h i hi).2.2.2.2.2⟩) hs j le_rfl
  have hE := encTrace_front enc enc' path.size path'.size ((⟨Array.replicate geom.payloadTagLength
      0⟩ : ByteArray) ++ payload) ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++
      payload') j hj hj'
    (fun i hi => (h i hi).2.2.2.1)
    ((encTrace_const enc path.size _ e j hj he).trans
      (encTrace_const enc' path'.size _ e j hj' he').symm) j le_rfl
  rw [show path.size - j + j = path.size by omega,
    show path'.size - j + j = path'.size by omega] at hT hE
  unfold nikePktFn
  rw [ite_eq_left hp, ite_eq_left hp', hT, hge0]
  exact congrArg (fun P => (nikeHdrTrace geom ks' tag' ge' filler' path' path'.size).map
    fun s => v0AD ++ ge' 0 ++ s.1 ++ s.2 ++ P) hE

omit nike in
/-- **The header's state after hop `i`'s step**: the hop's fragment and the routing information
behind it, masked by the head of the hop's keystream, and the hop's tag on `hdrMsg`. -/
theorem nikeHdrTrace_at (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ)
    (hi : i < path.size) :
    nikeHdrTrace geom ks tag ge filler path (path.size - i)
      = match nikeHdrTrace geom ks tag ge filler path (path.size - 1 - i) with
        | none => none
        | some s =>
          match nikeFragment geom path s.2 i with
          | .error _ => none
          | .ok F => some (xorBytes (F ++ s.1) ((ks i).extract 0 ((geom.routingInfoLength +
              geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength)),
            tag i (hdrMsg geom ks tag ge filler path i)) := by
  rw [show path.size - i = (path.size - 1 - i) + 1 by omega, nikeHdrTrace,
    show path.size - 1 - (path.size - 1 - i) = i by omega]
  unfold hdrMsg
  cases nikeHdrTrace geom ks tag ge filler path (path.size - 1 - i) with
  | none => rfl
  | some s =>
    dsimp only
    cases nikeFragment geom path s.2 i with
    | error e => rfl
    | ok F => rfl

omit nike in
/-- The bytes under the tag of the last hop: its fragment and the filler, masked. -/
theorem hdrMsg_last (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ)
    (hi : i + 1 = path.size) (F : ByteArray)
    (hF : nikeFragment geom path ByteArray.empty i = .ok F) :
    hdrMsg geom ks tag ge filler path i
      = v0AD ++ ge i
        ++ xorBytes (F ++ (if geom.nrHops > path.size then filler else ByteArray.empty))
          ((ks i).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
              geom.perHopRoutingInfoLength))
        ++ (if i > 0 then padAt geom ks (i - 1) else ByteArray.empty) := by
  unfold hdrMsg
  rw [show path.size - 1 - i = 0 by omega, nikeHdrTrace]
  dsimp only
  rw [hF]

omit nike in
/-- The payload after hop `j` returned the block `e` has `e`'s length, when the hops in front
keep lengths. -/
theorem encTrace_size_const (enc : ℕ → ByteArray → ByteArray) (n : ℕ) (init e : ByteArray)
    (j : ℕ) (hj : j < n) (he : ∀ b, enc j b = e)
    (hsz : ∀ m < j, ∀ b, (enc m b).size = b.size) (t : ℕ) (ht : n - j ≤ t) (ht' : t ≤ n) :
    (encTrace enc n init t).size = e.size := by
  induction t, ht using Nat.le_induction with
  | base => rw [encTrace_const enc n init e j hj he]
  | succ t ht ih =>
    rw [encTrace_succ, hsz (n - 1 - t) (by omega), ih (by omega)]

end Layer

/-! ## What a relay forwards -/

section Forward

variable (nike : NIKE) (macS : MAC) (streamS : StreamCipher) (geom : Geometry)

set_option maxHeartbeats 2000000 in
/-- **What a relay forwards.** A relay with the keys `t` that finds its packet's tag right and a
next hop among its commands answers with the blinded element, the routing information shifted
by a hop, the next hop's tag and the payload decrypted. -/
theorem procD_forward {L : ℕ} (t : HopKeys) (D : HopKeys → Vector UInt8 L → Vector UInt8 L)
    (pkt : ByteArray) (cmds : List RoutingCommand) (id m : Vector UInt8 32)
    (h1 : ¬ pkt.size < 2 + nike.publicKeySize + geom.routingInfoLength + macLength)
    (hver : (pkt.extract 0 2).data = v0AD.data)
    (hmac : (ofVector (macS.mac (ofVector t.headerMAC)
        (pkt.extract 0 (2 + nike.publicKeySize + geom.routingInfoLength)))).data
      = (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength)
        (2 + nike.publicKeySize + geom.routingInfoLength + macLength)).data)
    (hparse : parseAll ((xorBytes (pkt.extract (2 + nike.publicKeySize)
          (2 + nike.publicKeySize + geom.routingInfoLength)
        ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩)
        (streamS.keystream (ofVector t.headerEncryption) (ofVector t.headerEncryptionIV)
          (pkt.extract (2 + nike.publicKeySize)
            (2 + nike.publicKeySize + geom.routingInfoLength)
          ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)).size)).extract 0
        geom.perHopRoutingInfoLength) = .ok cmds)
    (hnext : cmds.findSome? RSOR.nextHop = some (id, m)) :
    procD nike macS streamS geom (fun _ => .ok t) D pkt
      = some (none, Primitives.Hash.Sha512.sha512_256 (pkt.extract 2 (2 + nike.publicKeySize)),
        cmds, some (v0AD ++ nikeBlind nike (pkt.extract 2 (2 + nike.publicKeySize))
            t.blindingFactor
          ++ (xorBytes (pkt.extract (2 + nike.publicKeySize)
          (2 + nike.publicKeySize + geom.routingInfoLength)
        ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩)
        (streamS.keystream (ofVector t.headerEncryption) (ofVector t.headerEncryptionIV)
          (pkt.extract (2 + nike.publicKeySize)
            (2 + nike.publicKeySize + geom.routingInfoLength)
          ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)).size)).extract
              geom.perHopRoutingInfoLength (xorBytes (pkt.extract (2 + nike.publicKeySize)
          (2 + nike.publicKeySize + geom.routingInfoLength)
        ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩)
        (streamS.keystream (ofVector t.headerEncryption) (ofVector t.headerEncryptionIV)
          (pkt.extract (2 + nike.publicKeySize)
            (2 + nike.publicKeySize + geom.routingInfoLength)
          ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)).size)).size
          ++ ofVector m
          ++ if (if (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength)
              pkt.size).size > 0 then blockDec D t (pkt.extract (2 + nike.publicKeySize +
              geom.routingInfoLength + macLength) pkt.size) else (pkt.extract (2 +
              nike.publicKeySize + geom.routingInfoLength + macLength) pkt.size)).size > 0 then (if
              (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength)
              pkt.size).size > 0 then blockDec D t (pkt.extract (2 + nike.publicKeySize +
              geom.routingInfoLength + macLength) pkt.size) else (pkt.extract (2 +
              nike.publicKeySize + geom.routingInfoLength + macLength) pkt.size)) else (pkt.extract
              (2 + nike.publicKeySize + geom.routingInfoLength + macLength) pkt.size))) := by
  unfold procD unwrapNIKEDec
  rw [dite_eq_right h1]
  simp only [hver, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind, pure, Except.pure,
    hmac, hparse]
  generalize hfs : List.findSome? _ cmds = o
  obtain rfl : o = some (id, m) := hfs.symm.trans hnext
  rfl

set_option maxHeartbeats 2000000 in
/-- **What a relay does as the last hop.** A relay with the keys `t` that finds its packet's
tag right, and among its commands no next hop and no reply block, hands over what follows the
zero tag of the decrypted payload, when that tag is zero. -/
theorem procD_last {L : ℕ} (t : HopKeys) (D : HopKeys → Vector UInt8 L → Vector UInt8 L)
    (pkt : ByteArray) (cmds : List RoutingCommand)
    (h1 : ¬ pkt.size < 2 + nike.publicKeySize + geom.routingInfoLength + macLength)
    (hver : (pkt.extract 0 2).data = v0AD.data)
    (hmac : (ofVector (macS.mac (ofVector t.headerMAC)
        (pkt.extract 0 (2 + nike.publicKeySize + geom.routingInfoLength)))).data
      = (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength)
        (2 + nike.publicKeySize + geom.routingInfoLength + macLength)).data)
    (hparse : parseAll ((xorBytes (pkt.extract (2 + nike.publicKeySize)
          (2 + nike.publicKeySize + geom.routingInfoLength)
        ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩)
        (streamS.keystream (ofVector t.headerEncryption) (ofVector t.headerEncryptionIV)
          (pkt.extract (2 + nike.publicKeySize)
            (2 + nike.publicKeySize + geom.routingInfoLength)
          ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)).size)).extract 0
        geom.perHopRoutingInfoLength) = .ok cmds)
    (hnext : cmds.findSome? RSOR.nextHop = none)
    (hsr : (cmds.any fun c => match c with
      | RoutingCommand.surbReply _ => true
      | _ => false) = false)
    (hsz : ¬ (if (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength)
        pkt.size).size > 0 then blockDec D t (pkt.extract (2 + nike.publicKeySize +
        geom.routingInfoLength + macLength) pkt.size) else (pkt.extract (2 + nike.publicKeySize +
        geom.routingInfoLength + macLength) pkt.size)).size < geom.payloadTagLength) :
    procD nike macS streamS geom (fun _ => .ok t) D pkt
      = if ((if (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength)
          pkt.size).size > 0 then blockDec D t (pkt.extract (2 + nike.publicKeySize +
          geom.routingInfoLength + macLength) pkt.size) else (pkt.extract (2 + nike.publicKeySize +
          geom.routingInfoLength + macLength) pkt.size)).extract 0 geom.payloadTagLength).data.all
          (· == 0) = true then
          some (some ((if (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength +
              macLength) pkt.size).size > 0 then blockDec D t (pkt.extract (2 + nike.publicKeySize
              + geom.routingInfoLength + macLength) pkt.size) else (pkt.extract (2 +
              nike.publicKeySize + geom.routingInfoLength + macLength) pkt.size)).extract
              geom.payloadTagLength (if (pkt.extract (2 + nike.publicKeySize +
              geom.routingInfoLength + macLength) pkt.size).size > 0 then blockDec D t (pkt.extract
              (2 + nike.publicKeySize + geom.routingInfoLength + macLength) pkt.size) else
              (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength)
              pkt.size)).size),
            Primitives.Hash.Sha512.sha512_256 (pkt.extract 2 (2 + nike.publicKeySize)), cmds, none)
        else none := by
  unfold procD unwrapNIKEDec
  rw [dite_eq_right h1]
  simp only [hver, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind, pure, Except.pure,
    hmac, hparse]
  generalize hfs : List.findSome? _ cmds = o
  obtain rfl : o = none := hfs.symm.trans hnext
  dsimp only
  generalize hany : List.any cmds _ = sr
  obtain rfl : sr = false := hany.symm.trans hsr
  by_cases hz : ((if (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength)
      pkt.size).size > 0 then blockDec D t (pkt.extract (2 + nike.publicKeySize +
      geom.routingInfoLength + macLength) pkt.size) else (pkt.extract (2 + nike.publicKeySize +
      geom.routingInfoLength + macLength) pkt.size)).extract 0 geom.payloadTagLength).data.all (·
      == 0) = true
  · simp only [hsz, hz, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    rfl
  · simp only [hsz, hz, ↓reduceIte, Bool.not_false, Bool.false_eq_true]
    rfl

set_option maxHeartbeats 2000000 in
/-- **What a relay forwards, for a header and a payload**: the header peeled, and the payload
decrypted. -/
theorem procD_forward_append {L : ℕ} (t : HopKeys)
    (D : HopKeys → Vector UInt8 L → Vector UInt8 L) (H P : ByteArray)
    (cmds : List RoutingCommand) (id m : Vector UInt8 32)
    (hH : H.size = 2 + nike.publicKeySize + geom.routingInfoLength + macLength) (hP : P.size = L)
        (hL : 0 < L)
    (hver : H.extract 0 2 = v0AD)
    (hmac : ofVector (macS.mac (ofVector t.headerMAC) (H.extract 0 (2 + nike.publicKeySize +
        geom.routingInfoLength)))
      = H.extract (2 + nike.publicKeySize + geom.routingInfoLength) (2 + nike.publicKeySize +
          geom.routingInfoLength + macLength))
    (hparse : parseAll ((xorBytes (H.extract (2 + nike.publicKeySize) (2 + nike.publicKeySize +
        geom.routingInfoLength)
        ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩)
        (streamS.keystream (ofVector t.headerEncryption) (ofVector t.headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))).extract 0
        geom.perHopRoutingInfoLength) = .ok cmds)
    (hnext : cmds.findSome? RSOR.nextHop = some (id, m)) :
    procD nike macS streamS geom (fun _ => .ok t) D (H ++ P)
      = some (none, Primitives.Hash.Sha512.sha512_256 (H.extract 2 (2 + nike.publicKeySize)),
        cmds, some (peelHdr nike geom (streamS.keystream (ofVector t.headerEncryption)
            (ofVector t.headerEncryptionIV)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)) t.blindingFactor H
          ++ ofVector (D t (Util.Bytes.toVecN L P)))) := by
  have hz : (⟨Array.replicate geom.perHopRoutingInfoLength (0 : UInt8)⟩ : ByteArray).size
      = geom.perHopRoutingInfoLength := Array.size_replicate
  have ex : ∀ a b, b ≤ H.size → (H ++ P).extract a b = H.extract a b := fun a b hb =>
    Util.Bytes.extract_append_of_le H P hb
  have e3 : (H ++ P).extract (2 + nike.publicKeySize + geom.routingInfoLength + macLength) (H ++
      P).size = P := by
    rw [ByteArray.size_append, ← hH]
    exact Util.Bytes.extract_append_right H P
  have e4 : (H.extract (2 + nike.publicKeySize) (2 + nike.publicKeySize + geom.routingInfoLength)
      ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)).size
      = geom.routingInfoLength + geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_append, ByteArray.size_extract, hz]
    omega
  have E := procD_forward nike macS streamS geom t D (H ++ P) cmds id m
    (by rw [ByteArray.size_append]; omega) (by rw [ex _ _ (by omega), hver])
    (by rw [ex _ _ (by omega), ex _ _ (by omega), hmac])
    (by rw [ex _ _ (by omega), e4]; exact hparse) hnext
  rw [E, ex _ _ (by omega), ex _ _ (by omega), e3, e4]
  unfold peelHdr blockDec
  dsimp only
  rw [hparse]
  dsimp only
  have hPpos : P.size > 0 := by omega
  have hD : (ofVector (D t (Util.Bytes.toVecN L P))).size > 0 := by
    rw [Util.Bytes.size_ofVector]
    exact hL
  rw [hnext, ite_eq_left hPpos, ite_eq_left hP, ite_eq_left hD]
  rfl

end Forward

/-! ## What a relay forwards for a layer -/

section ForwardLayer

variable (nike : NIKE) (macS : MAC) (streamS : StreamCipher) (geom : Geometry)

set_option maxHeartbeats 2000000 in
/-- **A relay given a layer before the last forwards the next layer**: the next layer's header,
and the payload decrypted. The relay's keys give the layer's keystream, tag and blinding. -/
theorem procD_layerHdr {L : ℕ} (t : HopKeys) (D : HopKeys → Vector UInt8 L → Vector UInt8 L)
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ) (P : ByteArray)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength) (hks : ∀ k,
        (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (hcmd : path[i]!.commands = []) (hT : (nikeHdrTrace geom ks tag ge filler path (path.size -
        i)).isSome)
    (hksi : streamS.keystream (ofVector t.headerEncryption) (ofVector t.headerEncryptionIV)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) = ks i)
    (htagi : ofVector (macS.mac (ofVector t.headerMAC) (hdrMsg geom ks tag ge filler path i)) = tag
        i (hdrMsg geom ks tag ge filler path i))
    (hblind : nikeBlind nike (ge i) t.blindingFactor = ge (i + 1))
    (hP : P.size = L) (hL : 0 < L) :
    procD nike macS streamS geom (fun _ => .ok t) D (layerHdr geom ks tag ge filler path i ++ P)
      = some (none, Primitives.Hash.Sha512.sha512_256 (ge i),
        [RoutingCommand.nextNodeHop path[i + 1]!.id (toVec32 (tag (i + 1) (hdrMsg geom ks tag ge
            filler path (i + 1))))],
        some (layerHdr geom ks tag ge filler path (i + 1)
          ++ ofVector (D t (Util.Bytes.toVecN L P)))) := by
  obtain ⟨F, B, hm0, hm1, hF, hFB, hU, hR, hp, -⟩ := hdrMsg_struct geom ks tag ge filler path i hi
    hnnh hle hrouting hn hfill hks htag hcmd hT
  obtain ⟨b0, b1, -, -, b4, b5, b6⟩ := peel_bytes nike geom (ks i) (ge i) F B (if i > 0 then padAt
      geom ks (i - 1) else ByteArray.empty)
    (tag i (hdrMsg geom ks tag ge filler path i)) ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength) hU hFB hR hge
  have hL0 : layerHdr geom ks tag ge filler path i
      = v0AD ++ ge i ++ (xorBytes (F ++ B) ((ks i).extract 0 ((geom.routingInfoLength +
          geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength)) ++ (if i > 0
          then padAt geom ks (i - 1) else ByteArray.empty))
        ++ tag i (hdrMsg geom ks tag ge filler path i) := congrArg (· ++ tag i (hdrMsg geom ks tag
            ge filler path i)) hm0
  rw [htag i (hdrMsg geom ks tag ge filler path i)] at b5
  rw [hL0, procD_forward_append nike macS streamS geom t D _ P _ path[i + 1]!.id
      (toVec32 (tag (i + 1) (hdrMsg geom ks tag ge filler path (i + 1))))
      (by rw [ByteArray.size_append, b6, htag]) hP hL b0
      (by rw [b4, b5, ← hm0]; exact htagi)
      (by rw [hksi, peel_cmdBuf nike geom (ks i) (ge i) F B _ _ _ hU hFB hF hR hge]; exact hp)
      rfl,
    b1, hksi, ← hL0, peelHdr_layerHdr nike geom ks tag ge filler path _ i hi hnnh hle hrouting hn
      hfill hks htag hge hblind hcmd hT]

end ForwardLayer

end Cryptlib.Protocols.Sphinx.NIKESphinx
