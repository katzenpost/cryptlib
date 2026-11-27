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
open Cryptlib.Protocols.Sphinx.KEMSphinx (keysEnc keysKs)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
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

/-- **A layer of a packet is its header peeled, and the block the hops after it left.** Each
hop's decryption undoes its encryption. -/
theorem peels_append (ks : List HopKeys) (n : ℕ) (init H : ByteArray)
    (hH : H.size = 2 + nike.publicKeySize + geom.routingInfoLength + macLength)
    (h16 : 16 ≤ init.size) (i : ℕ) (hin : i ≤ n) (hik : i ≤ ks.length) :
    (hdrPeels nike streamS geom ks i H).size
        = 2 + nike.publicKeySize + geom.routingInfoLength + macLength ∧
      peels nike cipher streamS geom ks i (H ++ encTrace (keysEnc cipher ks.toArray) n init n)
        = hdrPeels nike streamS geom ks i H
          ++ encTrace (keysEnc cipher ks.toArray) n init (n - i) := by
  induction i with
  | zero => exact ⟨hH, rfl⟩
  | succ i ih =>
    obtain ⟨ihs, ihp⟩ := ih (by omega) (by omega)
    have hi : i < ks.length := hik
    have hk : ks.toArray[i]! = ks[i] :=
      toArray_getElem!_of_getElem? _ _ _ (List.getElem?_eq_getElem hi)
    have hs : peels nike cipher streamS geom ks (i + 1)
          (H ++ encTrace (keysEnc cipher ks.toArray) n init n)
        = RSOR.peel nike cipher streamS geom ks[i] (peels nike cipher streamS geom ks i
          (H ++ encTrace (keysEnc cipher ks.toArray) n init n)) := by
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
    have he : encTrace (keysEnc cipher ks.toArray) n init (n - i)
        = cipher.encrypt ks[i].payloadEncryption.toArray (ofVector ks[i].headerEncryptionIV)
          (encTrace (keysEnc cipher ks.toArray) n init (n - (i + 1))) := by
      rw [show n - i = n - (i + 1) + 1 by omega, encTrace_succ,
        show n - 1 - (n - (i + 1)) = i by omega]
      unfold keysEnc
      rw [hk]
    have hsz := encTrace_keysEnc_size cipher ks.toArray n init (n - (i + 1))
    refine ⟨by rw [hh]; exact peelHdr_size nike geom _ _ _ ihs, ?_⟩
    rw [hs, ihp, he, peel_append nike cipher streamS geom _ _ _ ihs
      (by rw [cipher.encrypt_size, hsz]; omega), cipher.roundTrip _ _ _ (by rw [hsz]; exact h16),
      hh]

end Peel

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

end HeaderSize

end Cryptlib.Protocols.Sphinx.NIKESphinx
