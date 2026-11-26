/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTheorems

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

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
open Cryptlib.Util.Bytes (ofVector)

/-! # KEM-Sphinx: the forwarded packet is a fresh packet on the rest of the path

Kuhn, Beck and Strufe (*Breaking and (Partially) Fixing Provably Secure Onion Routing*, S&P 2020)
replace the 2009 properties with layer unlinkability and tail indistinguishability. Tail
indistinguishability says that the packet an honest hop forwards cannot be told from the same
layer of an unrelated onion that shares the rest of the path.

This file proves the exact fact that property rests on, for `newKEMPacket` and `unwrapKEM`
themselves (`newKEMPacket_unwrapKEM`): the packet the first hop forwards *is* the packet `newKEMPacket`
builds on the rest of the path, from the remaining seeds and with the filler `tailFiller`, the
old filler followed by one more block. That block is the XOR of one keystream block from every
hop of the path, the first hop included (`tailPad`). `wrapKEM_unwrapKEM_tail` says the same of
`wrapKEM`, and is the proof of the `unwrap_tail` field of `KEMSphinxScheme`, built here by
`kemSphinxSchemeOf`.

What is left of tail indistinguishability is that the extra block looks random to someone who
lacks the first hop's key; `KEMSphinxTailIndist.lean` states that with probabilities. Only the
first hop is treated: a later hop follows by applying the theorem once per hop before it. -/

/-- A `forIn` over `List.range' 0 n` whose every step yields the next value of `tr` returns
`tr n`. The converse of `List.forIn_exists_trace`. -/
theorem forIn_range'_ok {α ε : Type} (f : Nat → α → Except ε (ForInStep α)) (tr : Nat → α)
    (n a : Nat) (h : ∀ j, j < n → f (a + j) (tr j) = Except.ok (ForInStep.yield (tr (j + 1)))) :
    forIn (List.range' a n) (tr 0) f = Except.ok (tr n) := by
  induction n generalizing a tr with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h0]
    show forIn (List.range' (a + 1) n) (tr 1) f = Except.ok (tr (n + 1))
    exact ih (fun j => tr (j + 1)) (a + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show a + (j + 1) = a + 1 + j from by omega] at this)

/-- `forIn_range'_ok` with the first and last values of the trace named. -/
theorem forIn_range'_ok' {α ε : Type} (f : Nat → α → Except ε (ForInStep α)) (tr : Nat → α)
    (n : Nat) (init final : α) (h0 : tr 0 = init) (hn : tr n = final)
    (h : ∀ j, j < n → f j (tr j) = Except.ok (ForInStep.yield (tr (j + 1)))) :
    forIn (List.range' 0 n) init f = Except.ok final := by
  rw [← h0, ← hn]
  exact forIn_range'_ok f tr n 0 (fun j hj => by rw [Nat.zero_add]; exact h j hj)

/-- A fold over `List.range' 0 n` whose every step gives the next value of `tr` returns `tr n`. -/
theorem foldl_range'_trace {α : Type} (g : α → Nat → α) (tr : Nat → α) (n a : Nat)
    (h : ∀ j, j < n → tr (j + 1) = g (tr j) (a + j)) :
    (List.range' a n).foldl g (tr 0) = tr n := by
  induction n generalizing a tr with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons]
    have h0 : tr 1 = g (tr 0) a := by simpa using h 0 (by omega)
    rw [← h0]
    exact ih (fun j => tr (j + 1)) (a + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show a + (j + 1) = a + 1 + j from by omega] at this)

theorem Except.bind_eq_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {a : α} {b : β}
    (h1 : e = Except.ok a) (h2 : f a = Except.ok b) : (e >>= f) = Except.ok b := by
  subst h1; exact h2

/-- An index below the cut reads the same from a prefix as from the whole array. -/
theorem getElem!_extract_zero {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (hi : i < j)
    (hj : j ≤ a.size) : (a.extract 0 j)[i]! = a[i]! := by
  rw [getElem!_pos (a.extract 0 j) i (by simp; omega), getElem!_pos a i (by omega)]
  simp

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- The converse of `createKEMHeader_unfold`: arrays and a trace with the contents of the three
loops make `createKEMHeader` succeed with the header they describe. -/
theorem createKEMHeader_fold (kem : KEM) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
    (geom : Geometry) (ephemeralSeeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop)
    (kemElements : Array ByteArray) (keys : Array HopKeys)
    (riKeyStream riPadding : Array ByteArray) (s : Nat → ByteArray × ByteArray)
    (hpos : path.size ≠ 0) (hgen : path.size ≤ geom.nrHops)
    (hseeds : ephemeralSeeds.size = path.size)
    (hfsize : geom.nrHops > path.size →
      filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hkn : kemElements.size = path.size) (hkeys : keys.size = path.size)
    (hrks : riKeyStream.size = path.size) (hrp : riPadding.size = path.size)
    (hkc : ∀ i (_hi : i < path.size), ∃ ct ss,
      kemEncap kem (path[i]!).publicKey (ephemeralSeeds[i]!) = Except.ok (ct, ss) ∧
      kemElements[i]! = ct ∧ keys[i]! = deriveHopKeys kdfS ss)
    (hri : ∀ i (_hi : i < path.size),
      riKeyStream[i]! = (streamS.keystream (ofVector (keys[i]!).headerEncryption)
          (ofVector (keys[i]!).headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength)
          - (i + 1) * geom.perHopRoutingInfoLength) ∧
      riPadding[i]! =
        (let totalRiLen := geom.routingInfoLength + geom.perHopRoutingInfoLength
         let ks := streamS.keystream (ofVector (keys[i]!).headerEncryption)
           (ofVector (keys[i]!).headerEncryptionIV) totalRiLen
         let ksLen := totalRiLen - (i + 1) * geom.perHopRoutingInfoLength
         let thisPad0 := ks.extract ksLen totalRiLen
         if i > 0 then
           xorBytes (thisPad0.extract 0 riPadding[i - 1]!.size) riPadding[i - 1]!
             ++ thisPad0.extract riPadding[i - 1]!.size thisPad0.size
         else thisPad0))
    (hs0 : s 0 = (if geom.nrHops > path.size then filler else ByteArray.empty, ByteArray.empty))
    (hstep : ∀ j (_hj : j < path.size), ∃ riFragment,
      kemRiFragment kem geom path kemElements (s j).2 path.size (path.size - 1 - j)
          = Except.ok riFragment ∧
      (s (j + 1)).1 = xorBytes (riFragment ++ (s j).1) (riKeyStream[path.size - 1 - j]!) ∧
      (s (j + 1)).2 = ofVector (macS.mac (ofVector (keys[path.size - 1 - j]!).headerMAC)
        (v0AD ++ kemElements[path.size - 1 - j]! ++ (s (j + 1)).1
          ++ (if path.size - 1 - j > 0 then riPadding[path.size - 1 - j - 1]!
              else ByteArray.empty)))) :
    createKEMHeader kem macS kdfS streamS geom ephemeralSeeds filler path
      = Except.ok (v0AD ++ kemElements[0]! ++ (s path.size).1 ++ (s path.size).2,
          Array.ofFn (fun i : Fin path.size =>
            ({ key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV }
              : SPRPKey))) := by
  unfold createKEMHeader createKEMHeaderFrom
  dsimp only
  split
  case isTrue hc =>
    exfalso
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    omega
  case isFalse =>
    split
    case isTrue hc => exact absurd hseeds hc
    case isFalse =>
      split
      case isTrue hc =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.2 (hfsize hc.1)
      case isFalse =>
        simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
          Nat.add_sub_cancel, Nat.div_one]
        refine Except.bind_eq_ok (a := (kemElements, keys)) ?_ ?_
        · refine forIn_range'_ok' _ (fun j => (kemElements.extract 0 j, keys.extract 0 j))
            path.size _ _ (by simp) (by rw [← hkn, Array.extract_size, hkn, ← hkeys, Array.extract_size]) ?_
          intro j hj
          obtain ⟨ct, ss, hkenc, hct, hkey⟩ := hkc j hj
          dsimp only
          rw [hkenc]
          have h1 : (kemElements.extract 0 j).push ct = kemElements.extract 0 (j + 1) := by
            rw [← hct, getElem!_pos kemElements j (by omega),
              Array.push_extract_getElem (by omega)]
            simp
          have h2 : (keys.extract 0 j).push (deriveHopKeys kdfS ss) = keys.extract 0 (j + 1) := by
            rw [← hkey, getElem!_pos keys j (by omega), Array.push_extract_getElem (by omega)]
            simp
          show Except.ok (ForInStep.yield ((kemElements.extract 0 j).push ct,
            (keys.extract 0 j).push (deriveHopKeys kdfS ss))) = _
          rw [h1, h2]
        · refine Except.bind_eq_ok (a := (riKeyStream, riPadding)) ?_ ?_
          · refine forIn_range'_ok' _ (fun j => (riKeyStream.extract 0 j, riPadding.extract 0 j))
              path.size _ _ (by simp) (by rw [← hrks, Array.extract_size, hrks, ← hrp, Array.extract_size]) ?_
            intro j hj
            obtain ⟨hks, hpad⟩ := hri j hj
            dsimp only at hpad ⊢
            have h1 : (riKeyStream.extract 0 j).push riKeyStream[j]!
                = riKeyStream.extract 0 (j + 1) := by
              rw [getElem!_pos riKeyStream j (by omega), Array.push_extract_getElem (by omega)]
              simp
            have h2 : (riPadding.extract 0 j).push riPadding[j]!
                = riPadding.extract 0 (j + 1) := by
              rw [getElem!_pos riPadding j (by omega), Array.push_extract_getElem (by omega)]
              simp
            rw [← h1, ← h2, hks]
            by_cases hj0 : j > 0
            · rw [ite_eq_left hj0] at hpad
              rw [ite_eq_left hj0, getElem!_extract_zero riPadding (j - 1) j (by omega) (by omega),
                hpad]
              rfl
            · rw [ite_eq_right hj0] at hpad
              rw [ite_eq_right hj0, hpad]
              rfl
          · refine Except.bind_eq_ok (a := s path.size) ?_ ?_
            · refine forIn_range'_ok' _ s path.size _ _ hs0 rfl ?_
              intro j hj
              obtain ⟨riFragment, hfrag, h1, h2⟩ := hstep j hj
              dsimp only
              rw [hfrag]
              show Except.ok (ForInStep.yield (_, _)) = Except.ok (ForInStep.yield (s (j + 1)))
              rw [← h1, ← h2]
            · rfl

/-- The converse of `createKEMHeaderFrom_unfold`: arrays and a trace with the contents of its
two loops make `createKEMHeaderFrom` succeed with the header they describe. -/
theorem createKEMHeaderFrom_fold (kem : KEM) (macS : MAC) (streamS : StreamCipher)
    (geom : Geometry) (kemElements : Array ByteArray) (keys : Array HopKeys) (filler : ByteArray)
    (path : Array PathHop) (riKeyStream riPadding : Array ByteArray)
    (s : Nat → ByteArray × ByteArray)
    (hrks : riKeyStream.size = path.size) (hrp : riPadding.size = path.size)
    (hri : ∀ i (_hi : i < path.size),
      riKeyStream[i]! = (streamS.keystream (ofVector (keys[i]!).headerEncryption)
          (ofVector (keys[i]!).headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength)
          - (i + 1) * geom.perHopRoutingInfoLength) ∧
      riPadding[i]! =
        (let totalRiLen := geom.routingInfoLength + geom.perHopRoutingInfoLength
         let ks := streamS.keystream (ofVector (keys[i]!).headerEncryption)
           (ofVector (keys[i]!).headerEncryptionIV) totalRiLen
         let ksLen := totalRiLen - (i + 1) * geom.perHopRoutingInfoLength
         let thisPad0 := ks.extract ksLen totalRiLen
         if i > 0 then
           xorBytes (thisPad0.extract 0 riPadding[i - 1]!.size) riPadding[i - 1]!
             ++ thisPad0.extract riPadding[i - 1]!.size thisPad0.size
         else thisPad0))
    (hs0 : s 0 = (if geom.nrHops > path.size then filler else ByteArray.empty, ByteArray.empty))
    (hstep : ∀ j (_hj : j < path.size), ∃ riFragment,
      kemRiFragment kem geom path kemElements (s j).2 path.size (path.size - 1 - j)
          = Except.ok riFragment ∧
      (s (j + 1)).1 = xorBytes (riFragment ++ (s j).1) (riKeyStream[path.size - 1 - j]!) ∧
      (s (j + 1)).2 = ofVector (macS.mac (ofVector (keys[path.size - 1 - j]!).headerMAC)
        (v0AD ++ kemElements[path.size - 1 - j]! ++ (s (j + 1)).1
          ++ (if path.size - 1 - j > 0 then riPadding[path.size - 1 - j - 1]!
              else ByteArray.empty)))) :
    createKEMHeaderFrom kem macS streamS geom kemElements keys filler path
      = Except.ok (v0AD ++ kemElements[0]! ++ (s path.size).1 ++ (s path.size).2,
          Array.ofFn (fun i : Fin path.size =>
            ({ key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV }
              : SPRPKey))) := by
  unfold createKEMHeaderFrom
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine Except.bind_eq_ok (a := (riKeyStream, riPadding)) ?_ ?_
  · refine forIn_range'_ok' _ (fun j => (riKeyStream.extract 0 j, riPadding.extract 0 j))
      path.size _ _ (by simp)
      (by rw [← hrks, Array.extract_size, hrks, ← hrp, Array.extract_size]) ?_
    intro j hj
    obtain ⟨hks, hpad⟩ := hri j hj
    dsimp only at hpad ⊢
    have h1 : (riKeyStream.extract 0 j).push riKeyStream[j]!
        = riKeyStream.extract 0 (j + 1) := by
      rw [getElem!_pos riKeyStream j (by omega), Array.push_extract_getElem (by omega)]
      simp
    have h2 : (riPadding.extract 0 j).push riPadding[j]!
        = riPadding.extract 0 (j + 1) := by
      rw [getElem!_pos riPadding j (by omega), Array.push_extract_getElem (by omega)]
      simp
    rw [← h1, ← h2, hks]
    by_cases hj0 : j > 0
    · rw [ite_eq_left hj0] at hpad
      rw [ite_eq_left hj0, getElem!_extract_zero riPadding (j - 1) j (by omega) (by omega),
        hpad]
      rfl
    · rw [ite_eq_right hj0] at hpad
      rw [ite_eq_right hj0, hpad]
      rfl
  · refine Except.bind_eq_ok (a := s path.size) ?_ ?_
    · refine forIn_range'_ok' _ s path.size _ _ hs0 rfl ?_
      intro j hj
      obtain ⟨riFragment, hfrag, h1, h2⟩ := hstep j hj
      dsimp only
      rw [hfrag]
      show Except.ok (ForInStep.yield (_, _)) = Except.ok (ForInStep.yield (s (j + 1)))
      rw [← h1, ← h2]
    · rfl

/-- The converse of `newKEMPacket_unfold`. -/
theorem newKEMPacket_fold (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
    (streamS : StreamCipher) (geom : Geometry) (ephemeralSeeds : Array (Vector UInt8 32))
    (filler : ByteArray) (path : Array PathHop) (payload hdr : ByteArray)
    (sprpKeys : Array SPRPKey) (hpay : payload.size = geom.forwardPayloadLength)
    (hcreate : createKEMHeader kem macS kdfS streamS geom ephemeralSeeds filler path
      = Except.ok (hdr, sprpKeys)) :
    newKEMPacket kem cipher macS kdfS streamS geom ephemeralSeeds filler path payload
      = Except.ok (hdr ++ (List.range' 0 sprpKeys.size).foldl (payloadEncryptStep cipher sprpKeys)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)) := by
  unfold newKEMPacket
  dsimp only
  split
  case isTrue hc => exact absurd hpay hc
  case isFalse =>
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
    rw [hcreate]
    rfl

theorem Except.bind_eq_of_ok {ε α β : Type} {e : Except ε α} {a : α} (f : α → Except ε β)
    (h : e = Except.ok a) : (e >>= f) = f a := by
  subst h; rfl

/-- `createKEMHeader` is `createKEMHeaderFrom` on the ciphertexts and keys its first loop
produces: `kemElements[i]!` and `keys[i]!` come from hop `i`'s encapsulation. -/
theorem createKEMHeader_eq_createKEMHeaderFrom (kem : KEM) (macS : MAC) (kdfS : KDF)
    (streamS : StreamCipher) (geom : Geometry) (ephemeralSeeds : Array (Vector UInt8 32))
    (filler : ByteArray) (path : Array PathHop)
    (kemElements : Array ByteArray) (keys : Array HopKeys)
    (hpos : path.size ≠ 0) (hgen : path.size ≤ geom.nrHops)
    (hseeds : ephemeralSeeds.size = path.size)
    (hfsize : geom.nrHops > path.size →
      filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hkn : kemElements.size = path.size) (hkeys : keys.size = path.size)
    (hkc : ∀ i (_hi : i < path.size), ∃ ct ss,
      kemEncap kem (path[i]!).publicKey (ephemeralSeeds[i]!) = Except.ok (ct, ss) ∧
      kemElements[i]! = ct ∧ keys[i]! = deriveHopKeys kdfS ss) :
    createKEMHeader kem macS kdfS streamS geom ephemeralSeeds filler path
      = createKEMHeaderFrom kem macS streamS geom kemElements keys filler path := by
  unfold createKEMHeader
  dsimp only
  split
  case isTrue hc =>
    exfalso
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    omega
  case isFalse =>
    split
    case isTrue hc => exact absurd hseeds hc
    case isFalse =>
      split
      case isTrue hc =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.2 (hfsize hc.1)
      case isFalse =>
        simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
          Nat.add_sub_cancel, Nat.div_one]
        refine (Except.bind_eq_of_ok (a := (kemElements, keys)) _ ?_).trans rfl
        refine forIn_range'_ok' _ (fun j => (kemElements.extract 0 j, keys.extract 0 j))
          path.size _ _ (by simp)
          (by rw [← hkn, Array.extract_size, hkn, ← hkeys, Array.extract_size]) ?_
        intro j hj
        obtain ⟨ct, ss, hkenc, hct, hkey⟩ := hkc j hj
        dsimp only
        rw [hkenc]
        have h1 : (kemElements.extract 0 j).push ct = kemElements.extract 0 (j + 1) := by
          rw [← hct, getElem!_pos kemElements j (by omega),
            Array.push_extract_getElem (by omega)]
          simp
        have h2 : (keys.extract 0 j).push (deriveHopKeys kdfS ss) = keys.extract 0 (j + 1) := by
          rw [← hkey, getElem!_pos keys j (by omega), Array.push_extract_getElem (by omega)]
          simp
        show Except.ok (ForInStep.yield ((kemElements.extract 0 j).push ct,
          (keys.extract 0 j).push (deriveHopKeys kdfS ss))) = _
        rw [h1, h2]

/-- `newKEMPacket` is `newKEMPacketFrom` on the ciphertexts and keys the header's first loop
produces. -/
theorem newKEMPacket_eq_newKEMPacketFrom (kem : KEM) (cipher : WideBlockCipher) (macS : MAC)
    (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (ephemeralSeeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload : ByteArray) (kemElements : Array ByteArray) (keys : Array HopKeys)
    (hpos : path.size ≠ 0) (hgen : path.size ≤ geom.nrHops)
    (hseeds : ephemeralSeeds.size = path.size)
    (hfsize : geom.nrHops > path.size →
      filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hkn : kemElements.size = path.size) (hkeys : keys.size = path.size)
    (hkc : ∀ i (_hi : i < path.size), ∃ ct ss,
      kemEncap kem (path[i]!).publicKey (ephemeralSeeds[i]!) = Except.ok (ct, ss) ∧
      kemElements[i]! = ct ∧ keys[i]! = deriveHopKeys kdfS ss) :
    newKEMPacket kem cipher macS kdfS streamS geom ephemeralSeeds filler path payload
      = newKEMPacketFrom kem cipher macS streamS geom kemElements keys filler path payload := by
  unfold newKEMPacket newKEMPacketFrom
  rw [createKEMHeader_eq_createKEMHeaderFrom kem macS kdfS streamS geom ephemeralSeeds filler
    path kemElements keys hpos hgen hseeds hfsize hkn hkeys hkc]

/-- A packet `newKEMPacket` built is the packet `newKEMPacketFrom` builds from the ciphertexts
and keys of the hops' encapsulations. -/
theorem newKEMPacket_ok_newKEMPacketFrom (kem : KEM) (cipher : WideBlockCipher) (macS : MAC)
    (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (ephemeralSeeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload pkt : ByteArray)
    (h : newKEMPacket kem cipher macS kdfS streamS geom ephemeralSeeds filler path payload
      = Except.ok pkt) :
    ∃ (kemElements : Array ByteArray) (keys : Array HopKeys),
      kemElements.size = path.size ∧ keys.size = path.size ∧
      (∀ i (_hi : i < path.size), ∃ ct ss,
        kemEncap kem (path[i]!).publicKey (ephemeralSeeds[i]!) = Except.ok (ct, ss) ∧
        kemElements[i]! = ct ∧ keys[i]! = deriveHopKeys kdfS ss) ∧
      newKEMPacketFrom kem cipher macS streamS geom kemElements keys filler path payload
        = Except.ok pkt := by
  obtain ⟨-, hdr, sprpKeys, _t, hcreate, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ h
  obtain ⟨hpos, hgen, hseeds, hfsize, kemElements, keys, _rks, _rp, _s, hkn, hkeys, -, -, hkc,
    -⟩ := createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ _ _ hcreate
  refine ⟨kemElements, keys, hkn, hkeys, hkc, ?_⟩
  rw [← newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom ephemeralSeeds filler
    path payload kemElements keys hpos hgen hseeds hfsize hkn hkeys hkc]
  exact h

/-- An index reads the same from a suffix as from the whole array, shifted. -/
theorem getElem!_extract_from {α : Type} [Inhabited α] (a : Array α) (lo i : Nat)
    (h : lo + i < a.size) : (a.extract lo a.size)[i]! = a[lo + i]! := by
  rw [getElem!_pos (a.extract lo a.size) i (by simp; omega), getElem!_pos a (lo + i) h]
  simp

/-- `xorBytes` commutes with taking a slice both arguments cover. -/
theorem xorBytes_extract (a b : ByteArray) (p q : Nat) (hq : q ≤ a.size) (hb : q ≤ b.size) :
    (xorBytes a b).extract p q = xorBytes (a.extract p q) (b.extract p q) := by
  apply ByteArray.ext_getElem
  · simp [ByteArray.size_extract]
  · intro i h1 h2
    have hi : p + i < q := by
      simp only [ByteArray.size_extract, size_xorBytes] at h1
      omega
    rw [ByteArray.getElem_extract, xorBytes_getElem a b (p + i) (by omega), dite_eq_left (by omega),
      xorBytes_getElem (a.extract p q) (b.extract p q) i
        (by simp only [ByteArray.size_extract]; omega),
      dite_eq_left (by simp only [ByteArray.size_extract]; omega), ByteArray.getElem_extract,
      ByteArray.getElem_extract]

/-- A prefix splits at any earlier point. -/
theorem extract_split (b : ByteArray) (p q : Nat) (hpq : p ≤ q) (hq : q ≤ b.size) :
    b.extract 0 q = b.extract 0 p ++ b.extract p q := by
  have h := Cryptlib.Util.Bytes.append_extract (b.extract 0 q) p
    (by rw [ByteArray.size_extract]; omega)
  rw [ByteArray.extract_extract, ByteArray.extract_extract, ByteArray.size_extract] at h
  rw [← h]
  congr 1 <;> congr 1 <;> omega

/-- The first `m` bytes of a cascaded padding. -/
theorem pad_extract_head (T P : ByteArray) (m : Nat) (hm : m ≤ P.size) (hP : P.size ≤ T.size) :
    (xorBytes (T.extract 0 P.size) P ++ T.extract P.size T.size).extract 0 m
      = xorBytes (T.extract 0 m) (P.extract 0 m) := by
  have hsz : (T.extract 0 P.size).size = P.size := by rw [ByteArray.size_extract]; omega
  rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [size_xorBytes, hsz]; exact hm),
    xorBytes_extract _ _ _ _ (by rw [hsz]; exact hm) hm, ByteArray.extract_extract]
  congr 2
  omega

/-- A cascaded padding without its first `m` bytes is the cascaded padding of the two inputs
without theirs. -/
theorem pad_extract_tail (T P : ByteArray) (m : Nat) (hm : m ≤ P.size) (hP : P.size ≤ T.size) :
    (xorBytes (T.extract 0 P.size) P ++ T.extract P.size T.size).extract m T.size
      = xorBytes ((T.extract m T.size).extract 0 (P.extract m P.size).size) (P.extract m P.size)
        ++ (T.extract m T.size).extract (P.extract m P.size).size (T.extract m T.size).size := by
  have hsz : (T.extract 0 P.size).size = P.size := by rw [ByteArray.size_extract]; omega
  have hxs : (xorBytes (T.extract 0 P.size) P).size = P.size := by rw [size_xorBytes, hsz]
  have htl : (T.extract P.size T.size).size = T.size - P.size := by
    rw [ByteArray.size_extract]; omega
  have hTs : T.size = (xorBytes (T.extract 0 P.size) P).size + (T.extract P.size T.size).size := by
    rw [hxs, htl]; omega
  have hps : (P.extract m P.size).size = P.size - m := by rw [ByteArray.size_extract]; omega
  have hts : (T.extract m T.size).size = T.size - m := by rw [ByteArray.size_extract]; omega
  have key := Cryptlib.Util.Bytes.extract_append_ge (xorBytes (T.extract 0 P.size) P)
    (T.extract P.size T.size) (lo := m) (by rw [hxs]; exact hm)
  rw [← hTs] at key
  rw [key, hxs,
    xorBytes_extract _ _ _ _ (by rw [hsz]) (le_refl _), hps, hts]
  simp only [ByteArray.extract_extract]
  congr 1
  · congr 2 <;> omega
  · congr 1 <;> omega

theorem tail_size_arith (N n j slot : Nat) (hn : n ≤ N) (hj : j < n) :
    slot + ((N - n) * slot + j * slot) = slot * N + slot - (n - j) * slot := by
  have h : slot * N + slot = (N - n) * slot + j * slot + slot + (n - j) * slot := by
    have e : N + 1 = (N - n) + j + 1 + (n - j) := by omega
    calc slot * N + slot = (N + 1) * slot := by ring
      _ = ((N - n) + j + 1 + (n - j)) * slot := by rw [← e]
      _ = _ := by ring
  omega

/-- Hop `i`'s keys, as `createKEMHeader` derives them from the hop's seed. -/
def kemHopKeys (kem : KEM) (kdfS : KDF) (path : Array PathHop)
    (seeds : Array (Vector UInt8 32)) (i : Nat) : HopKeys :=
  match kemEncap kem (path[i]!).publicKey (seeds[i]!) with
  | .ok (_, ss) => deriveHopKeys kdfS ss
  | .error _ => deriveHopKeys kdfS (ofVector (kem.encodePlaintext kem.ptI.default))

/-- A hop's header keystream: one routing-info block longer than the routing info. -/
def headerKeystream (streamS : StreamCipher) (geom : Geometry) (k : HopKeys) : ByteArray :=
  streamS.keystream (ofVector k.headerEncryption) (ofVector k.headerEncryptionIV)
    (geom.routingInfoLength + geom.perHopRoutingInfoLength)

/-- The one block of hop `i`'s header keystream that reaches the end of the routing info once
the first hop has processed the packet. Hop 0's is the last block of its keystream, which
masks nothing the first hop receives. -/
def tailPadBlock (streamS : StreamCipher) (geom : Geometry) (k : HopKeys) (i : Nat) : ByteArray :=
  (headerKeystream streamS geom k).extract
    (geom.routingInfoLength + geom.perHopRoutingInfoLength - (i + 1) * geom.perHopRoutingInfoLength)
    (geom.routingInfoLength + geom.perHopRoutingInfoLength - i * geom.perHopRoutingInfoLength)

/-- The XOR of `tailPadBlock` over hops `0` to `i`. -/
def tailPad (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (path : Array PathHop) (seeds : Array (Vector UInt8 32)) : Nat → ByteArray
  | 0 => tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds 0) 0
  | i + 1 => xorBytes (tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds (i + 1)) (i + 1))
      (tailPad kem kdfS streamS geom path seeds i)

/-- The filler with which the rest of the path yields the packet the first hop forwards: the
original filler, then `tailPad` over the whole path. -/
def tailFiller (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) : ByteArray :=
  (if geom.nrHops > path.size then filler else ByteArray.empty)
    ++ tailPad kem kdfS streamS geom path seeds (path.size - 1)

/-- A hop's routing-info fragment is the same on the rest of the path, one index down. -/
theorem kemRiFragment_tail (kem : KEM) (geom : Geometry) (path : Array PathHop)
    (kemElements : Array ByteArray) (macBytes : ByteArray) (i : Nat) (hi : i + 1 < path.size)
    (hkn : kemElements.size = path.size) :
    kemRiFragment kem geom (path.extract 1 path.size) (kemElements.extract 1 kemElements.size)
        macBytes (path.size - 1) i
      = kemRiFragment kem geom path kemElements macBytes path.size (i + 1) := by
  have hp : (path.extract 1 path.size)[i]! = path[i + 1]! := by
    rw [getElem!_extract_from path 1 i (by omega), Nat.add_comm]
  unfold kemRiFragment
  by_cases ht : i + 1 = path.size - 1
  · have ht' : i = path.size - 1 - 1 := by omega
    simp [hp, ht, ← ht']
  · have hp2 : (path.extract 1 path.size)[i + 1]! = path[i + 1 + 1]! := by
      rw [getElem!_extract_from path 1 (i + 1) (by omega), Nat.add_comm]
    have hk2 : (kemElements.extract 1 kemElements.size)[i + 1]! = kemElements[i + 1 + 1]! := by
      rw [getElem!_extract_from kemElements 1 (i + 1) (by omega), Nat.add_comm]
    have hb1 : (i == path.size - 1 - 1) = false := by simp; omega
    have hb2 : (i + 1 == path.size - 1) = false := by simp; omega
    simp only [hp, hp2, hk2, hb1, hb2]

/-- `tailPad`, from each hop's header keystream. -/
def tailPadOf (geom : Geometry) (ks : ℕ → ByteArray) : ℕ → ByteArray
  | 0 => (ks 0).extract
      (geom.routingInfoLength + geom.perHopRoutingInfoLength
        - (0 + 1) * geom.perHopRoutingInfoLength)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength - 0 * geom.perHopRoutingInfoLength)
  | i + 1 => xorBytes ((ks (i + 1)).extract
      (geom.routingInfoLength + geom.perHopRoutingInfoLength
        - (i + 1 + 1) * geom.perHopRoutingInfoLength)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength
        - (i + 1) * geom.perHopRoutingInfoLength)) (tailPadOf geom ks i)

theorem tailPadOf_kemHopKeys (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (i : ℕ) :
    tailPadOf geom (fun m => headerKeystream streamS geom (kemHopKeys kem kdfS path seeds m)) i
      = tailPad kem kdfS streamS geom path seeds i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [tailPadOf, tailPad, ih, tailPadBlock]

/-- `tailPadOf` reads the keystreams of the hops up to `i` only. -/
theorem tailPadOf_congr (geom : Geometry) (ks ks' : ℕ → ByteArray) (i : ℕ)
    (h : ∀ m ≤ i, ks m = ks' m) : tailPadOf geom ks i = tailPadOf geom ks' i := by
  induction i with
  | zero => simp only [tailPadOf, h 0 le_rfl]
  | succ i ih =>
    simp only [tailPadOf, h (i + 1) le_rfl, ih fun m hm => h m (Nat.le_succ_of_le hm)]

/-- `tailPadOf` is one routing-info block wide. -/
theorem tailPadOf_size (geom : Geometry) (ks : ℕ → ByteArray) (i : ℕ)
    (hks : ∀ m ≤ i, (ks m).size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hle : (i + 1) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength + geom.perHopRoutingInfoLength) :
    (tailPadOf geom ks i).size = geom.perHopRoutingInfoLength := by
  cases i with
  | zero =>
    simp only [tailPadOf, ByteArray.size_extract, hks 0 le_rfl]
    omega
  | succ i =>
    have hsm : (i + 1 + 1) * geom.perHopRoutingInfoLength
        = (i + 1) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength :=
      Nat.succ_mul _ _
    simp only [tailPadOf, size_xorBytes, ByteArray.size_extract, hks (i + 1) le_rfl]
    omega

/-- The converse of `newKEMPacketFrom_unfold`. -/
theorem newKEMPacketFrom_fold (kem : KEM) (cipher : WideBlockCipher) (macS : MAC)
    (streamS : StreamCipher) (geom : Geometry) (kemElements : Array ByteArray)
    (keys : Array HopKeys) (filler : ByteArray) (path : Array PathHop) (payload hdr : ByteArray)
    (sprpKeys : Array SPRPKey) (hpay : payload.size = geom.forwardPayloadLength)
    (hcreate : createKEMHeaderFrom kem macS streamS geom kemElements keys filler path
      = Except.ok (hdr, sprpKeys)) :
    newKEMPacketFrom kem cipher macS streamS geom kemElements keys filler path payload
      = Except.ok (hdr ++ (List.range' 0 sprpKeys.size).foldl (payloadEncryptStep cipher sprpKeys)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)) := by
  unfold newKEMPacketFrom
  dsimp only
  split
  case isTrue hc => exact absurd hpay hc
  case isFalse =>
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
    rw [hcreate]
    rfl

set_option maxHeartbeats 4000000 in
/-- **The forwarded packet is a fresh packet on the rest of the path, for any keys.** When the
first hop unwraps a packet `newKEMPacketFrom` built, and its own ciphertext and keys come from an
encapsulation to it, it gets its own commands and the next hop's name, and what it forwards is
the packet `newKEMPacketFrom` builds on the rest of the path from the remaining ciphertexts and
keys, with the old filler followed by one more block (`tailPadOf`). The keys of the later hops
are arbitrary. -/
theorem newKEMPacketFrom_unwrapKEM (kem : KEM) (cipher : WideBlockCipher) (macS : MAC)
    (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (kemElements : Array ByteArray) (keys : Array HopKeys) (filler : ByteArray)
    (path : Array PathHop) (payload pkt privKey : ByteArray)
    (hple : path.size ≤ geom.nrHops)
    (hfsize : geom.nrHops > path.size →
      filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hknsize : kemElements.size = path.size) (hkeysArrSize : keys.size = path.size)
    (hksize : ∀ j (hj : j < kemElements.size), (kemElements[j]'hj).size = kem.ciphertextSize)
    (hpp : kemSelfPublicKeyBytes kem privKey = (path[0]!).publicKey)
    (hkey : ∃ seed ss, kem.Reliable (kem.stateFromSeed seed) ∧
      kemEncap kem (path[0]!).publicKey seed = Except.ok (kemElements[0]!, ss) ∧
      keys[0]! = deriveHopKeys kdfS ss)
    (hcmdnn : ∀ c ∈ (path[0]!).commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ (path[0]!).commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (hnk : newKEMPacketFrom kem cipher macS streamS geom kemElements keys filler path payload
      = Except.ok pkt) :
    (2 ≤ path.size →
      ∃ (replayTag mac : Vector UInt8 32) (fwd : Vector UInt8 pkt.size),
        unwrapKEM kem cipher macS kdfS streamS geom privKey pkt
          = Except.ok (none, replayTag,
              (path[0]!).commands ++ [RoutingCommand.nextNodeHop (path[1]!).id mac], some fwd) ∧
        newKEMPacketFrom kem cipher macS streamS geom (kemElements.extract 1 kemElements.size)
            (keys.extract 1 keys.size)
            ((if geom.nrHops > path.size then filler else ByteArray.empty)
        ++ tailPadOf geom (fun i => headerKeystream streamS geom (keys[i]!)) (path.size - 1))
            (path.extract 1 path.size) payload
          = Except.ok (ofVector fwd)) ∧
    (path.size = 1 →
      ∃ replayTag : Vector UInt8 32, unwrapKEM kem cipher macS kdfS streamS geom privKey pkt
        = Except.ok (some (if hasSurbReply (path[0]!).commands
            then (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload else payload),
          replayTag, (path[0]!).commands, none)) := by
  obtain ⟨hpaysize, hdr, sprpKeys, t, hcreate, ht0content, htstep, hpkteq⟩ :=
    newKEMPacketFrom_unfold kem cipher macS streamS geom kemElements keys filler path payload pkt
      hnk
  obtain ⟨riKeyStream, riPadding, s, hriKSarrSize, hriPadArrSize, hriContent, hs0eq, hstep,
    hhdreq, hsprpeq⟩ :=
    createKEMHeaderFrom_unfold kem macS streamS geom kemElements keys filler path hdr sprpKeys
      hcreate
  obtain ⟨hnnh, hperhopEq, hrouting, hheader, hpacket, -⟩ := id hvalid
  have hperhop : geom.nextNodeHopLength + kem.ciphertextSize ≤ geom.perHopRoutingInfoLength := by
    omega
  have hsprp : sprpKeys.size = path.size := by rw [hsprpeq]; simp
  have hriKScontent : ∀ i (_hi : i < path.size), riKeyStream[i]! =
      (streamS.keystream (ofVector (keys[i]!).headerEncryption) (ofVector (keys[i]!).headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength) :=
    fun i hi => (hriContent i hi).1
  have hriPadcontent : ∀ i (_hi : i < path.size), riPadding[i]! =
      (let totalRiLen := geom.routingInfoLength + geom.perHopRoutingInfoLength
       let ks := streamS.keystream (ofVector (keys[i]!).headerEncryption)
         (ofVector (keys[i]!).headerEncryptionIV) totalRiLen
       let ksLen := totalRiLen - (i + 1) * geom.perHopRoutingInfoLength
       let thisPad0 := ks.extract ksLen totalRiLen
       if i > 0 then
         xorBytes (thisPad0.extract 0 riPadding[i - 1]!.size) riPadding[i - 1]!
           ++ thisPad0.extract riPadding[i - 1]!.size thisPad0.size
       else thisPad0) :=
    fun i hi => (hriContent i hi).2
  have hle : ∀ j (_hj : j < path.size), (j + 1) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength + geom.perHopRoutingInfoLength := by
    intro j hj
    rw [hrouting]
    have h1 : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.perHopRoutingInfoLength * geom.nrHops := by
      rw [Nat.mul_comm geom.perHopRoutingInfoLength geom.nrHops]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hpadsize : ∀ i (_hi : i < path.size),
      riPadding[i]!.size = (i + 1) * geom.perHopRoutingInfoLength := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hc := hriPadcontent 0 hi
      dsimp only at hc
      rw [ite_eq_right (by omega)] at hc
      rw [hc, ByteArray.size_extract, streamS.keystream_size]
      have := hle 0 hi
      omega
    | succ i ih =>
      intro hi
      have hc := hriPadcontent (i + 1) hi
      dsimp only at hc
      rw [ite_eq_left (by omega : i + 1 > 0)] at hc
      have hihsize := ih (by omega)
      have hthis0size : ((streamS.keystream (ofVector keys[i + 1]!.headerEncryption)
          (ofVector keys[i + 1]!.headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract
          (geom.routingInfoLength + geom.perHopRoutingInfoLength
            - (i + 1 + 1) * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
          = (i + 1 + 1) * geom.perHopRoutingInfoLength := by
        rw [ByteArray.size_extract, streamS.keystream_size]
        have := hle (i + 1) hi
        omega
      rw [hc]
      simp only [ByteArray.size_append, size_xorBytes, ByteArray.size_extract, Nat.add_sub_cancel]
        at *
      omega
  have hs0size : (s 0).1.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength := by
    rw [hs0eq]
    split
    · next hc => rw [hfsize hc]
    · next hc =>
      have heq : geom.nrHops - path.size = 0 := by omega
      rw [heq, Nat.zero_mul]
      rfl
  have ht0size : (t 0).size = geom.payloadTagLength + geom.forwardPayloadLength := by
    rw [ht0content, ByteArray.size_append, hpaysize]
    simp [ByteArray.size]
  have hsprpkey : ∀ i (hi : i < sprpKeys.size), (sprpKeys[i]'hi).key = keys[i]!.payloadEncryption ∧
      (sprpKeys[i]'hi).iv = keys[i]!.headerEncryptionIV := by
    intro i hi
    simp only [hsprpeq, Array.getElem_ofFn]
    trivial
  have htsize := newKEMPacket_payload_size_trace cipher sprpKeys t htstep
  have hpkteq2 : pkt = hopPacket kemElements riPadding s t path.size 0 := by
    rw [hpkteq, hhdreq]
    unfold hopPacket
    rw [Nat.sub_zero, ite_eq_right (lt_irrefl 0), ByteArray.append_empty, hsprp]
  subst hpkteq2
  refine ⟨fun h2 => ?_, fun h1 => ⟨_, unwrapKEM_hopPacket_terminal kem cipher
    macS kdfS streamS geom path keys kemElements riKeyStream riPadding sprpKeys path.size s t
    hvalid hmactag hs0size hstep hknsize hksize hpadsize hriKScontent hriPadcontent
    htsize ht0size htstep hsprpkey hsprp hple h16 0 (by omega) hcmdnn hcmdnh payload
    hpaysize ht0content privKey hpp hkey⟩⟩
  obtain ⟨replayTag, cmds, hnewsize, hunwrap, rfl⟩ := unwrapKEM_hopPacket_nonterminal kem cipher
    macS kdfS streamS geom path keys kemElements riKeyStream riPadding sprpKeys path.size s t
    hvalid hmactag hs0size hstep hknsize hksize hpadsize hriKScontent hriPadcontent
    htsize ht0size htstep hsprpkey hsprp hple h16 0 (by omega) hcmdnn hcmdnh privKey hpp
    hkey
  refine ⟨replayTag, _,
    ⟨(hopPacket kemElements riPadding s t path.size (0 + 1)).data, hnewsize⟩, hunwrap, ?_⟩
  show newKEMPacketFrom kem cipher macS streamS geom (kemElements.extract 1 kemElements.size)
      (keys.extract 1 keys.size)
      ((if geom.nrHops > path.size then filler else ByteArray.empty)
        ++ tailPadOf geom (fun i => headerKeystream streamS geom (keys[i]!)) (path.size - 1))
      (path.extract 1 path.size) payload
    = Except.ok (hopPacket kemElements riPadding s t path.size (0 + 1))
  -- Indexing on the rest of the path.
  have hps : (path.extract 1 path.size).size = path.size - 1 := by simp
  have hkeget : ∀ i, i + 1 < path.size →
      (kemElements.extract 1 kemElements.size)[i]! = kemElements[i + 1]! :=
    fun i hi => by rw [getElem!_extract_from kemElements 1 i (by omega), Nat.add_comm]
  have hkget : ∀ i, i + 1 < path.size → (keys.extract 1 keys.size)[i]! = keys[i + 1]! :=
    fun i hi => by rw [getElem!_extract_from keys 1 i (by omega), Nat.add_comm]
  have hkssize : ∀ k : HopKeys, (streamS.keystream (ofVector k.headerEncryption)
      (ofVector k.headerEncryptionIV)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
      = geom.routingInfoLength + geom.perHopRoutingInfoLength :=
    fun k => streamS.keystream_size _ _ _
  have hslotle : ∀ i, geom.perHopRoutingInfoLength ≤ (i + 1) * geom.perHopRoutingInfoLength :=
    fun i => Nat.le_mul_of_pos_left _ (by omega)
  -- The first block of each cascaded padding is `tailPad`.
  have hpadhead : ∀ i, i < path.size →
      (riPadding[i]!).extract 0 geom.perHopRoutingInfoLength
        = tailPadOf geom (fun i => headerKeystream streamS geom (keys[i]!)) i := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hc := hriPadcontent 0 hi
      dsimp only at hc
      rw [ite_eq_right (by omega)] at hc
      have hle0 := hle 0 hi
      have h01 : (0 + 1) * geom.perHopRoutingInfoLength = geom.perHopRoutingInfoLength := by simp
      have h00 : 0 * geom.perHopRoutingInfoLength = 0 := by simp
      rw [hc, ByteArray.extract_extract]
      show _ = (headerKeystream streamS geom (keys[0]!)).extract _ _
      unfold headerKeystream
      congr 1
      omega
    | succ i ih =>
      intro hi
      have hc := hriPadcontent (i + 1) hi
      dsimp only at hc
      rw [ite_eq_left (by omega : i + 1 > 0)] at hc
      simp only [Nat.add_sub_cancel] at hc
      have hPs := hpadsize i (by omega)
      have hle1 := hle (i + 1) hi
      have hsm : (i + 1 + 1) * geom.perHopRoutingInfoLength
          = (i + 1) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength :=
        Nat.succ_mul _ _
      have hsl := hslotle i
      rw [hc, pad_extract_head _ _ _ (by rw [hPs]; exact hsl)
        (by rw [hPs, ByteArray.size_extract, hkssize]; omega), ih (by omega),
        ByteArray.extract_extract]
      show _ = xorBytes ((headerKeystream streamS geom (keys[i + 1]!)).extract _ _)
        (tailPadOf geom (fun i => headerKeystream streamS geom (keys[i]!)) i)
      congr 1
      unfold headerKeystream
      congr 1
      omega
  -- The arrays and trace of `createKEMHeader` on the rest of the path.
  let RKS' : Array ByteArray := Array.ofFn (fun i : Fin (path.size - 1) =>
    (streamS.keystream (ofVector (keys[i.val + 1]!).headerEncryption)
      (ofVector (keys[i.val + 1]!).headerEncryptionIV)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength)
        - (i.val + 1) * geom.perHopRoutingInfoLength))
  let RP' : Array ByteArray := Array.ofFn (fun i : Fin (path.size - 1) =>
    (riPadding[i.val + 1]!).extract geom.perHopRoutingInfoLength (riPadding[i.val + 1]!).size)
  let s' : Nat → ByteArray × ByteArray := fun j =>
    ((s j).1 ++ (riPadding[path.size - 1 - j]!).extract 0 geom.perHopRoutingInfoLength, (s j).2)
  have hRKSget : ∀ i (_hi : i < path.size - 1), RKS'[i]! =
      (streamS.keystream (ofVector (keys[i + 1]!).headerEncryption)
        (ofVector (keys[i + 1]!).headerEncryptionIV)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength)
          - (i + 1) * geom.perHopRoutingInfoLength) := by
    intro i hi
    rw [getElem!_pos RKS' i (by simp [RKS']; exact hi)]
    simp [RKS']
  have hRPget : ∀ i (_hi : i < path.size - 1), RP'[i]! =
      (riPadding[i + 1]!).extract geom.perHopRoutingInfoLength (riPadding[i + 1]!).size := by
    intro i hi
    rw [getElem!_pos RP' i (by simp [RP']; exact hi)]
    simp [RP']
  have hcreate' := createKEMHeaderFrom_fold kem macS streamS geom
    (kemElements.extract 1 kemElements.size) (keys.extract 1 keys.size)
    ((if geom.nrHops > path.size then filler else ByteArray.empty)
        ++ tailPadOf geom (fun i => headerKeystream streamS geom (keys[i]!)) (path.size - 1))
    (path.extract 1 path.size) RKS' RP' s' (by simp [RKS']) (by simp [RP'])
    (by
      intro i hi
      rw [hps] at hi
      refine ⟨?_, ?_⟩
      · rw [hRKSget i hi, hkget i (by omega)]
      · dsimp only
        rw [hRPget i hi, hkget i (by omega)]
        have hc := hriPadcontent (i + 1) (by omega)
        dsimp only at hc
        rw [ite_eq_left (by omega : i + 1 > 0)] at hc
        simp only [Nat.add_sub_cancel] at hc
        have hPs := hpadsize i (by omega)
        have hRs := hpadsize (i + 1) (by omega)
        have hle1 := hle (i + 1) (by omega)
        have hsm : (i + 1 + 1) * geom.perHopRoutingInfoLength
            = (i + 1) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength :=
          Nat.succ_mul _ _
        have hsl := hslotle i
        obtain ⟨T, hT⟩ : ∃ T, T = (streamS.keystream (ofVector keys[i + 1]!.headerEncryption)
            (ofVector keys[i + 1]!.headerEncryptionIV)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (i + 1 + 1) * geom.perHopRoutingInfoLength)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength) := ⟨_, rfl⟩
        rw [← hT] at hc
        have hTs : T.size = (i + 1 + 1) * geom.perHopRoutingInfoLength := by
          rw [hT, ByteArray.size_extract, hkssize]; omega
        have hU : (streamS.keystream (ofVector keys[i + 1]!.headerEncryption)
            (ofVector keys[i + 1]!.headerEncryptionIV)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (i + 1) * geom.perHopRoutingInfoLength)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)
            = T.extract geom.perHopRoutingInfoLength T.size := by
          rw [hTs, hT, ByteArray.extract_extract]
          congr 1 <;> omega
        have hcs : (riPadding[i + 1]!).size = T.size := by rw [hRs, hTs]
        rw [hU, hcs]
        by_cases hi0 : i > 0
        · rw [ite_eq_left hi0, hRPget (i - 1) (by omega), show i - 1 + 1 = i from by omega, hc]
          exact pad_extract_tail T _ _ (by rw [hPs]; exact hsl) (by rw [hPs, hTs]; omega)
        · have hi00 : i = 0 := by omega
          subst hi00
          have hP1 : (riPadding[0]!).size = geom.perHopRoutingInfoLength := by
            rw [hPs]; simp
          rw [ite_eq_right hi0, hc, Cryptlib.Util.Bytes.extract_append_of_ge _ _
            (by rw [size_xorBytes, ByteArray.size_extract, hP1]; omega),
            ByteArray.extract_extract, size_xorBytes, ByteArray.size_extract, hP1]
          congr 1 <;> omega)
    (by
      show s' 0 = _
      rw [ite_eq_left (by rw [hps]; omega)]
      show ((s 0).1 ++ (riPadding[path.size - 1 - 0]!).extract 0
        geom.perHopRoutingInfoLength, (s 0).2) = _
      rw [Nat.sub_zero,
        hpadhead (path.size - 1) (by omega), hs0eq])
    (by
      intro j hj
      rw [hps] at hj
      obtain ⟨frag, hfrag, h1, h2⟩ := hstep j (by omega)
      have hidx : path.size - 1 - 1 - j + 1 = path.size - 1 - j := by omega
      have hq : path.size - 1 - j - 1 = path.size - 1 - 1 - j := by omega
      rw [hq] at h2
      have hi1 : path.size - 1 - j < path.size := by omega
      have hPq := hpadsize (path.size - 1 - 1 - j) (by omega)
      have hslq := hslotle (path.size - 1 - 1 - j)
      refine ⟨frag, ?_, ?_, ?_⟩
      · show kemRiFragment kem geom (path.extract 1 path.size)
          (kemElements.extract 1 kemElements.size) (s j).2 (path.extract 1 path.size).size
          ((path.extract 1 path.size).size - 1 - j) = Except.ok frag
        rw [hps, kemRiFragment_tail kem geom path kemElements (s j).2 (path.size - 1 - 1 - j)
          (by omega) hknsize, hidx]
        exact hfrag
      · show (s (j + 1)).1 ++ (riPadding[path.size - 1 - (j + 1)]!).extract 0
            geom.perHopRoutingInfoLength
          = xorBytes (frag ++ ((s j).1 ++ (riPadding[path.size - 1 - j]!).extract 0
              geom.perHopRoutingInfoLength)) (RKS'[(path.extract 1 path.size).size - 1 - j]!)
        rw [hps, hRKSget (path.size - 1 - 1 - j) (by omega), hidx,
          show path.size - 1 - (j + 1) = path.size - 1 - 1 - j from by omega]
        -- The padding recurrence at hop `path.size - 1 - j`.
        have hc := hriPadcontent (path.size - 1 - j) hi1
        dsimp only at hc
        rw [ite_eq_left (by omega : path.size - 1 - j > 0), hq] at hc
        have hle1 := hle (path.size - 1 - j) hi1
        have hsm : (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength
            = (path.size - 1 - j) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength :=
          Nat.succ_mul _ _
        have hqm : (path.size - 1 - 1 - j + 1) * geom.perHopRoutingInfoLength
            = (path.size - 1 - j) * geom.perHopRoutingInfoLength := by rw [hidx]
        have hPq' := hPq
        rw [hqm] at hPq'
        have hslq' := hslq
        rw [hqm] at hslq'
        have hPi := hpadsize (path.size - 1 - j) hi1
        have hYj : (riPadding[path.size - 1 - j]!).extract 0 geom.perHopRoutingInfoLength
            = xorBytes ((streamS.keystream (ofVector keys[path.size - 1 - j]!.headerEncryption)
                (ofVector keys[path.size - 1 - j]!.headerEncryptionIV)
                (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract
                (geom.routingInfoLength + geom.perHopRoutingInfoLength
                  - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)
                (geom.routingInfoLength + geom.perHopRoutingInfoLength
                  - (path.size - 1 - j) * geom.perHopRoutingInfoLength))
              ((riPadding[path.size - 1 - 1 - j]!).extract 0 geom.perHopRoutingInfoLength) := by
          rw [hc, pad_extract_head _ _ _ (by rw [hPq]; exact hslq)
            (by rw [hPq', ByteArray.size_extract, hkssize]; omega), ByteArray.extract_extract]
          congr 2
          omega
        have hfragsize : frag.size = geom.perHopRoutingInfoLength :=
          kemRiFragment_size kem geom path kemElements (s j).2 path.size (path.size - 1 - j) hi1
            hperhop hnnh hknsize hksize frag hfrag
        have hsj := (createKEMHeader_s_size kem macS geom path keys kemElements riKeyStream
          riPadding path.size s hperhop hnnh hknsize hksize hstep j (by omega)).1
        have harith := tail_size_arith geom.nrHops path.size j geom.perHopRoutingInfoLength hple
          (by omega)
        rw [extract_split _ (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j) * geom.perHopRoutingInfoLength) (by omega)
            (by rw [hkssize]; omega),
          ← ByteArray.append_assoc,
          xorBytes_append _ _ _ _
            (by
              rw [ByteArray.size_append, hfragsize, hsj, hs0size, ByteArray.size_extract, hkssize,
                hrouting]
              have e : path.size - 1 - j + 1 = path.size - j := by omega
              rw [e]
              rw [hrouting] at hle1
              rw [e] at hle1
              omega)
            (by
              rw [ByteArray.size_extract, ByteArray.size_extract, hkssize, hPi]
              omega),
          ← hriKScontent (path.size - 1 - j) hi1, ← h1]
        congr 1
        rw [hYj.trans (xorBytes_comm_of_size_eq _ _
          (by
            rw [ByteArray.size_extract, ByteArray.size_extract, hkssize, hPq']
            omega)), xorBytes_xorBytes]
      · show (s (j + 1)).2 = ofVector (macS.mac
          (ofVector ((keys.extract 1 keys.size)[(path.extract 1 path.size).size - 1 - j]!).headerMAC)
          (v0AD ++ (kemElements.extract 1 kemElements.size)[(path.extract 1 path.size).size - 1 - j]!
            ++ ((s (j + 1)).1 ++ (riPadding[path.size - 1 - (j + 1)]!).extract 0
              geom.perHopRoutingInfoLength)
            ++ (if (path.extract 1 path.size).size - 1 - j > 0
                then RP'[(path.extract 1 path.size).size - 1 - j - 1]! else ByteArray.empty)))
        rw [hps, hkget _ (by omega), hkeget _ (by omega), hidx,
          show path.size - 1 - (j + 1) = path.size - 1 - 1 - j from by omega, h2,
          ite_eq_left (by omega : path.size - 1 - j > 0)]
        have hYZ : (riPadding[path.size - 1 - 1 - j]!).extract 0 geom.perHopRoutingInfoLength
            ++ (if path.size - 1 - 1 - j > 0 then RP'[path.size - 1 - 1 - j - 1]!
                else ByteArray.empty) = riPadding[path.size - 1 - 1 - j]! := by
          by_cases hq0 : path.size - 1 - 1 - j > 0
          · rw [ite_eq_left hq0, hRPget (path.size - 1 - 1 - j - 1) (by omega),
              show path.size - 1 - 1 - j - 1 + 1 = path.size - 1 - 1 - j from by omega]
            exact Cryptlib.Util.Bytes.append_extract _ _ (by rw [hPq]; exact hslq)
          · have hq00 : path.size - 1 - 1 - j = 0 := by omega
            have hP0 : (riPadding[0]!).size = geom.perHopRoutingInfoLength := by
              rw [hpadsize 0 (by omega)]; simp
            rw [ite_eq_right hq0, ByteArray.append_empty, hq00]
            conv_lhs => rw [← hP0]
            exact ByteArray.extract_zero_size
        simp only [ByteArray.append_assoc]
        rw [hYZ])
  rw [newKEMPacketFrom_fold kem cipher macS streamS geom _ _ _ _ payload _ _ hpaysize hcreate']
  congr 1
  unfold hopPacket
  have hfoldt : ∀ sprpT : Array SPRPKey, sprpT.size = path.size - 1 →
      (∀ k, k < path.size - 1 → sprpT[k]! = sprpKeys[k + 1]!) →
      List.foldl (payloadEncryptStep cipher sprpT)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)
        (List.range' 0 sprpT.size) = t (path.size - 1) := by
    intro sprpT hsz hget
    rw [hsz, ← ht0content]
    exact foldl_range'_trace _ t (path.size - 1) 0 (fun j hj => by
      rw [Nat.zero_add, htstep j (by omega)]
      unfold payloadEncryptStep
      rw [hsz, hsprp, hget _ (by omega),
        show path.size - 1 - 1 - j + 1 = path.size - 1 - j from by omega])
  have hP0 : (riPadding[0]!).size = geom.perHopRoutingInfoLength := by
    rw [hpadsize 0 (by omega)]; simp
  have hY0 : (riPadding[0]!).extract 0 geom.perHopRoutingInfoLength = riPadding[0]! := by
    conv_lhs => rw [← hP0]
    exact ByteArray.extract_zero_size
  rw [hfoldt _ (by simp) (fun k hk => by
        rw [getElem!_pos _ k (by simp; omega), getElem!_pos sprpKeys (k + 1) (by omega)]
        simp only [hsprpeq, Array.getElem_ofFn]
        rw [hkget k (by omega)]),
    hps, hkeget 0 (by omega)]
  show v0AD ++ kemElements[0 + 1]! ++ ((s (path.size - 1)).1
      ++ (riPadding[path.size - 1 - (path.size - 1)]!).extract 0 geom.perHopRoutingInfoLength)
    ++ (s (path.size - 1)).2 ++ t (path.size - 1) = _
  rw [Nat.sub_self, hY0]
  rfl

/-- **The forwarded packet is a fresh packet on the rest of the path.** When the first hop
unwraps a packet `newKEMPacket` built, it gets its own commands and the next hop's name, and what
it forwards is exactly the packet `newKEMPacket` builds on the rest of the path, from the
remaining seeds and with the filler `tailFiller`. The only hop of a one-hop path gets its
commands and the payload, with its tag still in front if the commands carry a SURB reply. -/
theorem newKEMPacket_unwrapKEM (kem : KEM) (cipher : WideBlockCipher) (macS : MAC)
    (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload pkt privKey : ByteArray)
    (hpp : kemSelfPublicKeyBytes kem privKey = (path[0]!).publicKey)
    (hrel : ∀ j, j < path.size → kem.Reliable (kem.stateFromSeed seeds[j]!))
    (hcmdnn : ∀ c ∈ (path[0]!).commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ (path[0]!).commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (hnk : newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload
      = Except.ok pkt) :
    (2 ≤ path.size →
      ∃ (replayTag mac : Vector UInt8 32) (fwd : Vector UInt8 pkt.size),
        unwrapKEM kem cipher macS kdfS streamS geom privKey pkt
          = Except.ok (none, replayTag,
              (path[0]!).commands ++ [RoutingCommand.nextNodeHop (path[1]!).id mac], some fwd) ∧
        newKEMPacket kem cipher macS kdfS streamS geom (seeds.extract 1 seeds.size)
            (tailFiller kem kdfS streamS geom path seeds filler) (path.extract 1 path.size) payload
          = Except.ok (ofVector fwd)) ∧
    (path.size = 1 →
      ∃ replayTag : Vector UInt8 32, unwrapKEM kem cipher macS kdfS streamS geom privKey pkt
        = Except.ok (some (if hasSurbReply (path[0]!).commands
            then (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload else payload),
          replayTag, (path[0]!).commands, none)) := by
  obtain ⟨-, hdr, sprpKeys, _t, hcreate, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom seeds filler path payload pkt hnk
  obtain ⟨hpne, hple, hesize, hfsize, kemElements, keys, _rks, _rp, _s, hknsize, hkeysArrSize,
    -, -, hkc, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom seeds filler path hdr sprpKeys hcreate
  have hfrom : newKEMPacketFrom kem cipher macS streamS geom kemElements keys filler path payload
      = Except.ok pkt := by
    rw [← newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom seeds filler path
      payload kemElements keys hpne hple hesize hfsize hknsize hkeysArrSize hkc]
    exact hnk
  have hksize : ∀ j (hj : j < kemElements.size),
      (kemElements[j]'hj).size = kem.ciphertextSize := by
    intro j hj
    obtain ⟨ct, ss, hk, hct, -⟩ := hkc j (by rwa [hknsize] at hj)
    have := kemEncap_size kem _ _ ct ss hk
    rwa [← hct, getElem!_pos kemElements j hj] at this
  obtain ⟨ct0, ss0, hk0, hct0, hkeq0⟩ := hkc 0 (by omega)
  obtain ⟨h2, h1⟩ := newKEMPacketFrom_unwrapKEM kem cipher macS kdfS streamS geom hvalid hmactag
    h16 kemElements keys filler path payload pkt privKey hple hfsize hknsize hkeysArrSize
    hksize hpp ⟨seeds[0]!, ss0, hrel 0 (by omega), hct0 ▸ hk0, hkeq0⟩ hcmdnn hcmdnh hfrom
  refine ⟨fun hn => ?_, h1⟩
  obtain ⟨replayTag, mac, fwd, hun, hfwd⟩ := h2 hn
  refine ⟨replayTag, mac, fwd, hun, ?_⟩
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hps : (path.extract 1 path.size).size = path.size - 1 := by simp
  have hpadeq : tailPadOf geom (fun i => headerKeystream streamS geom (keys[i]!)) (path.size - 1)
      = tailPad kem kdfS streamS geom path seeds (path.size - 1) := by
    rw [← tailPadOf_kemHopKeys]
    refine tailPadOf_congr geom _ _ _ fun m hm => ?_
    obtain ⟨ct, ss, hk, -, hkeq⟩ := hkc m (by omega)
    show headerKeystream streamS geom (keys[m]!)
      = headerKeystream streamS geom (kemHopKeys kem kdfS path seeds m)
    unfold kemHopKeys
    rw [hk, hkeq]
  have hpad1 : (tailPad kem kdfS streamS geom path seeds (path.size - 1)).size
      = geom.perHopRoutingInfoLength := by
    rw [← tailPadOf_kemHopKeys]
    refine tailPadOf_size geom _ _ (fun m _ => streamS.keystream_size _ _ _) ?_
    rw [Nat.sub_add_cancel (by omega), hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact le_trans (Nat.mul_le_mul_right _ hple) (Nat.le_add_right _ _)
  have hF : (if geom.nrHops > path.size then filler else ByteArray.empty).size
      = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength := by
    split
    · next hc => exact hfsize hc
    · next hc =>
      rw [show geom.nrHops - path.size = 0 by omega, Nat.zero_mul]
      rfl
  rw [hpadeq] at hfwd
  rw [newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom
    (seeds.extract 1 seeds.size) (tailFiller kem kdfS streamS geom path seeds filler)
    (path.extract 1 path.size) payload (kemElements.extract 1 kemElements.size)
    (keys.extract 1 keys.size) (by rw [hps]; omega) (by rw [hps]; omega) (by simp [hesize])
    (by
      intro _
      unfold tailFiller
      rw [ByteArray.size_append, hpad1, hps, hF,
        show geom.nrHops - (path.size - 1) = (geom.nrHops - path.size) + 1 from by omega,
        Nat.add_mul, Nat.one_mul])
    (by simp [hknsize]) (by simp [hkeysArrSize])
    (by
      intro i hi
      rw [hps] at hi
      obtain ⟨ct, ss, hk, hcteq, hkeq⟩ := hkc (i + 1) (by omega)
      refine ⟨ct, ss, ?_, ?_, ?_⟩
      · rw [getElem!_extract_from path 1 i (by omega), getElem!_extract_from seeds 1 i (by omega),
          Nat.add_comm 1 i]
        exact hk
      · rw [getElem!_extract_from kemElements 1 i (by omega), Nat.add_comm 1 i]
        exact hcteq
      · rw [getElem!_extract_from keys 1 i (by omega), Nat.add_comm 1 i]
        exact hkeq)]
  exact hfwd

open Cryptlib.Protocols.Sphinx.Interface (SeedStream nextSeed drawBytes seedBytes fillerLength)

/-- `get!` inside the array is `getElem`. -/
theorem get!_eq_getElem (x : ByteArray) (j : Nat) (h : j < x.size) : x.get! j = x[j]'h := by
  obtain ⟨bs⟩ := x
  show bs[j]! = _
  rw [getElem!_pos bs j h]
  rfl

/-- A seed stream whose seeds from `base` on are the 32-byte chunks of `b` yields `b`. -/
theorem seedBytes_chunks (b : ByteArray) (str : Nat → Vector UInt8 32) (base : Nat)
    (hstr : ∀ k, str (base + k) = toVec32 (b.extract (32 * k) (32 * k + 32))) :
    seedBytes str base b.size = b := by
  apply ByteArray.ext_getElem
  · exact Cryptlib.Protocols.Sphinx.Interface.seedBytes_size str base b.size
  · intro i hi hi'
    unfold seedBytes
    show (Array.ofFn fun k : Fin b.size =>
      (str (base + k.val / 32))[k.val % 32]'(Nat.mod_lt _ (by decide)))[i]'(by simpa using hi')
        = b[i]'hi'
    rw [Array.getElem_ofFn, hstr]
    show (Vector.ofFn fun j : Fin 32 => (b.extract (32 * (i / 32)) (32 * (i / 32) + 32)).get! j.val)[i % 32]'(Nat.mod_lt _ (by decide))
      = b[i]'hi'
    rw [Vector.getElem_ofFn]
    have hlt : i % 32 < (b.extract (32 * (i / 32)) (32 * (i / 32) + 32)).size := by
      rw [ByteArray.size_extract]
      have := Nat.div_add_mod i 32
      have := Nat.mod_lt i (by decide : 32 > 0)
      omega
    rw [get!_eq_getElem _ _ hlt, ByteArray.getElem_extract]
    congr 1
    exact Nat.div_add_mod i 32

set_option maxHeartbeats 1000000 in
/-- **`newKEMPacket_unwrapKEM` for `wrapKEM`.** What the first hop forwards from a wrapped
packet is what `wrapKEM` itself returns on the rest of the path, from some seed stream. -/
theorem wrapKEM_unwrapKEM_tail (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
    (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hop0 : PathHop) (rest : List PathHop) (privKey : ByteArray)
    (payload : Vector UInt8 geom.forwardPayloadLength) (st : SeedStream)
    (pkt : Vector UInt8 geom.packetLength) (st' : SeedStream) (hrest : rest ≠ [])
    (hrel : ∀ j, kem.Reliable (kem.stateFromSeed (st.2 (st.1 + j))))
    (hpp : kemSelfPublicKeyBytes kem privKey = hop0.publicKey)
    (hcmds : ∀ c ∈ hop0.commands,
      c ≠ RoutingCommand.null ∧ ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (hwrap : wrapKEM kem cipher macS kdfS streamS geom (hop0 :: rest) payload st = .ok pkt st') :
    ∃ (replayTag : Vector UInt8 32) (cmds : List RoutingCommand)
      (fwd : Vector UInt8 (ofVector pkt).size) (st0 st1 : SeedStream)
      (fresh : Vector UInt8 geom.packetLength),
      unwrapKEM kem cipher macS kdfS streamS geom privKey (ofVector pkt)
        = Except.ok (none, replayTag, cmds, some fwd) ∧
      wrapKEM kem cipher macS kdfS streamS geom rest payload st0 = .ok fresh st1 ∧
      ofVector fresh = ofVector fwd := by
  obtain ⟨i, str⟩ := st
  obtain ⟨seeds, hseedsize, hseedcontent, hnk⟩ := wrapKEM_unfold kem cipher macS kdfS streamS geom
    (hop0 :: rest) payload i str pkt st' hwrap
  have hrpos : 0 < rest.length := List.length_pos_of_ne_nil hrest
  have hp0 : ((hop0 :: rest).toArray)[0]! = hop0 := by simp
  have hpext : (hop0 :: rest).toArray.extract 1 (hop0 :: rest).toArray.size = rest.toArray := by
    simp
  obtain ⟨replayTag, mac, fwd, hunwrap, htail⟩ := (newKEMPacket_unwrapKEM kem cipher macS
    kdfS streamS geom hvalid hmactag h16 seeds _ (hop0 :: rest).toArray (ofVector payload)
    (ofVector pkt) privKey (by rw [hp0]; exact hpp)
    (fun j hj => by rw [hseedcontent j (by simpa using hj)]; exact hrel j)
    (by rw [hp0]; exact fun c hc => (hcmds c hc).1)
    (by rw [hp0]; exact fun c hc => (hcmds c hc).2) hnk).1 (by simp; omega)
  rw [hpext] at htail
  obtain ⟨-, hdr, sprpKeys, t, hcreate, -, -, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hnk
  obtain ⟨-, hple, -, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ hdr sprpKeys hcreate
  obtain ⟨TF, hTF⟩ : ∃ TF, TF = tailFiller kem kdfS streamS geom (hop0 :: rest).toArray seeds
      (seedBytes str (i + (hop0 :: rest).toArray.size)
        (fillerLength geom (hop0 :: rest).length)) := ⟨_, rfl⟩
  rw [← hTF] at htail
  have hTFsize : TF.size = fillerLength geom rest.length := by
    obtain ⟨-, hdr', sprp', t', hcreate', -, -, -⟩ :=
      newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ htail
    obtain ⟨-, -, -, hfs', -⟩ :=
      createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ hdr' sprp' hcreate'
    have := hfs' (by simp at hple ⊢; omega)
    simpa [fillerLength] using this
  -- The seed stream of the fresh packet: the remaining seeds, then the filler in chunks.
  let str0 : Nat → Vector UInt8 32 := fun k =>
    if k < rest.length then str (i + 1 + k)
    else toVec32 (TF.extract (32 * (k - rest.length)) (32 * (k - rest.length) + 32))
  obtain ⟨seeds', hs'size, hs'eq, hs'content⟩ := arrayMapM_nextSeed_succeeds rest.toArray 0 str0
  have hseeds' : seeds' = seeds.extract 1 seeds.size := by
    apply Array.ext
    · simp [hs'size, hseedsize]
    · intro j h1 h2
      have hj : j < rest.length := by simpa [hs'size] using h1
      have e1 := hs'content j (by simpa using hj)
      rw [getElem!_pos seeds' j h1] at e1
      have e2 := hseedcontent (1 + j) (by simp; omega)
      rw [getElem!_pos seeds (1 + j) (by rw [hseedsize]; simp; omega)] at e2
      rw [e1, Array.getElem_extract, e2]
      show str0 (0 + j) = _
      simp only [str0, Nat.zero_add, ite_eq_left hj]
      congr 1
      omega
  have hfill : seedBytes str0 (0 + rest.toArray.size) (fillerLength geom rest.length) = TF := by
    rw [← hTFsize]
    exact seedBytes_chunks TF str0 _ (fun k => by
      show str0 (0 + rest.toArray.size + k) = _
      simp only [str0]
      rw [ite_eq_right (by simp)]
      simp)
  have hsz : (ofVector fwd).size = geom.packetLength := by
    rw [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector]
  refine ⟨replayTag, _, fwd, (0, str0),
    (0 + rest.toArray.size + (fillerLength geom rest.length + 31) / 32, str0),
    ⟨(ofVector fwd).data, hsz⟩, hunwrap, ?_, rfl⟩
  unfold wrapKEM
  dsimp only [Bind.bind, EStateM.bind]
  rw [hs'eq]
  dsimp only [drawBytes]
  rw [hfill, hseeds', htail]
  dsimp only
  rw [dite_eq_left hsz]
  rfl

/-- A `KEMSphinxScheme` for any `KEM`, MAC, KDF, stream cipher and wide-block cipher. -/
def kemSphinxSchemeOf (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
    (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) : KEMSphinxScheme :=
  { State := SeedStream
    PrivateKey := ByteArray
    Command := RoutingCommand
    geometry := geom
    stateI := ⟨Cryptlib.Protocols.Sphinx.Interface.initWith (fun _ => Vector.replicate 32 0)⟩
    cipher := cipher
    mac    := macS
    kdf    := kdfS
    stream := streamS
    derivePublicKey := kemSelfPublicKeyBytes kem
    wrap := wrapKEM kem cipher macS kdfS streamS geom
    unwrap := unwrapKEM kem cipher macS kdfS streamS geom
    newSURB := wrapKEMSURB kem macS kdfS streamS geom
    newPacketFromSURB := fun surb payload =>
      Cryptlib.Protocols.Sphinx.SURB.newPacketFromSURB cipher geom (ofVector surb) payload
    -- Every draw keeps clear of the KEM's decapsulation-failure event.
    unwrapReliable := fun st => ∀ j, kem.Reliable (kem.stateFromSeed (st.2 (st.1 + j)))
    unwrap_complete := fun path privKeys payload st pkt st' hpath hrel hpriv hcmds hsurb hwrap =>
      wrapKEM_unwrapKEM_complete_valid kem cipher macS kdfS streamS geom hvalid hmactag h16
        path privKeys payload st pkt st' hpath hpriv hcmds hsurb (fun j _ => hrel j) hwrap
    kem := kem
    unwrap_tail := fun hop0 rest privKey payload st pkt st' hrest hrel hpp hcmds hwrap =>
      wrapKEM_unwrapKEM_tail kem cipher macS kdfS streamS geom hvalid hmactag h16 hop0 rest
        privKey payload st pkt st' hrest hrel hpp hcmds hwrap }

/-- A `KEMSphinxScheme` for the KEM `geom.kemName` names, with AEZ, HMAC-SHA256,
HKDF-SHA256-Expand and AES-256-CTR. Rejects a `geom` that fails the validity checks. -/
def kemSphinxScheme (geom : Geometry) : Except String KEMSphinxScheme :=
  if geom.kemName.isEmpty then
    throw s!"sphinx: geometry scheme {geom.nikeName} is a NIKE, not a KEM"
  else
    let name := geom.kemName
    match Cryptlib.Primitives.KEM.byName name with
    | none => throw s!"sphinx: KEM scheme {name} not implemented"
    | some kem =>
      if hvalid : geom.ValidForKEM kem then
        if hmactag : Cryptlib.Primitives.MAC.HMAC.hmacSha256MAC.tagSize = macLength then
          if h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength then
            pure (kemSphinxSchemeOf kem Cryptlib.Primitives.WideBlockCipher.AEZ.aez
              Cryptlib.Primitives.MAC.HMAC.hmacSha256MAC
              Cryptlib.Primitives.KDF.HKDF.hkdfSha256Expand
              Cryptlib.Primitives.StreamCipher.AES256CTR.aes256CTR geom hvalid hmactag h16)
          else throw s!"sphinx: geometry's payload tag/forward payload too short for scheme {name}"
        else throw "sphinx: internal error: hmacSha256MAC.tagSize ≠ macLength"
      else throw s!"sphinx: geometry is not valid for KEM scheme {name}"

end Cryptlib.Protocols.Sphinx.KEMSphinx
