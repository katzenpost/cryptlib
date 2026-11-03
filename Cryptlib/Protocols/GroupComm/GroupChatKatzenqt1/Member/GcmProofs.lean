/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.CborProofs
import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Gcm

/-! # A message reads back as written

`decode_encode`: every message this client writes, in the array form or the map form, read back,
is the message it wrote. -/

namespace Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Gcm

open Cbor

/-- An introduction katzenqt accepts, with a name this client can write. -/
def IntroWF (i : Introduction) : Prop :=
  1 ≤ i.name.length ∧ i.name.length ≤ maxNameChars ∧ i.readCap.size = readCapSize
    ∧ i.name.utf8ByteSize < 2 ^ 64

/-! ## The map form -/

/-- A field this client writes and reads back. -/
def FieldWF : Field → Prop
  | .version n => n < 2 ^ 64
  | .hash b => b.size < 2 ^ 64
  | .msgType n => n < 2 ^ 64
  | .text s => s.utf8ByteSize < 2 ^ 64
  | .intro i => 1 ≤ i.name.length ∧ i.name.length ≤ maxNameChars ∧ i.readCap.size = readCapSize
      ∧ i.name.utf8ByteSize < 2 ^ 64
  | .other _ _ => False
  | .acks b | .numbers b | .introducedAt b => b.size < 2 ^ 64

theorem bytes_size (b : ByteArray) : b.data.toList.length = b.size := Array.length_toList

theorem readByteArray_bytes (b : ByteArray) (rest : List UInt8) (hb : b.size < 2 ^ 64) :
    readByteArray (bytes b.data.toList ++ rest) = some (b, rest) := by
  unfold readByteArray
  rw [readBytes_bytes _ _ (by rw [bytes_size]; exact hb)]
  rfl

theorem nullable_some {α : Type} (read : List UInt8 → Option (α × List UInt8)) (l : List UInt8)
    (a : α) (rest : List UInt8) (h : read l = some (a, rest)) (hn : isNull l = false) :
    nullable read l = some (some a, rest) := by
  simp [nullable, hn, h]

theorem isNull_cons (x : ℕ) (r : List UInt8) (hx : x < 246) : isNull (x.toUInt8 :: r) = false := by
  simp only [isNull, List.head?_cons]
  cases h : (some x.toUInt8 == some (0xf6 : UInt8))
  · rfl
  · have := congrArg UInt8.toNat (Option.some.inj (beq_iff_eq.1 h))
    simp at this
    omega

theorem isNull_header (m n : ℕ) (rest : List UInt8) (hm : m < 7) :
    isNull (header m n ++ rest) = false := by
  unfold header
  split_ifs <;> simp only [List.cons_append] <;> exact isNull_cons _ _ (by omega)

theorem byteArray_eta (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by simp

theorem readIntro_encodeIntro (i : Introduction) (rest : List UInt8)
    (hn : 1 ≤ i.name.length ∧ i.name.length ≤ maxNameChars ∧ i.readCap.size = readCapSize
      ∧ i.name.utf8ByteSize < 2 ^ 64) :
    readIntro (encodeIntro i ++ rest) = some (i, rest) := by
  obtain ⟨h1, h2, h3, h4⟩ := hn
  have hcap : i.readCap.data.toList.length < 2 ^ 64 := by
    rw [bytes_size, h3]; decide
  simp only [encodeIntro, List.append_assoc, readIntro, readHeader_header 5 2 _ (by omega) (by omega),
    Option.bind_eq_bind, Option.bind_some, ne_eq, not_true_eq_false, if_false]
  rw [show introEntries 2 = introEntries (0 + 1 + 1) from rfl]
  simp only [introEntries, readText_text "display_name" _ (by decide), Option.bind_eq_bind,
    Option.bind_some, if_true]
  simp only [readText_text i.name _ h4, Option.bind_some,
    readText_text "read_cap" _ (by decide)]
  simp [readBytes_bytes _ _ hcap, h1, h2, h3]

theorem readField_encodeField (f : Field) (hf : FieldWF f) (rest : List UInt8) :
    readField (encodeField f ++ rest) = some (some f, rest) := by
  cases f with
  | version n =>
    simp only [encodeField, List.append_assoc, readField, readText_text "version" _ (by decide)]
    simp [readUInt_uint n rest hf]
  | hash b =>
    simp only [encodeField, List.append_assoc, readField,
      readText_text "membership_hash" _ (by decide)]
    simp [readByteArray_bytes b rest hf]
  | msgType n =>
    simp only [encodeField, List.append_assoc, readField, readText_text "msg_type" _ (by decide)]
    simp [nullable_some _ _ n rest (readUInt_uint n rest hf) (isNull_header 0 n rest (by omega))]
  | text t =>
    simp only [encodeField, List.append_assoc, readField, readText_text "text" _ (by decide)]
    simp [nullable_some _ _ t rest (readText_text t rest hf)
      (by unfold Cbor.text; rw [List.append_assoc]; exact isNull_header 3 _ _ (by omega))]
  | intro i =>
    simp only [encodeField, List.append_assoc, readField,
      readText_text "introduction" _ (by decide)]
    simp [nullable_some _ _ i rest (readIntro_encodeIntro i rest hf)
      (by unfold encodeIntro; simp only [List.append_assoc]; exact isNull_header 5 _ _ (by omega))]
  | other k raw => exact absurd hf id
  | acks b =>
    simp only [encodeField, List.append_assoc, readField, readText_text "acks" _ (by decide)]
    simp [otherKeys, nullable_some _ _ b rest (readByteArray_bytes b rest hf)
      (by unfold bytes; rw [List.append_assoc]; exact isNull_header 2 _ _ (by omega))]
  | numbers b =>
    simp only [encodeField, List.append_assoc, readField, readText_text "numbers" _ (by decide)]
    simp [otherKeys, nullable_some _ _ b rest (readByteArray_bytes b rest hf)
      (by unfold bytes; rw [List.append_assoc]; exact isNull_header 2 _ _ (by omega))]
  | introducedAt b =>
    simp only [encodeField, List.append_assoc, readField,
      readText_text "introduced_at" _ (by decide)]
    simp [otherKeys, nullable_some _ _ b rest (readByteArray_bytes b rest hf)
      (by unfold bytes; rw [List.append_assoc]; exact isNull_header 2 _ _ (by omega))]

theorem readFields_flatMap : ∀ (fs : List Field) (acc : Acc) (rest : List UInt8),
    (∀ f ∈ fs, FieldWF f) →
    readFields fs.length acc (fs.flatMap encodeField ++ rest) = some (fs.foldl Acc.add acc, rest)
  | [], _, _, _ => rfl
  | f :: fs, acc, rest, h => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readFields,
      readField_encodeField f (h f List.mem_cons_self) _, Option.bind_eq_bind, Option.bind_some,
      List.foldl_cons]
    exact readFields_flatMap fs _ rest fun g hg => h g (List.mem_cons_of_mem _ hg)

/-- A message this client writes in the map form and reads back as it was. -/
structure MapWF (g : Gcm) : Prop where
  version : g.version ≤ mapVersion
  hash : g.membershipHash.size = hashSize
  msgType : g.msgType ≤ MsgType.control
  text : ∀ s ∈ g.text, s.utf8ByteSize < 2 ^ 64
  intro : ∀ i ∈ g.introduction, 1 ≤ i.name.length ∧ i.name.length ≤ maxNameChars
    ∧ i.readCap.size = readCapSize ∧ i.name.utf8ByteSize < 2 ^ 64
  other : g.other = []
  acks : ∀ b ∈ g.acks, b.size < 2 ^ 64
  numbers : ∀ b ∈ g.numbers, b.size < 2 ^ 64
  introducedAt : ∀ b ∈ g.introducedAt, b.size < 2 ^ 64

theorem fields_wf {g : Gcm} (h : MapWF g) : ∀ f ∈ fields g, FieldWF f := by
  obtain ⟨hv, hh, ht, htext, hintro, hother, hacks, hnum, hia⟩ := h
  simp only [mapVersion, hashSize, MsgType.control] at hv hh ht
  simp only [fields, hother, List.map_nil, List.append_nil, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, List.forall_mem_map, Option.mem_toList, FieldWF,
    IsEmpty.forall_iff, implies_true, and_true]
  and_intros
  all_goals omega

theorem finish_fields {g : Gcm} (h : MapWF g) : ((fields g).foldl Acc.add {}).finish = some g := by
  obtain ⟨v, hs, t, text, intro, other, acks, numbers, ia⟩ := g
  obtain ⟨hv, hh, ht, -, -, rfl, -, -, -⟩ := h
  dsimp only at hv hh ht
  simp only [mapVersion, hashSize, MsgType.control] at hv hh ht
  have hv' : ¬ 3 < v := by omega
  have ht' : ¬ 10 < t := by omega
  cases text <;> cases intro <;> cases acks <;> cases numbers <;> cases ia <;>
    simp [fields, Acc.add, Acc.finish, hv', hh, ht', mapVersion, hashSize,
      MsgType.control]

/-- Decoding undoes encoding in the map form. -/
theorem decode_encode_map {g : Gcm} (h : MapWF g) : decode (encode g) = some g := by
  have hlen : (fields g).length < 2 ^ 64 := by
    have : (fields g).length ≤ 8 := by
      obtain ⟨_, _, _, text, intro, other, acks, numbers, ia⟩ := g
      have := h.other; simp only at this; subst this
      cases text <;> cases intro <;> cases acks <;> cases numbers <;> cases ia <;> simp [fields]
    omega
  have hread := readFields_flatMap (fields g) {} [] (fields_wf h)
  simp only [List.append_nil] at hread
  have hmap : ¬ currentVersion ≤ g.version := by
    have := h.version; simp only [currentVersion, mapVersion] at *; omega
  simp only [decode, encode, decodeList, encodeMapList, hmap, ite_false, List.toList_toArray,
    readHeader_header 5 _ _ (by omega) hlen, Option.bind_eq_bind, Option.bind_some, ite_true,
    hread]
  exact finish_fields h

/-! ## The array form -/

theorem nullable_null {α : Type} (read : List UInt8 → Option (α × List UInt8)) (l : List UInt8) :
    nullable read (null ++ l) = some (none, l) := by
  simp [nullable, isNull, null]

theorem readIntroArray_encodeIntroArray (i : Introduction) (rest : List UInt8) (h : IntroWF i) :
    readIntroArray (encodeIntroArray i ++ rest) = some (i, rest) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [encodeIntroArray, List.append_assoc, readIntroArray,
    readHeader_header 4 2 _ (by omega) (by omega), Option.bind_eq_bind, Option.bind_some,
    readText_text i.name _ h4, readByteArray_bytes i.readCap _ (by rw [h3]; decide)]
  simp [h1, h2, h3]

theorem readOpts_flatMap : ∀ (t : List (Option ByteArray)) (rest : List UInt8),
    (∀ b, some b ∈ t → b.size < 2 ^ 64) →
    readOpts t.length (t.flatMap encodeOpt ++ rest) = some (t, rest)
  | [], _, _ => rfl
  | none :: t, rest, h => by
    simp only [List.length_cons, List.flatMap_cons, encodeOpt, List.append_assoc, readOpts,
      nullable_null, Option.bind_eq_bind, Option.bind_some,
      readOpts_flatMap t rest fun b hb => h b (List.mem_cons_of_mem _ hb)]
  | some b :: t, rest, h => by
    have hb := h b List.mem_cons_self
    have hr := readByteArray_bytes b (t.flatMap encodeOpt ++ rest) hb
    have hnn : isNull (bytes b.data.toList ++ (t.flatMap encodeOpt ++ rest)) = false := by
      unfold bytes; rw [List.append_assoc]; exact isNull_header 2 _ _ (by omega)
    simp only [List.length_cons, List.flatMap_cons, encodeOpt, List.append_assoc, readOpts,
      nullable_some _ _ b _ hr hnn, Option.bind_eq_bind, Option.bind_some,
      readOpts_flatMap t rest fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- A body this client writes in the array form: a text, an introduction or nothing, as the type
says. -/
def BodyWF (g : Gcm) : Prop :=
  (g.msgType = MsgType.text ∧ g.introduction = none
      ∧ ∃ s, g.text = some s ∧ s.utf8ByteSize < 2 ^ 64)
    ∨ (g.msgType = MsgType.introduction ∧ g.text = none ∧ ∃ i, g.introduction = some i ∧ IntroWF i)
    ∨ (g.msgType = MsgType.control ∧ g.text = none ∧ g.introduction = none)

theorem readBody_encodeBody {g : Gcm} (h : BodyWF g) (ho : g.other = []) (rest : List UInt8) :
    readBody g.msgType (encodeBody g ++ rest) = some ((g.text, g.introduction, []), rest) := by
  rcases h with ⟨ht, hi, s, hs, hlen⟩ | ⟨ht, hs, i, hi, hwf⟩ | ⟨ht, hs, hi⟩
  · simp [readBody, encodeBody, ht, hi, hs, MsgType.text, readText_text s rest hlen]
  · simp [readBody, encodeBody, ht, hi, hs, MsgType.text, MsgType.introduction,
      readIntroArray_encodeIntroArray i rest hwf]
  · simp [readBody, encodeBody, ht, hi, hs, ho, bodyKey, MsgType.text, MsgType.introduction,
      MsgType.fileUpload, MsgType.who, MsgType.replyWho, MsgType.control, isNull, null]

/-- A message this client writes in the array form and reads back as it was. -/
structure ArrayWF (g : Gcm) : Prop where
  version : currentVersion ≤ g.version ∧ g.version < 2 ^ 64
  hash : g.membershipHash.size = hashSize
  body : BodyWF g
  other : g.other = []
  acks : ∀ b ∈ g.acks, b.size < 2 ^ 64
  numbers : ∀ b ∈ g.numbers, b.size < 2 ^ 64
  introducedAt : ∀ b ∈ g.introducedAt, b.size < 2 ^ 64

theorem mem_tail {g : Gcm} {b : ByteArray} (h : some b ∈ tail g) :
    some b ∈ [g.acks, g.numbers, g.introducedAt] := by
  unfold tail at h
  rw [List.mem_reverse] at h
  have := (List.dropWhile_suffix Option.isNone).subset h
  rwa [List.mem_reverse] at this

/-- Decoding undoes encoding in the array form. -/
theorem decode_encode_array {g : Gcm} (h : ArrayWF g) : decode (encode g) = some g := by
  obtain ⟨⟨hv4, hv⟩, hh, hb, ho, hacks, hnum, hia⟩ := h
  have htail : (tail g).length ≤ 3 := by
    unfold tail
    obtain ⟨_, _, _, _, _, _, a, n, i⟩ := g
    cases a <;> cases n <;> cases i <;> simp
  have hopts := readOpts_flatMap (tail g) [] fun b hb => by
    have := mem_tail hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h
    · exact hacks b h.symm
    · exact hnum b h.symm
    · exact hia b h.symm
  simp only [List.append_nil] at hopts
  have hn : ¬ (4 + (tail g).length < 4 ∨ 7 < 4 + (tail g).length) := by omega
  have ht : g.msgType ≤ MsgType.control := by
    rcases hb with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ <;> simp [ht, MsgType.text, MsgType.introduction,
      MsgType.control]
  have hok : ¬ (g.version < currentVersion ∨ g.membershipHash.size ≠ hashSize
      ∨ MsgType.control < g.msgType) := by omega
  have ht' : g.msgType < 2 ^ 64 := by simp only [MsgType.control] at ht; omega
  simp only [decode, encode, decodeList, encodeArrayList, hv4, ite_true, List.toList_toArray,
    List.append_assoc, readHeader_header 4 (4 + (tail g).length) _ (by omega) (by omega),
    Option.bind_eq_bind, Option.bind_some, readArray, hn, hok, ite_false,
    readUInt_uint g.version _ hv, readByteArray_bytes g.membershipHash _ (by rw [hh]; decide),
    readUInt_uint g.msgType _ ht', readBody_encodeBody hb ho, Nat.add_sub_cancel_left, hopts,
    Option.some.injEq]
  obtain ⟨_, _, _, _, _, _, a, n, i⟩ := g
  subst ho
  cases a <;> cases n <;> cases i <;> simp [tail]

/-- Decoding undoes encoding: for the messages this client writes in either form. -/
theorem decode_encode {g : Gcm} (h : MapWF g ∨ ArrayWF g) : decode (encode g) = some g :=
  h.elim decode_encode_map decode_encode_array

end Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Gcm
