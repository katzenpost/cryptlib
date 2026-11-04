/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.AckBytes
import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Cbor
import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Wire

/-! # Group chat messages on the wire

A box of a member's stream holds `F` followed by the CBOR of one `GroupChatMessage`: in version 4
the array `[version, membership_hash, msg_type, body, acks, numbers, introduced_at]` with trailing
nulls left out, in version 3 a map of the fields in declaration order, absent ones left out, as
katzenqt's `models.py` writes it. The first byte's major type tells the forms apart. A message too
long for a box goes to a substream of `C` chunks ending in an `F` chunk, announced in the member's
stream by an `I` chunk carrying the substream's read cap.

`Gcm` holds what this client reads of a message. The bodies it does not read (`file_upload`, `who`,
`reply_who`, `tally`) are kept in `other` as their CBOR in the map form, a `file_upload` as the map
`payload`, `filetype`, `basename`; keys katzenqt does not know are dropped, as its decoder drops
them. -/

namespace Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Gcm

open Cbor

/-- The version written: the array form. -/
def currentVersion : Nat := 4
/-- The newest version of the map form, which is read as well. -/
def mapVersion : Nat := 3

def hashSize : Nat := 32
def readCapSize : Nat := 136
def maxNameChars : Nat := 30

namespace MsgType
def text : Nat := 0
def introduction : Nat := 1
def fileUpload : Nat := 2
def who : Nat := 3
def replyWho : Nat := 4
def control : Nat := 10
end MsgType

/-- The fields this client keeps without reading, in the order they are written. -/
def otherKeys : List String := ["file_upload", "who", "reply_who", "tally"]

/-- The field a message type's body is, in the map form and in `other`. -/
def bodyKey (t : Nat) : Option String :=
  if t = MsgType.fileUpload then some "file_upload"
  else if t = MsgType.who then some "who"
  else if t = MsgType.replyWho then some "reply_who"
  else if 5 ≤ t ∧ t ≤ 9 then some "tally"
  else none

structure Gcm where
  version : Nat
  membershipHash : ByteArray
  msgType : Nat
  text : Option String := none
  introduction : Option Introduction := none
  other : List (String × List UInt8) := []
  acks : Option ByteArray := none
  numbers : Option ByteArray := none
  introducedAt : Option ByteArray := none
  deriving DecidableEq, Inhabited

/-! ## Encoding

### The map form -/

inductive Field
  | version (n : Nat)
  | hash (b : ByteArray)
  | msgType (n : Nat)
  | text (s : String)
  | intro (i : Introduction)
  | other (key : String) (raw : List UInt8)
  | acks (b : ByteArray)
  | numbers (b : ByteArray)
  | introducedAt (b : ByteArray)

/-- A message's fields, in the order they are written. -/
def fields (g : Gcm) : List Field :=
  [.version g.version, .hash g.membershipHash, .msgType g.msgType]
    ++ g.text.toList.map .text
    ++ g.introduction.toList.map .intro
    ++ g.other.map (fun o => .other o.1 o.2)
    ++ g.acks.toList.map .acks
    ++ g.numbers.toList.map .numbers
    ++ g.introducedAt.toList.map .introducedAt

def encodeIntro (i : Introduction) : List UInt8 :=
  header 5 2 ++ Cbor.text "display_name" ++ Cbor.text i.name
    ++ Cbor.text "read_cap" ++ bytes i.readCap.data.toList

def encodeField : Field → List UInt8
  | .version n => Cbor.text "version" ++ uint n
  | .hash b => Cbor.text "membership_hash" ++ bytes b.data.toList
  | .msgType n => Cbor.text "msg_type" ++ uint n
  | .text s => Cbor.text "text" ++ Cbor.text s
  | .intro i => Cbor.text "introduction" ++ encodeIntro i
  | .other k raw => Cbor.text k ++ raw
  | .acks b => Cbor.text "acks" ++ bytes b.data.toList
  | .numbers b => Cbor.text "numbers" ++ bytes b.data.toList
  | .introducedAt b => Cbor.text "introduced_at" ++ bytes b.data.toList

def encodeMapList (g : Gcm) : List UInt8 :=
  header 5 (fields g).length ++ (fields g).flatMap encodeField

/-! ### The array form -/

/-- A `file_upload` map's `payload`, `filetype` and `basename`; a missing one is empty. -/
def uploadEntries : Nat → List UInt8 × String × String → List UInt8 →
    Option (List UInt8 × String × String)
  | 0, acc, _ => some acc
  | n + 1, (p, t, b), l => do
    let (k, l) ← readText l
    if k = "payload" then
      let (v, l) ← readBytes l
      uploadEntries n (v, t, b) l
    else if k = "filetype" then
      let (v, l) ← readText l
      uploadEntries n (p, v, b) l
    else if k = "basename" then
      let (v, l) ← readText l
      uploadEntries n (p, t, v) l
    else
      uploadEntries n (p, t, b) (← skipItems (l.length + 1) 1 l)

/-- The array body `[payload, filetype, basename]` of a `file_upload` map; anything else as it
came. -/
def uploadArray (raw : List UInt8) : List UInt8 :=
  match readHeader raw with
  | some (5, n, rest) =>
    match uploadEntries n ([], "", "") rest with
    | some (p, t, b) => header 4 3 ++ bytes p ++ Cbor.text t ++ Cbor.text b
    | none => raw
  | _ => raw

def encodeIntroArray (i : Introduction) : List UInt8 :=
  header 4 2 ++ Cbor.text i.name ++ bytes i.readCap.data.toList

/-- The type's payload: the text, `[display_name, read_cap]`, `[payload, filetype, basename]`,
an app's value, or null. -/
def encodeBody (g : Gcm) : List UInt8 :=
  if g.msgType = MsgType.text then Cbor.text (g.text.getD "")
  else if g.msgType = MsgType.introduction then
    match g.introduction with
    | some i => encodeIntroArray i
    | none => null
  else match (bodyKey g.msgType).bind (fun k => g.other.lookup k) with
    | some raw => if g.msgType = MsgType.fileUpload then uploadArray raw else raw
    | none => null

/-- The fields after the body, the trailing absent ones left out. -/
def tail (g : Gcm) : List (Option ByteArray) :=
  ([g.acks, g.numbers, g.introducedAt].reverse.dropWhile Option.isNone).reverse

def encodeOpt : Option ByteArray → List UInt8
  | some b => bytes b.data.toList
  | none => null

def encodeArrayList (g : Gcm) : List UInt8 :=
  header 4 (4 + (tail g).length) ++ uint g.version ++ bytes g.membershipHash.data.toList
    ++ uint g.msgType ++ encodeBody g ++ (tail g).flatMap encodeOpt

/-- The CBOR of `g`: the array form from version 4 on, the map form below. -/
def encode (g : Gcm) : ByteArray :=
  ⟨(if currentVersion ≤ g.version then encodeArrayList g else encodeMapList g).toArray⟩

/-! ## Decoding

### The map form -/

/-- An `introduction` map's entries: `display_name` and `read_cap`, in either order. -/
def introEntries : Nat → Option String × Option ByteArray → List UInt8 →
    Option ((Option String × Option ByteArray) × List UInt8)
  | 0, acc, l => some (acc, l)
  | n + 1, (name, cap), l => do
    let (k, l) ← readText l
    if k = "display_name" then
      let (s, l) ← readText l
      introEntries n (some s, cap) l
    else if k = "read_cap" then
      let (b, l) ← readBytes l
      introEntries n (name, some ⟨b.toArray⟩) l
    else
      let l ← skipItems (l.length + 1) 1 l
      introEntries n (name, cap) l

/-- An introduction katzenqt accepts: a name of 1 to 30 characters and a whole read cap. -/
def readIntro (l : List UInt8) : Option (Introduction × List UInt8) := do
  let (major, n, rest) ← readHeader l
  if major ≠ 5 then none
  let ((name, cap), rest) ← introEntries n (none, none) rest
  let name ← name
  let cap ← cap
  if 1 ≤ name.length ∧ name.length ≤ maxNameChars ∧ cap.size = readCapSize then
    some (⟨name, cap⟩, rest)
  else none

/-- Read a value that may be `null`, which counts as absent. -/
def nullable {α : Type} (read : List UInt8 → Option (α × List UInt8)) (l : List UInt8) :
    Option (Option α × List UInt8) :=
  if isNull l then some (none, l.drop 1)
  else (read l).map fun (a, rest) => (some a, rest)

def readByteArray (l : List UInt8) : Option (ByteArray × List UInt8) :=
  (readBytes l).map fun (b, rest) => (⟨b.toArray⟩, rest)

/-- What the fields read so far say. -/
structure Acc where
  version : Option Nat := none
  hash : Option ByteArray := none
  msgType : Option Nat := none
  text : Option String := none
  introduction : Option Introduction := none
  other : List (String × List UInt8) := []
  acks : Option ByteArray := none
  numbers : Option ByteArray := none
  introducedAt : Option ByteArray := none

/-- One map entry: a key this client reads and its value, or `none` for an entry it passes
over. -/
def readField (l : List UInt8) : Option (Option Field × List UInt8) := do
  let (k, l) ← readText l
  if k = "version" then
    let (n, l) ← readUInt l
    some (some (.version n), l)
  else if k = "membership_hash" then
    let (b, l) ← readByteArray l
    some (some (.hash b), l)
  else if k = "msg_type" then
    let (n, l) ← nullable readUInt l
    some (n.map .msgType, l)
  else if k = "text" then
    let (s, l) ← nullable readText l
    some (s.map .text, l)
  else if k = "introduction" then
    let (i, l) ← nullable readIntro l
    some (i.map .intro, l)
  else if k ∈ otherKeys then
    if isNull l then some (none, l.drop 1)
    else
      let (raw, l) ← readRaw l
      some (some (.other k raw), l)
  else if k = "acks" then
    let (b, l) ← nullable readByteArray l
    some (b.map .acks, l)
  else if k = "numbers" then
    let (b, l) ← nullable readByteArray l
    some (b.map .numbers, l)
  else if k = "introduced_at" then
    let (b, l) ← nullable readByteArray l
    some (b.map .introducedAt, l)
  else
    let l ← skipItems (l.length + 1) 1 l
    some (none, l)

/-- Take in one field; a repeated key keeps its last value, as a Python dict does. -/
def Acc.add (a : Acc) : Field → Acc
  | .version n => { a with version := some n }
  | .hash b => { a with hash := some b }
  | .msgType n => { a with msgType := some n }
  | .text s => { a with text := some s }
  | .intro i => { a with introduction := some i }
  | .other k raw => { a with other := a.other.filter (·.1 ≠ k) ++ [(k, raw)] }
  | .acks b => { a with acks := some b }
  | .numbers b => { a with numbers := some b }
  | .introducedAt b => { a with introducedAt := some b }

def readFields : Nat → Acc → List UInt8 → Option (Acc × List UInt8)
  | 0, a, l => some (a, l)
  | n + 1, a, l => do
    let (f, l) ← readField l
    readFields n (match f with | some f => a.add f | none => a) l

/-- The type of a message written before `msg_type` was, from the field it carries. -/
def inferType (a : Acc) : Nat :=
  if a.introduction.isSome then MsgType.introduction
  else if a.other.any (·.1 = "file_upload") then MsgType.fileUpload
  else if a.other.any (·.1 = "who") then MsgType.who
  else if a.other.any (·.1 = "reply_who") then MsgType.replyWho
  else MsgType.text

/-- A message from the fields read, when katzenqt would accept it. -/
def Acc.finish (a : Acc) : Option Gcm := do
  let v ← a.version
  let h ← a.hash
  let t := a.msgType.getD (inferType a)
  if mapVersion < v ∨ h.size ≠ hashSize ∨ MsgType.control < t then none
  some { version := v, membershipHash := h, msgType := t, text := a.text,
         introduction := a.introduction,
         other := otherKeys.filterMap fun k => (a.other.lookup k).map (k, ·),
         acks := a.acks, numbers := a.numbers, introducedAt := a.introducedAt }

/-! ### The array form -/

def readIntroArray (l : List UInt8) : Option (Introduction × List UInt8) := do
  let (major, n, l) ← readHeader l
  if major ≠ 4 ∨ n ≠ 2 then none
  let (name, l) ← readText l
  let (cap, l) ← readByteArray l
  if 1 ≤ name.length ∧ name.length ≤ maxNameChars ∧ cap.size = readCapSize then
    some (⟨name, cap⟩, l)
  else none

def uploadMap (p : List UInt8) (t b : String) : List UInt8 :=
  header 5 3 ++ Cbor.text "payload" ++ bytes p ++ Cbor.text "filetype" ++ Cbor.text t
    ++ Cbor.text "basename" ++ Cbor.text b

/-- A `[payload, filetype, basename]` body, as the `file_upload` map. -/
def readUpload (l : List UInt8) : Option (List UInt8 × List UInt8) := do
  let (major, n, l) ← readHeader l
  if major ≠ 4 ∨ n ≠ 3 then none
  let (p, l) ← readBytes l
  let (t, l) ← readText l
  let (b, l) ← readText l
  some (uploadMap p t b, l)

/-- What a body says: the text, the introduction, or the field kept unread. -/
abbrev Body := Option String × Option Introduction × List (String × List UInt8)

def readBody (t : Nat) (l : List UInt8) : Option (Body × List UInt8) :=
  if t = MsgType.text then (readText l).map fun (s, l) => ((some s, none, []), l)
  else if t = MsgType.introduction then
    (readIntroArray l).map fun (i, l) => ((none, some i, []), l)
  else if t = MsgType.fileUpload then
    (readUpload l).map fun (raw, l) => ((none, none, [("file_upload", raw)]), l)
  else if t = MsgType.control then
    if isNull l then some ((none, none, []), l.drop 1) else none
  else if isNull l then some ((none, none, []), l.drop 1)
  else (readRaw l).map fun (raw, l) => ((none, none, [((bodyKey t).getD "tally", raw)]), l)

/-- `k` fields that are each a byte string or null. -/
def readOpts : Nat → List UInt8 → Option (List (Option ByteArray) × List UInt8)
  | 0, l => some ([], l)
  | k + 1, l => do
    let (b, l) ← nullable readByteArray l
    let (bs, l) ← readOpts k l
    some (b :: bs, l)

/-- The message an array of `n` elements holds. -/
def readArray (n : Nat) (l : List UInt8) : Option Gcm := do
  if n < 4 ∨ 7 < n then none
  let (v, l) ← readUInt l
  let (h, l) ← readByteArray l
  let (t, l) ← readUInt l
  if v < currentVersion ∨ h.size ≠ hashSize ∨ MsgType.control < t then none
  let ((text, introduction, other), l) ← readBody t l
  let (opts, _) ← readOpts (n - 4) l
  some { version := v, membershipHash := h, msgType := t, text, introduction, other,
         acks := opts.getD 0 none, numbers := opts.getD 1 none, introducedAt := opts.getD 2 none }

def decodeList (l : List UInt8) : Option Gcm := do
  let (major, n, rest) ← readHeader l
  if major = 4 then readArray n rest
  else if major = 5 then
    let (a, _) ← readFields n {} rest
    a.finish
  else none

/-- The message a CBOR item holds, in either form, or `none` when it is refused. What follows the
item is ignored, as `cbor2.loads` ignores it. -/
def decode (b : ByteArray) : Option Gcm := decodeList b.data.toList

/-! ## Boxes -/

/-- What a box of a stream holds. -/
inductive Chunk
  /-- The last or only chunk of a message. -/
  | final (cbor : ByteArray)
  /-- A chunk of a message that continues in the next box. -/
  | continued (part : ByteArray)
  /-- Where a long message is: the substream's read cap, and how many chunks it holds when the
  writer said. -/
  | indirection (total : Option Nat) (readCap : ByteArray)
  | unknown
  deriving Inhabited

def frame (cbor : ByteArray) : ByteArray := ByteArray.mk #['F'.toNat.toUInt8] ++ cbor

def unframe (box : ByteArray) : Chunk :=
  let rest := box.extract 1 box.size
  if box.size = 0 then .unknown
  else if box[0]! = 'F'.toNat.toUInt8 then .final rest
  else if box[0]! = 'C'.toNat.toUInt8 then .continued rest
  else if box[0]! = 'I'.toNat.toUInt8 then
    if rest.size = 4 + readCapSize then
      .indirection (some (Cbor.fromBE (rest.extract 0 4).data.toList)) (rest.extract 4 rest.size)
    else if rest.size = readCapSize then .indirection none rest
    else .unknown
  else .unknown

/-! ## Between a message and what a member reads of it

As katzenqt's `GcmCodec`: a content message's whole CBOR travels as its content; control messages
and introductions are written afresh. -/

/-- The hash a control message or an introduction carries in place of the membership hash. -/
def sentinel : ByteArray := ⟨(List.replicate hashSize (0 : UInt8)).toArray⟩

/-- The sentinel older clients send. -/
def oldSentinel : ByteArray := "TODOTODOTODOTODOTODOTODOTODOTODO".toUTF8

/-- Whether `h` says no membership hash. -/
def isSentinel (h : ByteArray) : Bool := h == sentinel || h == oldSentinel

def isControl (g : Gcm) : Bool :=
  g.msgType = MsgType.control || g.msgType = MsgType.introduction

/-- What a member reads of a message's CBOR, or `none` when it is not a message. -/
def toMessage (cbor : ByteArray) : Option Message := do
  let g ← decode cbor
  let intro := if g.msgType = MsgType.introduction then g.introduction else none
  some { content := if isControl g then none else some cbor
         introduction := intro
         numbers := decodeNumbers (g.numbers.getD .empty).data.toList
         introducedAt := g.introducedAt.bind fun b => decodeIntroducedAt b.data.toList
         acks := (AckBytes.decode (g.acks.getD .empty)).getD []
         membershipHash := if isControl g && !isSentinel g.membershipHash then some g.membershipHash
           else none }

def nonEmpty (b : ByteArray) : Option ByteArray := if b.size = 0 then none else some b

/-- The message whose CBOR a member's `m` is written as, a control message or introduction in
`version`; `none` when its content is not a message. -/
def ofMessage (m : Message) (version : Nat := currentVersion) : Option Gcm := do
  let g ← match m.content, m.introduction with
    | some c, _ => decode c
    | none, some i => some { version, membershipHash := m.membershipHash.getD sentinel,
                              msgType := MsgType.introduction, introduction := some i }
    | none, none => some { version, membershipHash := m.membershipHash.getD sentinel,
                           msgType := MsgType.control }
  some { g with
    acks := nonEmpty (AckBytes.encode m.acks)
    numbers := nonEmpty ⟨(encodeNumbers m.numbers).toArray⟩
    introducedAt := m.introducedAt.map fun r => ⟨(encodeIntroducedAt r).toArray⟩ }

/-- The box for a member's `m`. -/
def box (m : Message) (version : Nat := currentVersion) : Option ByteArray :=
  (ofMessage m version).map fun g => frame (encode g)

/-- A text message, as a member's content. -/
def textContent (membershipHash : ByteArray) (s : String) : ByteArray :=
  encode { version := currentVersion, membershipHash, msgType := MsgType.text, text := some s }

end Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Gcm
