/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Lean.Data.Json

import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Gcm
import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Membership
import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.ReplyWho
import Cryptlib.Util.HexBytes

/-! # Group chat wire vectors

Checks `testdata/groupchat_wire_vectors.json`, generated from katzenqt, and
`testdata/groupchat_wire_vectors_v4.json`, the same cases in the array form: each message reads as
katzenqt reads it and is written back as katzenqt writes it, each member's message is written as
the same box, membership hashes agree, each reply decodes, encodes to the same bytes and carries
the same `JoinReply`, and each malformed array is refused. -/

open Lean
open Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member
open Cryptlib.Util.HexBytes

def hex (s : String) : Except String ByteArray :=
  match hexStringToByteArray s with
  | some b => pure b
  | none => throw s!"not valid hex: {s}"

def str (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?

def opt {α : Type} (j : Json) (k : String) (read : Json → Except String α) :
    Except String (Option α) := do
  match j.getObjVal? k with
  | .ok .null | .error _ => pure none
  | .ok v => some <$> read v

def readMessage (j : Json) : Except String Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Message := do
  let content ← opt j "content" fun v => do hex (← v.getStr?)
  let introduction ← opt j "introduction" fun v => do
    pure (Introduction.mk (← str v "name") (← hex (← str v "read_cap")))
  let numbers ← (← (← j.getObjVal? "numbers").getArr?).toList.mapM fun n => do
    let p ← n.getArr?
    let k ← p[0]!.getNat?
    match p[1]! with
    | .null => pure (k, none)
    | v => pure (k, some (← hex (← v.getStr?)))
  let introducedAt ← opt j "introduced_at" fun v => do
    pure (IntroRef.mk (← (← v.getObjVal? "introducer").getNat?) (← hex (← str v "index")))
  let acks ← (← (← j.getObjVal? "acks").getArr?).toList.mapM fun a => do
    let p ← a.getArr?
    pure (← p[0]!.getNat?, ← p[1]!.getNat?)
  let membershipHash ← opt j "membership_hash" fun v => do hex (← v.getStr?)
  pure { content, introduction, numbers, introducedAt, acks, membershipHash }

/-- The CBOR major type of the first byte: 4 for the array form, 5 for the map form. -/
def major (b : ByteArray) : Nat := b[0]!.toNat / 32

def message (version : Nat) (j : Json) : Except String String := do
  let name ← str j "name"
  let cbor ← hex (← str j "cbor")
  if version = Gcm.currentVersion ∧ major cbor ≠ 4 then throw s!"{name}: not an array"
  let expected ← opt j "message" readMessage
  let got := Gcm.toMessage cbor
  if got != expected then throw s!"{name}: read differently"
  match got, ← opt j "rewritten" fun v => do hex (← v.getStr?) with
  | some m, some rewritten =>
    unless (Gcm.ofMessage m version).map Gcm.encode == some rewritten do
      throw s!"{name}: written back differently"
    if rewritten == cbor then
      unless (Gcm.decode cbor).map Gcm.encode == some cbor do
        throw s!"{name}: does not decode and encode to itself"
  | none, none => pure ()
  | _, _ => throw s!"{name}: the vector is inconsistent"
  pure s!"{name}{if got.isNone then " (refused)" else ""}"

def written (version : Nat) (j : Json) : Except String String := do
  let name ← str j "name"
  let m ← readMessage (← j.getObjVal? "message")
  let box ← hex (← str j "box")
  unless Gcm.box m version == some box do throw s!"{name}: written as another box"
  if version = Gcm.currentVersion ∧ (box[0]! ≠ 'F'.toNat.toUInt8 ∨ major (box.extract 1 2) ≠ 4) then
    throw s!"{name}: not F then an array"
  pure s!"{name} (written)"

def membership (j : Json) : Except String String := do
  let caps ← (← (← j.getObjVal? "read_caps").getArr?).toList.mapM fun c => do hex (← c.getStr?)
  unless membershipHash caps == (← hex (← str j "hash")) do
    throw s!"membership of {caps.length}: a different hash"
  pure s!"membership of {caps.length} read caps"

def readJoinReply (j : Json) : Except String JoinReply := do
  let members ← (← (← j.getObjVal? "members").getArr?).toList.mapM fun m => do
    match m with
    | .null => pure none
    | v => do
      let p ← v.getArr?
      pure (some (← hex (← p[0]!.getStr?), ← hex (← p[1]!.getStr?)))
  let rosters ← (← (← j.getObjVal? "rosters").getArr?).toList.mapM fun r => do
    match r with
    | .null => pure none
    | v => some <$> (← v.getArr?).toList.mapM fun e => do
      let p ← e.getArr?
      let slot ← match p[1]! with
        | .null => pure none
        | s => some <$> s.getNat?
      pure (← p[0]!.getNat?, slot)
  let introductions ← (← (← j.getObjVal? "introductions").getArr?).toList.mapM fun i => do
    let p ← i.getArr?
    pure (← p[0]!.getNat?, ← hex (← p[1]!.getStr?), ← p[2]!.getNat?)
  pure { members, rosters, introductions,
         introducer := ← (← j.getObjVal? "introducer").getNat?,
         newcomer := ← (← j.getObjVal? "newcomer").getNat? }

def reply (version : Nat) (j : Json) : Except String String := do
  let name ← str j "name"
  let cbor ← hex (← str j "cbor")
  let some w := ReplyWho.decode cbor | throw s!"{name}: does not decode"
  let encode := if version = Gcm.currentVersion then ReplyWho.encode else ReplyWho.encodeMap
  unless encode w == cbor do throw s!"{name}: encodes differently"
  unless ReplyWho.toJoinReply w == (← opt j "join_reply" readJoinReply) do
    throw s!"{name}: carries another JoinReply"
  pure s!"{name} (reply)"

def malformed (j : Json) : Except String String := do
  let name ← str j "name"
  unless (Gcm.decode (← hex (← str j "cbor"))).isNone do throw s!"{name}: not refused"
  pure s!"{name} (refused)"

def file (path : String) (version : Nat) : IO (List String) := do
  let text ← IO.FS.readFile path
  IO.ofExcept do
    let j ← Json.parse text
    let run (key : String) (check : Json → Except String String) : Except String (List String) :=
      match j.getObjVal? key with
      | .ok v => do (← v.getArr?).toList.mapM check
      | .error _ => pure []
    pure ((← run "messages" (message version)) ++ (← run "written" (written version))
      ++ (← run "membership" membership) ++ (← run "replies" (reply version))
      ++ (← run "malformed" malformed))

def zeros (n : Nat) : ByteArray := ⟨(List.replicate n (0 : UInt8)).toArray⟩

/-- The rules the vectors do not show: what is written by default, what each form costs, that
the map form still reads, and that each body reads back. -/
def rules : Except String (List String) := do
  let h := zeros 32
  let check (name : String) (ok : Bool) : Except String String :=
    if ok then pure s!"{name} (rule)" else throw s!"{name}: fails"
  let t4 := Gcm.textContent h "hello"
  let m3 := Gcm.encode { version := Gcm.mapVersion, membershipHash := h,
                         msgType := Gcm.MsgType.text, text := some "hello" }
  let map (p : ByteArray) (t b : String) := Gcm.uploadMap p.data.toList t b
  let bodies : List Gcm.Gcm := [
    { version := 4, membershipHash := h, msgType := Gcm.MsgType.fileUpload,
      other := [("file_upload", map ⟨#[1, 2]⟩ "image/png" "a.png")] },
    { version := 4, membershipHash := h, msgType := Gcm.MsgType.who, other := [("who", Cbor.text "w")] },
    { version := 4, membershipHash := h, msgType := 5, other := [("tally", Cbor.uint 7)] },
    { version := 4, membershipHash := h, msgType := Gcm.MsgType.control, numbers := some ⟨#[4]⟩,
      introducedAt := some (zeros 105) } ]
  let control := Gcm.encode { version := 4, membershipHash := h, msgType := Gcm.MsgType.control,
                              acks := some (zeros 10) }
  pure [
    ← check "default is version 4" (major t4 = 4 ∧ (Gcm.decode t4).map (·.version) = some 4),
    ← check "the map form still reads" (major m3 = 5 ∧ (Gcm.decode m3).bind (·.text) = some "hello"
      ∧ (Gcm.toMessage m3).bind (·.content) = some m3),
    ← check "bodies read back" (bodies.all fun g => Gcm.decode (Gcm.encode g) == some g),
    ← check "a file body is [payload, filetype, basename]"
      (((Gcm.encode bodies[0]!).data.toList.drop 37).take 5 == [0x83, 0x42, 1, 2, 0x69]),
    ← check "a control body is null and trailing nulls are left out"
      ((control.data.toList.drop 36).take 3 == [0x0a, 0xf6, 0x4a]),
    ← check "costs" ((Gcm.textContent h "").size = 38 ∧ (Gcm.textContent h "hello" ).size = 43
      ∧ m3.size = 81 ∧ (Gcm.encode { version := 4, membershipHash := h,
                                     msgType := Gcm.MsgType.control }).size = 38) ]

def main : IO UInt32 := do
  let results := (← file "testdata/groupchat_wire_vectors.json" Gcm.mapVersion)
    ++ (← file "testdata/groupchat_wire_vectors_v4.json" Gcm.currentVersion) ++ (← IO.ofExcept rules)
  results.forM fun r => IO.println s!"ok   {r}"
  IO.println s!"{results.length} group chat wire vectors"
  pure 0
