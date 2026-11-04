/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cborg
import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Events

/-! # The reply to a new member

What an introducer seals into a contact voucher's reply: its roster in order, each member as a
display name and a read cap starting where the new member is to start reading, then the rest of a
`JoinReply`, each member written as its place in that list. Written as the version 4 array
`[please_adds, rosters, introductions, introducer, newcomer]` with trailing nulls left out; read
in that form and as katzenqt's `GroupChatReplyWho` map, which the first byte's major type tells
apart. -/

namespace Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.ReplyWho

open Cborg

def maxNameChars : Nat := 30
def readCapSize : Nat := 136

structure PleaseAdd where
  name : String
  readCap : ByteArray
  deriving DecidableEq, Inhabited

structure ReplyWho where
  pleaseAdds : List (Option PleaseAdd)
  rosters : Option (List (Option (List (Nat × Option Nat)))) := none
  introductions : Option (List (Nat × Index × Nat)) := none
  introducer : Option Nat := none
  newcomer : Option Nat := none
  deriving DecidableEq, Inhabited

/-! ## Between a reply and a `JoinReply` -/

/-- The reply for `r`, naming each member by `name`; a member with no name takes no place, as
katzenqt leaves out a member it does not know. -/
def ofJoinReply (r : JoinReply) (name : Key → Option String) : ReplyWho :=
  { pleaseAdds := r.members.map fun m => m.bind fun (readCap, start) =>
      (name (keyOf readCap)).map fun n => ⟨n, keyOf readCap ++ start⟩
    rosters := some r.rosters
    introductions := some r.introductions
    introducer := some r.introducer
    newcomer := some r.newcomer }

/-- The `JoinReply` a reply carries, or `none` when it carries no rosters or cannot be read. -/
def toJoinReply (w : ReplyWho) : Option JoinReply := do
  let places := w.pleaseAdds.length
  let rosters ← w.rosters
  let introducer ← w.introducer
  let newcomer ← w.newcomer
  if newcomer ≠ places ∨ ¬ (introducer < places ∧ places < rosterMax) then none
  if (w.pleaseAdds.getD introducer none).isNone ∨ rosters.length ≠ places then none
  let keys := w.pleaseAdds.filterMap (·.map fun p => (keyOf p.readCap).data.toList)
  if keys.eraseDups.length ≠ keys.length then none
  let ok := rosters.all fun r => (r.getD []).all fun (i, slot) =>
    i < rosterMax && (slot.all (· < places))
  if !ok then none
  let introductions := (w.introductions.getD []).filter fun (by_, index, member) =>
    by_ < places && member < places && index.size == indexSize
  some { members := w.pleaseAdds.map (·.map fun p => (p.readCap, startOf p.readCap))
         rosters, introductions, introducer, newcomer }

/-! ## CBOR -/

def nat (n : Nat) : Term := .TInt n.toInt64

def optNat : Option Nat → Term
  | some n => nat n
  | none => .TNull

def pleaseAddTerm (p : PleaseAdd) : Term :=
  .TMap #[(.TString "display_name", .TString p.name), (.TString "read_cap", .TBytes p.readCap)]

def rosterTerm (r : List (Nat × Option Nat)) : Term :=
  .TList (r.map fun (i, slot) => .TList #[nat i, optNat slot]).toArray

/-- The five fields in order, each `please_adds` entry written by `pleaseAdd`. -/
def values (pleaseAdd : PleaseAdd → Term) (w : ReplyWho) : List (Option Term) :=
  [ some (.TList (w.pleaseAdds.map fun p => (p.map pleaseAdd).getD .TNull).toArray),
    w.rosters.map fun rs => .TList (rs.map fun r => (r.map rosterTerm).getD .TNull).toArray,
    w.introductions.map fun is =>
      .TList (is.map fun (b, i, m) => .TList #[nat b, .TBytes i, nat m]).toArray,
    w.introducer.map nat, w.newcomer.map nat ]

def keys : List String := ["please_adds", "rosters", "introductions", "introducer", "newcomer"]

/-- The map form, version 3. -/
def toMapTerm (w : ReplyWho) : Term :=
  .TMap ((keys.zip (values pleaseAddTerm w)).filterMap fun (k, v) =>
    v.map (.TString k, ·)).toArray

/-- The array form, version 4. -/
def toTerm (w : ReplyWho) : Term :=
  let vs := values (fun p => .TList #[.TString p.name, .TBytes p.readCap]) w
  .TList ((vs.reverse.dropWhile Option.isNone).reverse.map (·.getD .TNull)).toArray

def encode (w : ReplyWho) : ByteArray := toByteArray (encodeTerm (toTerm w))

def encodeMap (w : ReplyWho) : ByteArray := toByteArray (encodeTerm (toMapTerm w))

def termNat? : Term → Option Nat
  | .TInt n => if 0 ≤ n then some n.toInt.toNat else none
  | .TInteger n => if 0 ≤ n then some n.toNat else none
  | _ => none

def termList? : Term → Option (List Term)
  | .TList ts | .TListI ts => some ts.toList
  | _ => none

def termMap? : Term → Option (List (Term × Term))
  | .TMap kvs | .TMapI kvs => some kvs.toList
  | _ => none

def termString? : Term → Option String
  | .TString s => some s
  | .TStringI ss => some (String.join ss.toList)
  | _ => none

def termBytes? : Term → Option ByteArray
  | .TBytes b => some b
  | .TBytesI bs => some (bs.foldl (· ++ ·) .empty)
  | _ => none

def isNull : Term → Bool
  | .TNull => true
  | _ => false

def field? (kvs : List (Term × Term)) (key : String) : Option Term :=
  (kvs.reverse.find? fun (k, _) => termString? k = some key).map (·.2)

/-- A value that may be absent or `null`; `none` when it is present and cannot be read. -/
def optional {α : Type} (t : Option Term) (read : Term → Option α) : Option (Option α) :=
  match t with
  | none => some none
  | some t => if isNull t then some none else (read t).map some

def nullableList {α : Type} (read : Term → Option α) (t : Term) : Option (List (Option α)) := do
  (← termList? t).mapM fun x => if isNull x then some none else (read x).map some

/-- A member katzenqt accepts: a name of 1 to 30 characters and a whole read cap. -/
def pleaseAdd? (name : Option Term) (cap : Option Term) : Option PleaseAdd := do
  let name ← termString? (← name)
  let cap ← termBytes? (← cap)
  if 1 ≤ name.length ∧ name.length ≤ maxNameChars ∧ cap.size = readCapSize then some ⟨name, cap⟩
  else none

def readPleaseAdd (t : Term) : Option PleaseAdd := do
  let kvs ← termMap? t
  pleaseAdd? (field? kvs "display_name") (field? kvs "read_cap")

def readPleaseAddArray (t : Term) : Option PleaseAdd := do
  match ← termList? t with
  | [name, cap] => pleaseAdd? name cap
  | _ => none

def readRoster (t : Term) : Option (List (Nat × Option Nat)) := do
  (← termList? t).mapM fun e => do
    match ← termList? e with
    | [i, slot] => some (← termNat? i, ← if isNull slot then some none else (termNat? slot).map some)
    | _ => none

def readIntroduction (t : Term) : Option (Nat × Index × Nat) := do
  match ← termList? t with
  | [b, i, m] => some (← termNat? b, ← termBytes? i, ← termNat? m)
  | _ => none

def readIntroductions (t : Term) : Option (List (Nat × Index × Nat)) := do
  (← termList? t).mapM readIntroduction

/-- The rest of a reply from its fields after `please_adds`, each absent or null when unknown. -/
def ofFields (pleaseAdds : List (Option PleaseAdd)) (rosters introductions introducer newcomer :
    Option Term) : Option ReplyWho := do
  some { pleaseAdds
         rosters := ← optional rosters (nullableList readRoster)
         introductions := ← optional introductions readIntroductions
         introducer := ← optional introducer termNat?
         newcomer := ← optional newcomer termNat? }

def ofArray (ts : List Term) : Option ReplyWho := do
  if ts.isEmpty ∨ 5 < ts.length then none
  ofFields (← nullableList readPleaseAddArray (← ts[0]?)) ts[1]? ts[2]? ts[3]? ts[4]?

def ofMap (kvs : List (Term × Term)) : Option ReplyWho := do
  ofFields (← nullableList readPleaseAdd (← field? kvs "please_adds")) (field? kvs "rosters")
    (field? kvs "introductions") (field? kvs "introducer") (field? kvs "newcomer")

def ofTerm (t : Term) : Option ReplyWho :=
  match termList? t, termMap? t with
  | some ts, _ => ofArray ts
  | _, some kvs => ofMap kvs
  | _, _ => none

def decode (b : ByteArray) : Option ReplyWho :=
  match deserialiseFromBytes decodeTerm b with
  | .ok (_, t) => ofTerm t
  | .error _ => none

end Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.ReplyWho
