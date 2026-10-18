/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member.Events

/-! # Reading one member's stream

A reader reads in order, one box at a time. A scan rechecks boxes previously stepped past and may
jump ahead to a box another member acknowledged, keeping the boxes it skips. A reader acknowledges
the end of the unbroken run it has read (`run`). See "Rewrite and scan" in the group chat spec. -/

namespace Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member

inductive Mode | idle | reading | scanning
  deriving DecidableEq, Inhabited

structure Reader where
  stream : Key
  readCap : ByteArray
  /-- The index of the next box to read. -/
  next : Index
  /-- The last box read in order, data or tombstone. -/
  last : Option Index := none
  /-- How many boxes this reader has passed. -/
  passed : Nat := 0
  /-- Boxes a scan stepped past without reading, oldest first: each with the count it was passed
  at and the box before it. -/
  kept : List (Index × Nat × Option Index) := []
  /-- The first box passed unread and no longer kept; acknowledgements stop before it. -/
  lost : Option (Nat × Option Index) := none
  mode : Mode := .idle
  /-- The `Idx64` of each acknowledged box ahead that a scan has already looked for, while it is
  still heard: no more than there are members. -/
  tried : List Nat := []
  deriving DecidableEq, Inhabited

namespace Reader

def read (r : Reader) : Reader × List Effect :=
  if r.mode ≠ .idle then (r, [])
  else ({ r with mode := .reading }, [.readBox r.stream r.readCap r.next false])

/-- Each of `l` once, where it first appears. -/
def firstEach (l : List Nat) : List Nat :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Acknowledged boxes ahead of here a scan has not looked for yet, each once. A walk only goes
forward, so one behind is never found. -/
def ahead (r : Reader) (heard : List Nat) : List Nat :=
  firstEach (heard.filter fun h => counter r.next < h && !r.tried.contains h)

def rechecks (r : Reader) : List Effect := r.kept.map fun e => .readBox r.stream r.readCap e.1 true

/-- What a scan still needs to remember having looked for: boxes ahead that are still heard. -/
def prune (r : Reader) (heard : List Nat) : Reader :=
  { r with tried := r.tried.filter fun t => counter r.next < t && heard.contains t }

/-- Recheck what was kept, then look for acknowledged boxes ahead, or probe forward from here. -/
def scan (r : Reader) (heard : List Nat) (window : Nat) : Reader × List Effect :=
  let r := r.prune heard
  if (r.ahead heard).isEmpty then
    ({ r with mode := .scanning }, r.rechecks ++ [.readBox r.stream r.readCap r.next false])
  else
    ({ r with mode := .scanning, tried := r.tried ++ r.ahead heard },
      r.rechecks ++ [.walk r.stream r.next (r.ahead heard) window])

/-- The end of the unbroken run read: how far this stream may be acknowledged. -/
def run (r : Reader) : Option Index :=
  match r.kept.map (·.2) ++ r.lost.toList with
  | [] => r.last
  | g :: gs => (gs.foldl (fun m x => if x.1 < m.1 then x else m) g).2

def lose (r : Reader) (at_ : Nat) (before : Option Index) : Reader :=
  match r.lost with
  | some (l, _) => if at_ < l then { r with lost := some (at_, before) } else r
  | none => { r with lost := some (at_, before) }

/-- Give up on each of `dropped`. -/
def loseAll (r : Reader) (dropped : List (Index × Nat × Option Index)) : Reader :=
  dropped.foldl (fun r e => r.lose e.2.1 e.2.2) r

/-- Drop kept boxes more than `window` behind, as lost. -/
def forget (r : Reader) (window : Nat) : Reader :=
  { r.loseAll (r.kept.filter fun e => e.2.1 + window < r.passed) with
    kept := r.kept.filter fun e => r.passed ≤ e.2.1 + window }

/-- The boxes a walk kept, from position `start`, each with the box before it. -/
def stepped (r : Reader) (skipped : List Index) (start : Nat) : List (Index × Nat × Option Index) :=
  (skipped.zip (r.last :: skipped.map some)).zipIdx.map fun ((i, b), n) => (i, start + n, b)

/-- Jump to `t` past `steps` boxes, keeping the last `skipped` of them; any before those are
given up on. -/
def jump (r : Reader) (t : Index) (skipped : List Index) (steps : Nat) : Reader :=
  let start := r.passed + steps - skipped.length
  let r1 := if start > r.passed then r.lose r.passed r.last else r
  { r1 with kept := r1.kept ++ r.stepped skipped start, passed := r1.passed + steps, next := t }

/-- The result of a walk: jump to `target`, keeping the boxes passed. -/
def walked (r : Reader) (target : Option Index) (skipped : List Index) (steps window : Nat) :
    Reader × List Effect :=
  match target with
  | none => (r, [.readBox r.stream r.readCap r.next false])
  | some t =>
    ((r.jump t skipped steps).forget window,
      [.readBox r.stream r.readCap t false])

def messageOf : ReadResult → Option Message
  | .data m => m
  | .missing _ => none

/-- Read the box expected next, in order. -/
def advance (r : Reader) (index next : Index) : Reader :=
  { r with last := some index, next := next, passed := r.passed + 1 }

/-- Take one box read: its message if it is new data to ingest, and what to read next. -/
def found (r : Reader) (index : Index) (result : ReadResult) (next : Option Index) (window : Nat) :
    Option Message × Reader × List Effect :=
  match r.kept.find? (·.1 = index) with
  | some e =>
    if result = .missing .notFound then (none, r, [])
    else (messageOf result, { r with kept := r.kept.eraseP (· = e) }, [])
  | none =>
    if index ≠ r.next || r.mode = .idle then (none, r, [])
    else match result, next with
      | .missing .notFound, _ => (none, { r with mode := .idle }, [])
      | _, none => (none, { r with mode := .idle }, [])
      | _, some n => (messageOf result, (r.advance index n).forget window, [.readBox r.stream r.readCap n false])

end Reader

end Cryptlib.Protocols.GroupComm.GroupChatKatzenqt1.Member
