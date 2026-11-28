/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Lean

/-! # Axiom check

`lake lint` runs this. It fails if a theorem of the library rests on an axiom that is not
`allowed`: a `sorry`, a `native_decide`, or an axiom declared without being listed here. -/

open Lean

/-- Lean's own axioms, and the ones the library declares on purpose: that the field prime of
Curve25519 and the order of its prime subgroup are prime. -/
def declared : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound, `Cryptlib.Primitives.NIKE.X25519.p_prime,
    `Cryptlib.Primitives.Sign.Ed25519Blinded.ell_prime]

/-- An axiom `bv_decide` adds for the certificate it checked with compiled code. -/
def fromBvDecide : Name → Bool
  | .str p s => s == "bv_decide" || fromBvDecide p
  | .num p _ => fromBvDecide p
  | .anonymous => false

def allowed (c : Name) : Bool := declared.contains c || fromBvDecide c

/-- The axioms outside `allowed` that `c` rests on. -/
partial def unlisted (env : Environment) (c : Name) :
    StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some found := (← get)[c]? then return found
  modify (·.insert c #[])
  let mut found := #[]
  match env.find? c with
  | some (.axiomInfo _) => if !allowed c then found := #[c]
  | some info =>
    for d in info.getUsedConstantsAsSet do
      for a in ← unlisted env d do
        if !found.contains a then found := found.push a
  | none => pure ()
  modify (·.insert c found)
  return found

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Cryptlib }] {}
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut checked := 0
  let mut failed := 0
  for (c, info) in env.constants.map₁ do
    let some idx := env.getModuleIdxFor? c | continue
    if info matches .thmInfo _ && (`Cryptlib).isPrefixOf env.header.moduleNames[idx.toNat]! then
      let (found, memo') := (unlisted env c).run memo
      memo := memo'
      checked := checked + 1
      if !found.isEmpty then
        failed := failed + 1
        IO.eprintln s!"{c} rests on {found.toList}"
  if failed = 0 then
    IO.println s!"{checked} theorems rest on the listed axioms only"
    return 0
  IO.eprintln s!"FAIL: {failed} of {checked} theorems rest on an axiom that is not listed"
  return 1
