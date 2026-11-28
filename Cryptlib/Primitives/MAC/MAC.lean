/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

namespace Cryptlib.Primitives.MAC

/-! # Message authentication codes

`keySize` is informational; `mac` accepts any key length. Unforgeability is computational, so
there are no law fields. -/

structure MAC where
  keySize : Nat
  tagSize : Nat

  mac : ByteArray → ByteArray → Vector UInt8 tagSize

/-- The empty MAC, to show `MAC` is inhabited. Not a MAC. -/
instance : Inhabited MAC := ⟨{
  keySize := 0
  tagSize := 0
  mac := fun _ _ => #v[]
}⟩

/-- The "MAC" that gives one fixed tag. A reduction that holds a tag and not its key runs a
verifier with it in place of the MAC. -/
def MAC.const {n : Nat} (tag : Vector UInt8 n) : MAC where
  keySize := 32
  tagSize := n
  mac _ _ := tag

end Cryptlib.Primitives.MAC
