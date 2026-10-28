/-
SPDX-FileCopyrightText: © 2024 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasPrimality

import Cryptlib.Util.NatBytes
import Cryptlib.Util.HexBytes
import Cryptlib.Primitives.NIKE.NIKE
import Cryptlib.Primitives.NIKE.X25519Common
import Cryptlib.Primitives.NIKE.X25519
import Cryptlib.Primitives.NIKE.Field25519

open Cryptlib.Util.NatBytes
open Cryptlib.Primitives.NIKE.NIKE
open Cryptlib.Primitives.NIKE.X25519Common

namespace Cryptlib.Primitives.NIKE.X25519_montgomery_ladder

/-- Little-endian byte encoding, exactly 32 bytes. -/
def fromField (x : ZMod p) : Vector UInt8 keySize := X25519.encodeFieldChecked x

def basepointBytes : Vector UInt8 keySize := fromField basepoint

structure LadderState where
  x1 : ZMod p
  x2 : ZMod p
  z2 : ZMod p
  x3 : ZMod p
  z3 : ZMod p

def montgomery_step (s : LadderState) : LadderState :=
  let tmp0 := s.x3 - s.z3
  let tmp1 := s.x2 - s.z2
  let x2 := s.x2 + s.z2
  let z2 := s.x3 + s.z3
  let z3 := (tmp0 * x2)
  let z2 := z2 * tmp1
  let tmp0 := tmp1^2
  let tmp1 := x2^2
  let x3 := z3 + z2
  let z2 := z3 - z2
  let x2 := tmp1 * tmp0
  let tmp1 := tmp1 - tmp0
  let z2 := z2^2
  let z3 := tmp1 * 121666
  let x3 := x3^2
  let tmp0 := tmp0 + z3
  let z3 := s.x1 * z2
  let z2 := tmp1 * tmp0
  { s with x2 := x2, z2 := z2, x3 := x3, z3 := z3 }

def cswap (swap : Bool) (x y : ZMod p) : (ZMod p × ZMod p) :=
  if swap then (y, x) else (x, y)

/-- The ladder takes the scalar as bytes: a clamped scalar can exceed `p`, so it must not be
reduced modulo `p`. -/
def montgomery_ladder (e : Vector UInt8 keySize) (point : ZMod p) : Id LadderState :=
  do
    let mut state : LadderState := {
      x1 := point,
      x2 := 1,
      z2 := 0,
      x3 := point,
      z3 := 1
    }
    let mut swap := false
    for pos in (List.range 255).reverse do
      let b : Bool := ((e[pos / 8]!).toNat >>> (pos % 8)) &&& 1 == 1
      let newSwap := swap != b
      let (stateX2, stateX3) := cswap newSwap state.x2 state.x3
      let (stateZ2, stateZ3) := cswap newSwap state.z2 state.z3
      state := { state with x2 := stateX2, x3 := stateX3, z2 := stateZ2, z3 := stateZ3 }
      state := montgomery_step state
      swap := b
    let (finalX2, finalX3) := cswap swap state.x2 state.x3
    let (finalZ2, finalZ3) := cswap swap state.z2 state.z3
    state := { state with x2 := finalX2, x3 := finalX3, z2 := finalZ2, z3 := finalZ3 }
    state

def scalarmult (scalarBytes : Vector UInt8 keySize) (point : ZMod p) : ZMod p :=
  let finalState := montgomery_ladder (clampScalar scalarBytes) point
  finalState.x2 * finalState.z2⁻¹

def curve25519 (scalar point : Vector UInt8 keySize) : Vector UInt8 keySize :=
  fromField (scalarmult scalar (toField point))

/-- RFC 7748 X25519. Total: the ladder is defined on every u-coordinate, including twist
points. -/
def x25519 (scalarBytes uCoordBytes : Vector UInt8 keySize) : Vector UInt8 keySize :=
  curve25519 scalarBytes uCoordBytes

/-! ## The same ladder on `Field25519.Fe`

The ladder on fixed-width limbs, with masked swaps so it does not branch on scalar bits. Tested
against the `ZMod` ladder and RFC 7748 vectors, not yet proved equal to it; `X25519LadderCorrect`
proves the `ZMod` ladder. -/

open Cryptlib.Primitives.NIKE.Field25519 (Fe)

structure LadderStateFe where
  x1 : Fe
  x2 : Fe
  z2 : Fe
  x3 : Fe
  z3 : Fe

def montgomery_step_fe (s : LadderStateFe) : LadderStateFe :=
  let tmp0 := s.x3.sub s.z3
  let tmp1 := s.x2.sub s.z2
  let x2 := s.x2.add s.z2
  let z2 := s.x3.add s.z3
  let z3 := tmp0.mul x2
  let z2 := z2.mul tmp1
  let tmp0 := tmp1.sq
  let tmp1 := x2.sq
  let x3 := z3.add z2
  let z2 := z3.sub z2
  let x2 := tmp1.mul tmp0
  let tmp1 := tmp1.sub tmp0
  let z2 := z2.sq
  let z3 := tmp1.mulSmall 121666
  let x3 := x3.sq
  let tmp0 := tmp0.add z3
  let z3 := s.x1.mul z2
  let z2 := tmp1.mul tmp0
  { s with x2 := x2, z2 := z2, x3 := x3, z3 := z3 }

def montgomery_ladder_fe (e : Vector UInt8 keySize) (point : Fe) : LadderStateFe := Id.run do
  let mut state : LadderStateFe := { x1 := point, x2 := Fe.one, z2 := Fe.zero, x3 := point, z3 := Fe.one }
  let mut swap : UInt64 := 0
  for k in [0:255] do
    let pos := 254 - k
    let b : UInt64 := ((e[pos / 8]!).toUInt64 >>> (pos % 8).toUInt64) &&& 1
    let s := swap ^^^ b
    let (x2, x3) := Fe.cswap s state.x2 state.x3
    let (z2, z3) := Fe.cswap s state.z2 state.z3
    state := montgomery_step_fe { state with x2, x3, z2, z3 }
    swap := b
  let (x2, x3) := Fe.cswap swap state.x2 state.x3
  let (z2, z3) := Fe.cswap swap state.z2 state.z3
  return { state with x2, x3, z2, z3 }

def scalarmult_fe (scalarBytes : Vector UInt8 keySize) (point : Fe) : Fe :=
  let s := montgomery_ladder_fe (clampScalar scalarBytes) point
  s.x2.mul s.z2.invert

def curve25519_fe (scalar point : Vector UInt8 keySize) : Vector UInt8 keySize :=
  (scalarmult_fe scalar (Fe.ofBytes point)).toBytes

/- NIKE types for X25519. -/

structure PublicKey    where data : Vector UInt8 keySize
structure SharedSecret where data : Vector UInt8 keySize

def derivePub (sk : PrivateKey) : PublicKey := ⟨curve25519 sk.data basepointBytes⟩

end Cryptlib.Primitives.NIKE.X25519_montgomery_ladder
