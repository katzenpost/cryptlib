/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

namespace Cryptlib.Primitives.Cipher.AES

/-! # AES-128 and AES-256

Encryption direction only. The S-box is computed from its FIPS-197 definition rather than
transcribed. Not constant time.
-/

/-- Multiplication in `GF(2^8)` modulo AES's `x^8 + x^4 + x^3 + x + 1`. -/
def mul (a b : UInt8) : UInt8 := Id.run do
  let mut x := a
  let mut y := b
  let mut p : UInt8 := 0
  for _ in [0:8] do
    if y &&& 1 != 0 then
      p := p ^^^ x
    let carry := x &&& 0x80
    x := x <<< 1
    if carry != 0 then
      x := x ^^^ 0x1b
    y := y >>> 1
  return p

/-- The multiplicative inverse in `GF(2^8)`, computed as `a^254`; `inv 0 = 0`. -/
def inv (a : UInt8) : UInt8 := Id.run do
  let mut square := a
  let mut acc : UInt8 := 1
  for _ in [0:7] do
    square := mul square square
    acc := mul acc square
  return acc

private def rotl (x : UInt8) (n : UInt8) : UInt8 := (x <<< n) ||| (x >>> (8 - n))

/-- FIPS-197 §5.1.1: invert in `GF(2^8)`, then apply the affine transformation over `GF(2)`. -/
def sboxByte (a : UInt8) : UInt8 :=
  let b := inv a
  b ^^^ rotl b 1 ^^^ rotl b 2 ^^^ rotl b 3 ^^^ rotl b 4 ^^^ 0x63

/-- `sboxByte` tabulated over all 256 inputs. -/
def sbox : Array UInt8 := (Array.range 256).map fun i => sboxByte (UInt8.ofNat i)

/-- The key schedule round constant `x^i` in `GF(2^8)`. -/
private def rcon (i : Nat) : UInt8 := Id.run do
  let mut c : UInt8 := 1
  for _ in [0:i] do
    c := mul c 2
  return c

/-- The FIPS-197 §5.2 key schedule for an `nk`-word key: `4 * (nk + 7)` words, `nk + 7` round
keys. -/
private def expand (nk : Nat) (key : Array UInt8) : Array UInt8 := Id.run do
  let mut w := key
  for i in [nk:4 * (nk + 7)] do
    let mut t := #[w[4*i - 4]!, w[4*i - 3]!, w[4*i - 2]!, w[4*i - 1]!]
    if i % nk == 0 then
      t := #[sbox[t[1]!.toNat]! ^^^ rcon (i / nk - 1), sbox[t[2]!.toNat]!,
             sbox[t[3]!.toNat]!, sbox[t[0]!.toNat]!]
    else if nk > 6 && i % nk == 4 then
      t := t.map fun b => sbox[b.toNat]!
    for j in [0:4] do
      w := w.push (w[4*(i - nk) + j]! ^^^ t[j]!)
  return w

/-- The AES-256 key schedule: sixty 4-byte words, fifteen round keys. -/
def expandKey (key : Vector UInt8 32) : Array UInt8 := expand 8 key.toArray

/-- The AES-128 key schedule: forty-four 4-byte words, eleven round keys. -/
def expandKey128 (key : Vector UInt8 16) : Array UInt8 := expand 4 key.toArray

def subBytes (s : Array UInt8) : Array UInt8 := s.map fun b => sbox[b.toNat]!

/-- Byte `i` of the state is row `i % 4`, column `i / 4`; row `r` rotates left by `r` columns. -/
def shiftRows (s : Array UInt8) : Array UInt8 :=
  Array.ofFn fun i : Fin 16 => s[(i.val + 4 * (i.val % 4)) % 16]!

/-- Each column multiplied by the fixed polynomial `{03}x³ + {01}x² + {01}x + {02}`. -/
def mixColumns (s : Array UInt8) : Array UInt8 :=
  Array.ofFn fun i : Fin 16 =>
    let a := fun j => s[4 * (i.val / 4) + j]!
    match i.val % 4 with
    | 0 => mul (a 0) 2 ^^^ mul (a 1) 3 ^^^ a 2 ^^^ a 3
    | 1 => a 0 ^^^ mul (a 1) 2 ^^^ mul (a 2) 3 ^^^ a 3
    | 2 => a 0 ^^^ a 1 ^^^ mul (a 2) 2 ^^^ mul (a 3) 3
    | _ => mul (a 0) 3 ^^^ a 1 ^^^ a 2 ^^^ mul (a 3) 2

private def addRoundKey (s : Array UInt8) (rk : Array UInt8) (round : Nat) : Array UInt8 :=
  Array.ofFn fun i : Fin 16 => s[i.val]! ^^^ rk[16 * round + i.val]!

/-- AES on one block, against an expanded key schedule; the round count follows from its length. -/
def encryptBlock (rk : Array UInt8) (input : Vector UInt8 16) : Vector UInt8 16 := Id.run do
  let rounds := rk.size / 16 - 1
  let mut s := addRoundKey input.toArray rk 0
  for round in [1:rounds] do
    s := addRoundKey (mixColumns (shiftRows (subBytes s))) rk round
  s := addRoundKey (shiftRows (subBytes s)) rk rounds
  return Vector.ofFn fun i : Fin 16 => s[i.val]!

/-- Expand the key and encrypt one block. -/
def encryptBlockWithKey (key : Vector UInt8 32) (input : Vector UInt8 16) : Vector UInt8 16 :=
  encryptBlock (expandKey key) input

/-- Expand an AES-128 key and encrypt one block. -/
def encryptBlockWithKey128 (key : Vector UInt8 16) (input : Vector UInt8 16) : Vector UInt8 16 :=
  encryptBlock (expandKey128 key) input

end Cryptlib.Primitives.Cipher.AES
