/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

namespace Cryptlib.Primitives.Cipher.AES

/-! # AES-128 and AES-256

Encryption direction only. The table S-box `sbox`, computed from its FIPS-197 definition rather
than transcribed, and the bit-serial `mul` are the specification. `subBytes` instead evaluates the
Boyar–Peralta S-box circuit, bitsliced across the bytes of the state, and `mixColumns` doubles with
mask arithmetic; both are proved equal to the table versions. The cipher and key schedule are
written without secret-dependent branches or secret-indexed memory accesses. Lean compiles through
C, and neither compiler is proven to preserve that, so the machine code is not verified to be
constant time.
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

def subBytesSpec (s : Array UInt8) : Array UInt8 := s.map fun b => sbox[b.toNat]!

/-- Each column multiplied by the fixed polynomial `{03}x³ + {01}x² + {01}x + {02}`. -/
def mixColumnsSpec (s : Array UInt8) : Array UInt8 :=
  Array.ofFn fun i : Fin 16 =>
    let a := fun j => s[4 * (i.val / 4) + j]!
    match i.val % 4 with
    | 0 => mul (a 0) 2 ^^^ mul (a 1) 3 ^^^ a 2 ^^^ a 3
    | 1 => a 0 ^^^ mul (a 1) 2 ^^^ mul (a 2) 3 ^^^ a 3
    | 2 => a 0 ^^^ a 1 ^^^ mul (a 2) 2 ^^^ mul (a 3) 3
    | _ => mul (a 0) 3 ^^^ a 1 ^^^ a 2 ^^^ mul (a 3) 2

/-! ## Constant-time S-box -/

/-- The S-box circuit of Boyar and Peralta, "A depth-16 circuit for the AES S-box" (2011): 128
gates, 34 of them AND, over any carrier of bitwise operations. `u0` is the most significant input
bit, and the result lists the output bits from the most significant down. -/
def sboxCircuit {α : Type} [XorOp α] [AndOp α] [Complement α] (u0 u1 u2 u3 u4 u5 u6 u7 : α) :
    Vector α 8 :=
  let t1 := u0 ^^^ u3
  let t2 := u0 ^^^ u5
  let t3 := u0 ^^^ u6
  let t4 := u3 ^^^ u5
  let t5 := u4 ^^^ u6
  let t6 := t1 ^^^ t5
  let t7 := u1 ^^^ u2
  let t8 := u7 ^^^ t6
  let t9 := u7 ^^^ t7
  let t10 := t6 ^^^ t7
  let t11 := u1 ^^^ u5
  let t12 := u2 ^^^ u5
  let t13 := t3 ^^^ t4
  let t14 := t6 ^^^ t11
  let t15 := t5 ^^^ t11
  let t16 := t5 ^^^ t12
  let t17 := t9 ^^^ t16
  let t18 := u3 ^^^ u7
  let t19 := t7 ^^^ t18
  let t20 := t1 ^^^ t19
  let t21 := u6 ^^^ u7
  let t22 := t7 ^^^ t21
  let t23 := t2 ^^^ t22
  let t24 := t2 ^^^ t10
  let t25 := t20 ^^^ t17
  let t26 := t3 ^^^ t16
  let t27 := t1 ^^^ t12
  let m1 := t13 &&& t6
  let m2 := t23 &&& t8
  let m3 := t14 ^^^ m1
  let m4 := t19 &&& u7
  let m5 := m4 ^^^ m1
  let m6 := t3 &&& t16
  let m7 := t22 &&& t9
  let m8 := t26 ^^^ m6
  let m9 := t20 &&& t17
  let m10 := m9 ^^^ m6
  let m11 := t1 &&& t15
  let m12 := t4 &&& t27
  let m13 := m12 ^^^ m11
  let m14 := t2 &&& t10
  let m15 := m14 ^^^ m11
  let m16 := m3 ^^^ m2
  let m17 := m5 ^^^ t24
  let m18 := m8 ^^^ m7
  let m19 := m10 ^^^ m15
  let m20 := m16 ^^^ m13
  let m21 := m17 ^^^ m15
  let m22 := m18 ^^^ m13
  let m23 := m19 ^^^ t25
  let m24 := m22 ^^^ m23
  let m25 := m22 &&& m20
  let m26 := m21 ^^^ m25
  let m27 := m20 ^^^ m21
  let m28 := m23 ^^^ m25
  let m29 := m28 &&& m27
  let m30 := m26 &&& m24
  let m31 := m20 &&& m23
  let m32 := m27 &&& m31
  let m33 := m27 ^^^ m25
  let m34 := m21 &&& m22
  let m35 := m24 &&& m34
  let m36 := m24 ^^^ m25
  let m37 := m21 ^^^ m29
  let m38 := m32 ^^^ m33
  let m39 := m23 ^^^ m30
  let m40 := m35 ^^^ m36
  let m41 := m38 ^^^ m40
  let m42 := m37 ^^^ m39
  let m43 := m37 ^^^ m38
  let m44 := m39 ^^^ m40
  let m45 := m42 ^^^ m41
  let m46 := m44 &&& t6
  let m47 := m40 &&& t8
  let m48 := m39 &&& u7
  let m49 := m43 &&& t16
  let m50 := m38 &&& t9
  let m51 := m37 &&& t17
  let m52 := m42 &&& t15
  let m53 := m45 &&& t27
  let m54 := m41 &&& t10
  let m55 := m44 &&& t13
  let m56 := m40 &&& t23
  let m57 := m39 &&& t19
  let m58 := m43 &&& t3
  let m59 := m38 &&& t22
  let m60 := m37 &&& t20
  let m61 := m42 &&& t1
  let m62 := m45 &&& t4
  let m63 := m41 &&& t2
  let l0 := m61 ^^^ m62
  let l1 := m50 ^^^ m56
  let l2 := m46 ^^^ m48
  let l3 := m47 ^^^ m55
  let l4 := m54 ^^^ m58
  let l5 := m49 ^^^ m61
  let l6 := m62 ^^^ l5
  let l7 := m46 ^^^ l3
  let l8 := m51 ^^^ m59
  let l9 := m52 ^^^ m53
  let l10 := m53 ^^^ l4
  let l11 := m60 ^^^ l2
  let l12 := m48 ^^^ m51
  let l13 := m50 ^^^ l0
  let l14 := m52 ^^^ m61
  let l15 := m55 ^^^ l1
  let l16 := m56 ^^^ l0
  let l17 := m57 ^^^ l1
  let l18 := m58 ^^^ l8
  let l19 := m63 ^^^ l4
  let l20 := l0 ^^^ l1
  let l21 := l1 ^^^ l7
  let l22 := l3 ^^^ l12
  let l23 := l18 ^^^ l2
  let l24 := l15 ^^^ l9
  let l25 := l6 ^^^ l10
  let l26 := l7 ^^^ l9
  let l27 := l8 ^^^ l10
  let l28 := l11 ^^^ l14
  let l29 := l11 ^^^ l17
  let s0 := l6 ^^^ l24
  let s1 := ~~~(l16 ^^^ l26)
  let s2 := ~~~(l19 ^^^ l28)
  let s3 := l6 ^^^ l21
  let s4 := l20 ^^^ l22
  let s5 := l25 ^^^ l29
  let s6 := ~~~(l13 ^^^ l27)
  let s7 := ~~~(l6 ^^^ l23)
  #v[s0, s1, s2, s3, s4, s5, s6, s7]

/-- Lane `k` of a bit plane. -/
def lane (k : Nat) (x : UInt64) : Bool := x.toBitVec.getLsbD k

private def bitTerm (b : UInt8) (j m : Nat) : UInt64 :=
  ((b >>> (7 - j).toUInt8) &&& 1).toUInt64 <<< m.toUInt64

/-- Bit `7 - j` of the first `n` bytes, byte `k` in lane `k`. -/
private def planeAux (s : Array UInt8) (j : Nat) : Nat → UInt64
  | 0 => 0
  | n + 1 => planeAux s j n ||| bitTerm s[n]! j n

/-- Byte `k` of the result, gathered from lane `k` of the output planes. -/
private def unpack (o : Vector UInt64 8) (k : Nat) : UInt8 :=
  let b := fun j : Fin 8 => ((o[j] >>> k.toUInt64) &&& 1).toUInt8
  b 0 <<< 7 ||| b 1 <<< 6 ||| b 2 <<< 5 ||| b 3 <<< 4 ||| b 4 <<< 3 ||| b 5 <<< 2 ||| b 6 <<< 1 |||
    b 7

/-- The S-box on up to 64 bytes at once, one byte per lane. -/
private def sliced (s : Array UInt8) : Array UInt8 :=
  let p := fun j => planeAux s j s.size
  let o := sboxCircuit (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7)
  Array.ofFn fun k : Fin s.size => unpack o k.val

def subBytes (s : Array UInt8) : Array UInt8 :=
  if s.size ≤ 64 then sliced s else s.map fun b => (sliced #[b])[0]!

/-- Multiplication by `x`, reducing with a mask rather than a branch. -/
def xtime (x : UInt8) : UInt8 := (x <<< 1) ^^^ ((0x1b : UInt8) &&& ((0 : UInt8) - (x >>> 7)))

def mixColumns (s : Array UInt8) : Array UInt8 :=
  Array.ofFn fun i : Fin 16 =>
    let a := fun j => s[4 * (i.val / 4) + j]!
    let d := fun j => xtime (a j)
    match i.val % 4 with
    | 0 => d 0 ^^^ d 1 ^^^ a 1 ^^^ a 2 ^^^ a 3
    | 1 => a 0 ^^^ d 1 ^^^ d 2 ^^^ a 2 ^^^ a 3
    | 2 => a 0 ^^^ a 1 ^^^ d 2 ^^^ d 3 ^^^ a 3
    | _ => d 0 ^^^ a 0 ^^^ a 1 ^^^ a 2 ^^^ d 3

/-! ### Agreement with the specification -/

section
local instance : XorOp Bool := ⟨Bool.xor⟩
local instance : AndOp Bool := ⟨and⟩
local instance : Complement Bool := ⟨not⟩

private def ofBits (o : Vector Bool 8) : UInt8 :=
  o[0].toUInt8 <<< 7 ||| o[1].toUInt8 <<< 6 ||| o[2].toUInt8 <<< 5 ||| o[3].toUInt8 <<< 4 |||
    o[4].toUInt8 <<< 3 ||| o[5].toUInt8 <<< 2 ||| o[6].toUInt8 <<< 1 ||| o[7].toUInt8

private def bit (b : UInt8) (i : Nat) : Bool := b.toBitVec.getLsbD i

/-- The circuit on the bits of one byte. -/
private def sboxBits (b : UInt8) : UInt8 :=
  ofBits
    (sboxCircuit (bit b 7) (bit b 6) (bit b 5) (bit b 4) (bit b 3) (bit b 2) (bit b 1) (bit b 0))

private theorem sboxBits_eq_fin :
    ∀ i : Fin 256, sboxBits (UInt8.ofNat i) = sboxByte (UInt8.ofNat i) := by
  decide +kernel

theorem sboxBits_eq (b : UInt8) : sboxBits b = sboxByte b := by
  simpa using sboxBits_eq_fin ⟨b.toNat, b.toNat_lt⟩

private theorem lane_xor (k : Nat) (a b : UInt64) : lane k (a ^^^ b) = (lane k a ^^^ lane k b) := by
  simp [lane]; rfl

private theorem lane_and (k : Nat) (a b : UInt64) : lane k (a &&& b) = (lane k a &&& lane k b) := by
  simp [lane]; rfl

private theorem lane_not (k : Nat) (hk : k < 64) (a : UInt64) : lane k (~~~a) = ~~~(lane k a) := by
  show _ = not _
  simp [lane, hk]

/-- The bitsliced circuit computes the circuit in every lane. -/
theorem sboxCircuit_lane (k : Nat) (hk : k < 64) (u0 u1 u2 u3 u4 u5 u6 u7 : UInt64) :
    (sboxCircuit u0 u1 u2 u3 u4 u5 u6 u7).map (lane k) =
      sboxCircuit (lane k u0) (lane k u1) (lane k u2) (lane k u3) (lane k u4) (lane k u5)
        (lane k u6) (lane k u7) := by
  simp only [sboxCircuit, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, lane_xor,
    lane_and, lane_not k hk]

private theorem lane_bitTerm (b : UInt8) (j k m : Nat) (hj : j < 8) (hk : k < 64) (hm : m < 64) :
    lane k (bitTerm b j m) = (decide (k = m) && bit b (7 - j)) := by
  simp [lane, bitTerm, bit]
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega : 7 - j < 8),
    Nat.mod_eq_of_lt (by omega : 7 - j < 64)]
  by_cases h : k = m
  · subst h; simp [hk]; omega
  · simp [h]; omega

private theorem lane_planeAux (s : Array UInt8) (j k : Nat) (hj : j < 8) (hk : k < 64) :
    ∀ n, n ≤ 64 → lane k (planeAux s j n) = (decide (k < n) && bit s[k]! (7 - j))
  | 0, _ => by simp [planeAux, lane]
  | n + 1, hn => by
    have ih := lane_planeAux s j k hj hk n (by omega)
    simp only [planeAux]
    rw [show lane k (planeAux s j n ||| bitTerm s[n]! j n) =
        (lane k (planeAux s j n) || lane k (bitTerm s[n]! j n)) by simp [lane]]
    rw [ih, lane_bitTerm _ _ _ _ hj hk (by omega)]
    by_cases h : k = n
    · subst h; simp
    · have : (k < n + 1) = (k < n) := by apply propext; omega
      simp [h, this]

private theorem lane_extract (x : UInt64) (k : Nat) (hk : k < 64) :
    ((x >>> k.toUInt64) &&& 1).toUInt8 = (lane k x).toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp [lane, Nat.mod_eq_of_lt hk]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat >>> k) with h | h <;>
    simp [BitVec.getLsbD, Nat.testBit, Nat.one_and_eq_mod_two, h] <;> rfl

private theorem unpack_eq (o : Vector UInt64 8) (k : Nat) (hk : k < 64) :
    unpack o k = ofBits (o.map (lane k)) := by
  simp only [unpack, ofBits, lane_extract _ _ hk, Vector.getElem_map]
  rfl

private theorem sliced_getElem (s : Array UInt8) (hs : s.size ≤ 64) (k : Nat) (hk : k < s.size) :
    (sliced s)[k]'(by simp [sliced, hk]) = sboxByte s[k] := by
  simp only [sliced, Array.getElem_ofFn]
  rw [unpack_eq _ _ (by omega), sboxCircuit_lane _ (by omega)]
  have hp : ∀ j, j < 8 → lane k (planeAux s j s.size) = bit s[k] (7 - j) := fun j hj => by
    rw [lane_planeAux s j k hj (by omega) s.size hs, decide_eq_true hk, Bool.true_and,
      getElem!_pos s k hk]
  simp only [hp 0 (by omega), hp 1 (by omega), hp 2 (by omega), hp 3 (by omega), hp 4 (by omega),
    hp 5 (by omega), hp 6 (by omega), hp 7 (by omega)]
  exact sboxBits_eq s[k]

private theorem sbox_getElem (b : UInt8) : sbox[b.toNat]! = sboxByte b := by
  simp [sbox, getElem!_pos, b.toNat_lt]

theorem subBytes_eq_spec : subBytes = subBytesSpec := by
  funext s
  apply Array.ext
  · simp [subBytes, subBytesSpec, sliced]; split <;> simp
  · intro k h1 h2
    have hk : k < s.size := by simpa [subBytesSpec] using h2
    simp only [subBytesSpec, Array.getElem_map, sbox_getElem]
    unfold subBytes
    split
    · next hs => exact sliced_getElem s hs k hk
    · simp only [Array.getElem_map]
      simp only [getElem!_pos (sliced #[s[k]]) 0 (by simp [sliced])]
      exact sliced_getElem #[s[k]] (by simp) 0 (by simp)

end

theorem xtime_eq (x : UInt8) : xtime x = mul x 2 := by
  have : ∀ i : Fin 256, xtime (UInt8.ofNat i) = mul (UInt8.ofNat i) 2 := by decide +kernel
  simpa using this ⟨x.toNat, x.toNat_lt⟩

theorem xtime_xor_eq (x : UInt8) : xtime x ^^^ x = mul x 3 := by
  have : ∀ i : Fin 256, xtime (UInt8.ofNat i) ^^^ UInt8.ofNat i = mul (UInt8.ofNat i) 3 := by
    decide +kernel
  simpa using this ⟨x.toNat, x.toNat_lt⟩

theorem mixColumns_eq_spec : mixColumns = mixColumnsSpec := by
  funext s
  apply Array.ext
  · simp [mixColumns, mixColumnsSpec]
  · intro i h1 h2
    simp only [mixColumns, mixColumnsSpec, Array.getElem_ofFn, ← xtime_eq, ← xtime_xor_eq]
    split <;> ac_rfl

/-! ## Key schedule and cipher -/

/-- The key schedule round constant `x^i` in `GF(2^8)`. -/
private def rcon (i : Nat) : UInt8 := Id.run do
  let mut c : UInt8 := 1
  for _ in [0:i] do
    c := mul c 2
  return c

/-- The FIPS-197 §5.2 key schedule for an `nk`-word key, `4 * (nk + 7)` words and `nk + 7` round
keys, with `sub` as SubWord. -/
private def expand (sub : Array UInt8 → Array UInt8) (nk : Nat) (key : Array UInt8) :
    Array UInt8 := Id.run do
  let mut w := key
  for i in [nk:4 * (nk + 7)] do
    let mut t := #[w[4*i - 4]!, w[4*i - 3]!, w[4*i - 2]!, w[4*i - 1]!]
    if i % nk == 0 then
      let u := sub #[t[1]!, t[2]!, t[3]!, t[0]!]
      t := u.set! 0 (u[0]! ^^^ rcon (i / nk - 1))
    else if nk > 6 && i % nk == 4 then
      t := sub t
    for j in [0:4] do
      w := w.push (w[4*(i - nk) + j]! ^^^ t[j]!)
  return w

/-- The AES-256 key schedule: sixty 4-byte words, fifteen round keys. -/
def expandKey (key : Vector UInt8 32) : Array UInt8 := expand subBytes 8 key.toArray

/-- The AES-128 key schedule: forty-four 4-byte words, eleven round keys. -/
def expandKey128 (key : Vector UInt8 16) : Array UInt8 := expand subBytes 4 key.toArray

def expandKeySpec (key : Vector UInt8 32) : Array UInt8 := expand subBytesSpec 8 key.toArray

def expandKey128Spec (key : Vector UInt8 16) : Array UInt8 := expand subBytesSpec 4 key.toArray

theorem expandKey_eq_spec : expandKey = expandKeySpec := by
  funext key
  simp only [expandKey, expandKeySpec, subBytes_eq_spec]

theorem expandKey128_eq_spec : expandKey128 = expandKey128Spec := by
  funext key
  simp only [expandKey128, expandKey128Spec, subBytes_eq_spec]

/-- Byte `i` of the state is row `i % 4`, column `i / 4`; row `r` rotates left by `r` columns. -/
def shiftRows (s : Array UInt8) : Array UInt8 :=
  Array.ofFn fun i : Fin 16 => s[(i.val + 4 * (i.val % 4)) % 16]!

private def addRoundKey (s : Array UInt8) (rk : Array UInt8) (round : Nat) : Array UInt8 :=
  Array.ofFn fun i : Fin 16 => s[i.val]! ^^^ rk[16 * round + i.val]!

/-- The FIPS-197 cipher on one block, against an expanded key schedule, with the given SubBytes
and MixColumns; the round count follows from the schedule's length. -/
private def cipher (sub mix : Array UInt8 → Array UInt8) (rk : Array UInt8)
    (input : Vector UInt8 16) : Vector UInt8 16 := Id.run do
  let rounds := rk.size / 16 - 1
  let mut s := addRoundKey input.toArray rk 0
  for round in [1:rounds] do
    s := addRoundKey (mix (shiftRows (sub s))) rk round
  s := addRoundKey (shiftRows (sub s)) rk rounds
  return Vector.ofFn fun i : Fin 16 => s[i.val]!

/-- AES on one block, against an expanded key schedule. -/
def encryptBlock (rk : Array UInt8) (input : Vector UInt8 16) : Vector UInt8 16 :=
  cipher subBytes mixColumns rk input

def encryptBlockSpec (rk : Array UInt8) (input : Vector UInt8 16) : Vector UInt8 16 :=
  cipher subBytesSpec mixColumnsSpec rk input

theorem encryptBlock_eq_spec : encryptBlock = encryptBlockSpec := by
  funext rk input
  simp only [encryptBlock, encryptBlockSpec, subBytes_eq_spec, mixColumns_eq_spec]

/-- Expand the key and encrypt one block. -/
def encryptBlockWithKey (key : Vector UInt8 32) (input : Vector UInt8 16) : Vector UInt8 16 :=
  encryptBlock (expandKey key) input

/-- Expand an AES-128 key and encrypt one block. -/
def encryptBlockWithKey128 (key : Vector UInt8 16) (input : Vector UInt8 16) : Vector UInt8 16 :=
  encryptBlock (expandKey128 key) input

end Cryptlib.Primitives.Cipher.AES
