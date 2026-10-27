/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

namespace Cryptlib.Primitives.Cipher.ChaCha20

/-! # ChaCha20 (original/Bernstein construction, 64-bit nonce)

Single-block function; `ChaChaPoly` builds the RFC 8439 variant on top of it. `blockSpec` is the
algorithm as written in the RFC, over an array of words; `block` keeps the 16 words in unboxed
fields, and `block_eq_spec` proves the two equal. -/

private def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

private def sigma0 : UInt32 := 0x61707865
private def sigma1 : UInt32 := 0x3320646e
private def sigma2 : UInt32 := 0x79622d32
private def sigma3 : UInt32 := 0x6b206574

/-- 4 little-endian bytes as a word. -/
private def leWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- A word as 4 little-endian bytes. -/
private def leBytes (w : UInt32) : Array UInt8 :=
  #[w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

private def quarterRound (s : Array UInt32) (a b c d : Nat) : Array UInt32 := Id.run do
  let mut s := s
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 16)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 12)
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 8)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 7)
  return s

/-- One 64-byte ChaCha20 block: 32-byte key, 8-byte nonce, 64-bit counter (as two 32-bit
little-endian words). -/
def blockSpec (key : Array UInt8) (nonce : Array UInt8) (counterLo counterHi : UInt32) :
    Array UInt8 := Id.run do
  let keyWords : Array UInt32 := Array.ofFn fun i : Fin 8 =>
    leWord key[4*i.val]! key[4*i.val+1]! key[4*i.val+2]! key[4*i.val+3]!
  let nonceWords : Array UInt32 := Array.ofFn fun i : Fin 2 =>
    leWord nonce[4*i.val]! nonce[4*i.val+1]! nonce[4*i.val+2]! nonce[4*i.val+3]!
  let init : Array UInt32 :=
    #[sigma0, sigma1, sigma2, sigma3] ++ keyWords ++ #[counterLo, counterHi] ++ nonceWords
  let mut s := init
  for _ in [0:10] do
    -- Column rounds.
    s := quarterRound s 0 4 8 12
    s := quarterRound s 1 5 9 13
    s := quarterRound s 2 6 10 14
    s := quarterRound s 3 7 11 15
    -- Diagonal rounds.
    s := quarterRound s 0 5 10 15
    s := quarterRound s 1 6 11 12
    s := quarterRound s 2 7 8 13
    s := quarterRound s 3 4 9 14
  let out : Array UInt32 := Array.ofFn fun i : Fin 16 => s[i.val]! + init[i.val]!
  return (Array.range 16).foldl (fun acc i => acc ++ leBytes out[i]!) #[]

/-! ## The block over unboxed words -/

/-- The 16-word state. -/
structure Words where
  x0 : UInt32
  x1 : UInt32
  x2 : UInt32
  x3 : UInt32
  x4 : UInt32
  x5 : UInt32
  x6 : UInt32
  x7 : UInt32
  x8 : UInt32
  x9 : UInt32
  x10 : UInt32
  x11 : UInt32
  x12 : UInt32
  x13 : UInt32
  x14 : UInt32
  x15 : UInt32

def Words.toArray (w : Words) : Array UInt32 :=
  #[w.x0, w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7, w.x8, w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15]

@[inline] private def qr (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b; let d := rotl (d ^^^ a) 16
  let c := c + d; let b := rotl (b ^^^ c) 12
  let a := a + b; let d := rotl (d ^^^ a) 8
  let c := c + d; let b := rotl (b ^^^ c) 7
  (a, b, c, d)

/-- A column round and a diagonal round. -/
def doubleRound (w : Words) : Words :=
  let (x0, x4, x8, x12) := qr w.x0 w.x4 w.x8 w.x12
  let (x1, x5, x9, x13) := qr w.x1 w.x5 w.x9 w.x13
  let (x2, x6, x10, x14) := qr w.x2 w.x6 w.x10 w.x14
  let (x3, x7, x11, x15) := qr w.x3 w.x7 w.x11 w.x15
  let (x0, x5, x10, x15) := qr x0 x5 x10 x15
  let (x1, x6, x11, x12) := qr x1 x6 x11 x12
  let (x2, x7, x8, x13) := qr x2 x7 x8 x13
  let (x3, x4, x9, x14) := qr x3 x4 x9 x14
  ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩

def rounds : Nat → Words → Words
  | 0, w => w
  | n + 1, w => rounds n (doubleRound w)

def Words.add (a b : Words) : Words :=
  ⟨a.x0 + b.x0, a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.x4 + b.x4, a.x5 + b.x5, a.x6 + b.x6, a.x7 + b.x7, a.x8 + b.x8, a.x9 + b.x9, a.x10 + b.x10, a.x11 + b.x11, a.x12 + b.x12, a.x13 + b.x13, a.x14 + b.x14, a.x15 + b.x15⟩

/-- The words as 64 little-endian bytes. -/
def Words.bytes (w : Words) : Array UInt8 :=
  #[w.x0.toUInt8, (w.x0 >>> 8).toUInt8, (w.x0 >>> 16).toUInt8, (w.x0 >>> 24).toUInt8, w.x1.toUInt8, (w.x1 >>> 8).toUInt8, (w.x1 >>> 16).toUInt8, (w.x1 >>> 24).toUInt8, w.x2.toUInt8, (w.x2 >>> 8).toUInt8, (w.x2 >>> 16).toUInt8, (w.x2 >>> 24).toUInt8, w.x3.toUInt8, (w.x3 >>> 8).toUInt8, (w.x3 >>> 16).toUInt8, (w.x3 >>> 24).toUInt8, w.x4.toUInt8, (w.x4 >>> 8).toUInt8, (w.x4 >>> 16).toUInt8, (w.x4 >>> 24).toUInt8, w.x5.toUInt8, (w.x5 >>> 8).toUInt8, (w.x5 >>> 16).toUInt8, (w.x5 >>> 24).toUInt8, w.x6.toUInt8, (w.x6 >>> 8).toUInt8, (w.x6 >>> 16).toUInt8, (w.x6 >>> 24).toUInt8, w.x7.toUInt8, (w.x7 >>> 8).toUInt8, (w.x7 >>> 16).toUInt8, (w.x7 >>> 24).toUInt8, w.x8.toUInt8, (w.x8 >>> 8).toUInt8, (w.x8 >>> 16).toUInt8, (w.x8 >>> 24).toUInt8, w.x9.toUInt8, (w.x9 >>> 8).toUInt8, (w.x9 >>> 16).toUInt8, (w.x9 >>> 24).toUInt8, w.x10.toUInt8, (w.x10 >>> 8).toUInt8, (w.x10 >>> 16).toUInt8, (w.x10 >>> 24).toUInt8, w.x11.toUInt8, (w.x11 >>> 8).toUInt8, (w.x11 >>> 16).toUInt8, (w.x11 >>> 24).toUInt8, w.x12.toUInt8, (w.x12 >>> 8).toUInt8, (w.x12 >>> 16).toUInt8, (w.x12 >>> 24).toUInt8, w.x13.toUInt8, (w.x13 >>> 8).toUInt8, (w.x13 >>> 16).toUInt8, (w.x13 >>> 24).toUInt8, w.x14.toUInt8, (w.x14 >>> 8).toUInt8, (w.x14 >>> 16).toUInt8, (w.x14 >>> 24).toUInt8, w.x15.toUInt8, (w.x15 >>> 8).toUInt8, (w.x15 >>> 16).toUInt8, (w.x15 >>> 24).toUInt8]

def initWords (key : Array UInt8) (nonce : Array UInt8) (counterLo counterHi : UInt32) : Words :=
  ⟨sigma0,
   sigma1,
   sigma2,
   sigma3,
   leWord key[0]! key[1]! key[2]! key[3]!,
   leWord key[4]! key[5]! key[6]! key[7]!,
   leWord key[8]! key[9]! key[10]! key[11]!,
   leWord key[12]! key[13]! key[14]! key[15]!,
   leWord key[16]! key[17]! key[18]! key[19]!,
   leWord key[20]! key[21]! key[22]! key[23]!,
   leWord key[24]! key[25]! key[26]! key[27]!,
   leWord key[28]! key[29]! key[30]! key[31]!,
   counterLo,
   counterHi,
   leWord nonce[0]! nonce[1]! nonce[2]! nonce[3]!,
   leWord nonce[4]! nonce[5]! nonce[6]! nonce[7]!⟩

/-- One 64-byte ChaCha20 block, equal to `blockSpec` (`block_eq_spec`). -/
def block (key : Array UInt8) (nonce : Array UInt8) (counterLo counterHi : UInt32) : Array UInt8 :=
  let w := initWords key nonce counterLo counterHi
  ((rounds 10 w).add w).bytes

/-! ## `block` is `blockSpec` -/

private theorem qr_0 (w : Words) : quarterRound w.toArray 0 4 8 12 =
    let (a, b, c, d) := qr w.x0 w.x4 w.x8 w.x12
    { w with x0 := a, x4 := b, x8 := c, x12 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem qr_1 (w : Words) : quarterRound w.toArray 1 5 9 13 =
    let (a, b, c, d) := qr w.x1 w.x5 w.x9 w.x13
    { w with x1 := a, x5 := b, x9 := c, x13 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem qr_2 (w : Words) : quarterRound w.toArray 2 6 10 14 =
    let (a, b, c, d) := qr w.x2 w.x6 w.x10 w.x14
    { w with x2 := a, x6 := b, x10 := c, x14 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem qr_3 (w : Words) : quarterRound w.toArray 3 7 11 15 =
    let (a, b, c, d) := qr w.x3 w.x7 w.x11 w.x15
    { w with x3 := a, x7 := b, x11 := c, x15 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem qr_4 (w : Words) : quarterRound w.toArray 0 5 10 15 =
    let (a, b, c, d) := qr w.x0 w.x5 w.x10 w.x15
    { w with x0 := a, x5 := b, x10 := c, x15 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem qr_5 (w : Words) : quarterRound w.toArray 1 6 11 12 =
    let (a, b, c, d) := qr w.x1 w.x6 w.x11 w.x12
    { w with x1 := a, x6 := b, x11 := c, x12 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem qr_6 (w : Words) : quarterRound w.toArray 2 7 8 13 =
    let (a, b, c, d) := qr w.x2 w.x7 w.x8 w.x13
    { w with x2 := a, x7 := b, x8 := c, x13 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem qr_7 (w : Words) : quarterRound w.toArray 3 4 9 14 =
    let (a, b, c, d) := qr w.x3 w.x4 w.x9 w.x14
    { w with x3 := a, x4 := b, x9 := c, x14 := d }.toArray := by
  simp [quarterRound, Words.toArray, qr, Array.set!, Array.setIfInBounds]

private theorem rounds_toArray (l : List Nat) (w : Words) :
    l.foldl (fun s _ => quarterRound (quarterRound (quarterRound (quarterRound (quarterRound
      (quarterRound (quarterRound (quarterRound s 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15)
      0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14) w.toArray = (rounds l.length w).toArray := by
  induction l generalizing w with
  | nil => rfl
  | cons _ l ih =>
    simp only [List.foldl_cons, qr_0, qr_1, qr_2, qr_3, qr_4, qr_5, qr_6, qr_7]
    exact ih (doubleRound w)

private theorem bytes_eq (r w : Words) :
    (Array.range 16).foldl (fun acc i =>
      acc ++ leBytes (Array.ofFn fun i : Fin 16 => r.toArray[i.val]! + w.toArray[i.val]!)[i]!) #[] =
      (r.add w).bytes := by
  simp [Words.toArray, Words.add, Words.bytes, leBytes, Array.range, Array.ofFn_succ]

theorem block_eq_spec (key nonce : Array UInt8) (counterLo counterHi : UInt32) :
    block key nonce counterLo counterHi = blockSpec key nonce counterLo counterHi := by
  have hinit : #[sigma0, sigma1, sigma2, sigma3] ++ (Array.ofFn fun i : Fin 8 =>
      leWord key[4*i.val]! key[4*i.val+1]! key[4*i.val+2]! key[4*i.val+3]!) ++
      #[counterLo, counterHi] ++ (Array.ofFn fun i : Fin 2 =>
      leWord nonce[4*i.val]! nonce[4*i.val+1]! nonce[4*i.val+2]! nonce[4*i.val+3]!) =
      (initWords key nonce counterLo counterHi).toArray := by
    simp [initWords, Words.toArray, Array.ofFn_succ]
  simp only [block, blockSpec, Id.run, hinit]
  generalize initWords key nonce counterLo counterHi = w
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, rounds_toArray]
  have h10 : (List.range' 0 [:10].size).length = 10 := by decide
  rw [h10, ← bytes_eq]
  rfl

/-- The first 32 bytes of the ChaCha20 keystream for `key`, with zero nonce and counter. -/
def keystream32 (key : Array UInt8) : Array UInt8 :=
  (block key (Array.replicate 8 0) 0 0).extract 0 32

end Cryptlib.Primitives.Cipher.ChaCha20
