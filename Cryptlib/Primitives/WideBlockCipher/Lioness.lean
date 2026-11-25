/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Primitives.Cipher.ChaCha20
import Cryptlib.Primitives.Hash.Blake2b
import Cryptlib.Primitives.MAC.MAC
import Cryptlib.Primitives.StreamCipher.StreamCipher
import Cryptlib.Primitives.WideBlockCipher.WideBlockCipher
import Cryptlib.Util.Bytes

namespace Cryptlib.Primitives.WideBlockCipher.Lioness

open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Util.Bytes

/-! # Lioness

The Anderson-Biham wide-block cipher: a four-round unbalanced Feistel network over a stream cipher
`S` and a keyed hash `H`. The block is split into `L`, as long as the hash output, and the rest `R`:

    R ← R ⊕ S(L ⊕ k1, iv1)
    L ← L ⊕ H(k2 ‖ iv2, R)
    R ← R ⊕ S(L ⊕ k3, iv3)
    L ← L ⊕ H(k4 ‖ iv4, R)

Decryption runs the rounds in reverse. Each round is an involution, so the round trip holds for
any `S` and `H`, any key and IV, and any block length. The key is `k1 ‖ k2 ‖ k3 ‖ k4` and the IV is
`iv1 ‖ iv2 ‖ iv3 ‖ iv4`, as in rust-lioness. A block no longer than the hash output is all `L`;
rust-lioness rejects such blocks. -/

/-- `a ⊕ b`, as long as `a`. Bytes that `b` lacks count as zero. -/
def xor (a b : ByteArray) : ByteArray := ⟨a.data.mapIdx fun i x => x ^^^ b.data.getD i 0⟩

@[simp] theorem xor_size (a b : ByteArray) : (xor a b).size = a.size := by
  show (a.data.mapIdx _).size = a.data.size
  simp

@[simp] theorem xor_xor (a b : ByteArray) : xor (xor a b) b = a := by
  apply ByteArray.ext
  apply Array.ext <;> simp [xor, UInt8.xor_assoc]

/-- The block as `(L, R)`, with `L` the first `n` bytes. -/
def split (n : Nat) (msg : ByteArray) : ByteArray × ByteArray :=
  (msg.extract 0 (min n msg.size), msg.extract (min n msg.size) msg.size)

/-- `R ← R ⊕ S(L ⊕ k, iv)`. -/
def streamRound (s : StreamCipher) (k iv : ByteArray) (x : ByteArray × ByteArray) :
    ByteArray × ByteArray :=
  (x.1, xor x.2 (s.keystream (xor x.1 k) iv x.2.size))

/-- `L ← L ⊕ H(k, R)`. -/
def hashRound (h : MAC) (k : ByteArray) (x : ByteArray × ByteArray) : ByteArray × ByteArray :=
  (xor x.1 (ofVector (h.mac k x.2)), x.2)

@[simp] theorem streamRound_streamRound (s : StreamCipher) (k iv : ByteArray)
    (x : ByteArray × ByteArray) : streamRound s k iv (streamRound s k iv x) = x := by
  simp [streamRound]

@[simp] theorem hashRound_hashRound (h : MAC) (k : ByteArray) (x : ByteArray × ByteArray) :
    hashRound h k (hashRound h k x) = x := by
  simp [hashRound]

@[simp] theorem streamRound_size_fst (s : StreamCipher) (k iv : ByteArray)
    (x : ByteArray × ByteArray) : (streamRound s k iv x).1.size = x.1.size := rfl

@[simp] theorem streamRound_size_snd (s : StreamCipher) (k iv : ByteArray)
    (x : ByteArray × ByteArray) : (streamRound s k iv x).2.size = x.2.size := by
  simp [streamRound]

@[simp] theorem hashRound_size_fst (h : MAC) (k : ByteArray) (x : ByteArray × ByteArray) :
    (hashRound h k x).1.size = x.1.size := by
  simp [hashRound]

@[simp] theorem hashRound_size_snd (h : MAC) (k : ByteArray) (x : ByteArray × ByteArray) :
    (hashRound h k x).2.size = x.2.size := rfl

theorem join_split (n : Nat) (msg : ByteArray) : (split n msg).1 ++ (split n msg).2 = msg :=
  append_extract msg (min n msg.size) (Nat.min_le_right _ _)

/-- Splitting a rejoined pair gives the pair back, when `L` has the length `split` would cut. -/
theorem split_join (n : Nat) (x : ByteArray × ByteArray)
    (hx : x.1.size = min n (x.1.size + x.2.size)) : split n (x.1 ++ x.2) = x := by
  obtain ⟨l, r⟩ := x
  simp only [split, ByteArray.size_append] at hx ⊢
  rw [← hx, extract_append_left, extract_append_right]

/-- The four round keys and IVs cut from the key and IV: `(k1, iv1, k2 ‖ iv2, k3, iv3, k4 ‖ iv4)`. -/
structure RoundKeys where
  k1 : ByteArray
  iv1 : ByteArray
  k2 : ByteArray
  k3 : ByteArray
  iv3 : ByteArray
  k4 : ByteArray

def roundKeys (s : StreamCipher) (h : MAC) (key : Array UInt8) (iv : ByteArray) : RoundKeys :=
  let key : ByteArray := ⟨key⟩
  let sk := s.keySize
  let hk := h.keySize
  let n := s.ivSize
  { k1 := key.extract 0 sk
    iv1 := iv.extract 0 n
    k2 := key.extract sk (sk + hk) ++ iv.extract n (2 * n)
    k3 := key.extract (sk + hk) (2 * sk + hk)
    iv3 := iv.extract (2 * n) (3 * n)
    k4 := key.extract (2 * sk + hk) (2 * sk + 2 * hk) ++ iv.extract (3 * n) (4 * n) }

def encryptRounds (s : StreamCipher) (h : MAC) (k : RoundKeys) (x : ByteArray × ByteArray) :
    ByteArray × ByteArray :=
  hashRound h k.k4 (streamRound s k.k3 k.iv3 (hashRound h k.k2 (streamRound s k.k1 k.iv1 x)))

def decryptRounds (s : StreamCipher) (h : MAC) (k : RoundKeys) (x : ByteArray × ByteArray) :
    ByteArray × ByteArray :=
  streamRound s k.k1 k.iv1 (hashRound h k.k2 (streamRound s k.k3 k.iv3 (hashRound h k.k4 x)))

def encrypt (s : StreamCipher) (h : MAC) (key : Array UInt8) (iv msg : ByteArray) : ByteArray :=
  let y := encryptRounds s h (roundKeys s h key iv) (split h.tagSize msg)
  y.1 ++ y.2

def decrypt (s : StreamCipher) (h : MAC) (key : Array UInt8) (iv msg : ByteArray) : ByteArray :=
  let y := decryptRounds s h (roundKeys s h key iv) (split h.tagSize msg)
  y.1 ++ y.2

theorem encrypt_size (s : StreamCipher) (h : MAC) (key : Array UInt8) (iv msg : ByteArray) :
    (encrypt s h key iv msg).size = msg.size := by
  simp only [encrypt, encryptRounds, ByteArray.size_append, hashRound_size_fst,
    hashRound_size_snd, streamRound_size_fst, streamRound_size_snd]
  rw [← ByteArray.size_append, join_split]

theorem decrypt_size (s : StreamCipher) (h : MAC) (key : Array UInt8) (iv msg : ByteArray) :
    (decrypt s h key iv msg).size = msg.size := by
  simp only [decrypt, decryptRounds, ByteArray.size_append, hashRound_size_fst,
    hashRound_size_snd, streamRound_size_fst, streamRound_size_snd]
  rw [← ByteArray.size_append, join_split]

/-- Decryption inverts encryption, for any stream cipher, keyed hash, key, IV and block. -/
theorem decrypt_encrypt (s : StreamCipher) (h : MAC) (key : Array UInt8) (iv msg : ByteArray) :
    decrypt s h key iv (encrypt s h key iv msg) = msg := by
  have hsplit : split h.tagSize (encrypt s h key iv msg)
      = encryptRounds s h (roundKeys s h key iv) (split h.tagSize msg) := by
    apply split_join
    simp only [encryptRounds, hashRound_size_fst, hashRound_size_snd, streamRound_size_fst,
      streamRound_size_snd]
    simp only [split, ByteArray.size_extract]
    omega
  simp only [decrypt, hsplit, encryptRounds, decryptRounds, hashRound_hashRound,
    streamRound_streamRound]
  exact join_split _ _

/-- Lioness over a stream cipher and a keyed hash. `L` is as long as the hash output, which should
equal the stream cipher's key size. -/
def lioness (s : StreamCipher) (h : MAC) : WideBlockCipher where
  keySize := 2 * s.keySize + 2 * h.keySize
  ivSize  := 4 * s.ivSize
  encrypt := encrypt s h
  decrypt := decrypt s h
  encrypt_size := encrypt_size s h
  decrypt_size := decrypt_size s h
  roundTrip := fun key iv msg _ => decrypt_encrypt s h key iv msg

/-! ## ChaCha20 and BLAKE2b, as in rust-lioness -/

/-- Generic over the per-block function `f`. -/
private theorem fold64_size (f : Nat → Array UInt8) (hf : ∀ i, (f i).size = 64) (n : Nat) :
    ((List.range n).foldl (fun (out : ByteArray) i => out ++ ⟨f i⟩) ByteArray.empty).size
      = 64 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ByteArray.size_append, ih]
    show _ + (f n).size = _
    rw [hf]
    omega

/-- IETF ChaCha20 block `i`: 32-byte key, 12-byte nonce, 32-bit block counter. The first nonce
word sits in the high half of `ChaCha20.block`'s 64-bit counter. -/
private def chachaBlock (key nonce : ByteArray) (i : Nat) : Array UInt8 :=
  let n := nonce.data
  Cipher.ChaCha20.block key.data (n.extract 4 12) (UInt32.ofNat i)
    (n[0]!.toUInt32 ||| (n[1]!.toUInt32 <<< 8) ||| (n[2]!.toUInt32 <<< 16) |||
      (n[3]!.toUInt32 <<< 24))

private theorem chachaBlock_size (key nonce : ByteArray) (i : Nat) :
    (chachaBlock key nonce i).size = 64 := rfl

/-- IETF ChaCha20 keystream from block counter 0. -/
def chacha20 : StreamCipher where
  keySize := 32
  ivSize  := 12
  keystream := fun key nonce len =>
    ((List.range ((len + 63) / 64)).foldl (fun out i => out ++ ⟨chachaBlock key nonce i⟩)
      ByteArray.empty).extract 0 len
  keystream_size := fun key nonce len => by
    rw [ByteArray.size_extract, fold64_size _ (chachaBlock_size key nonce)]
    omega

/-- Keyed BLAKE2b-256. -/
def blake2b256 : MAC where
  keySize := 32
  tagSize := 32
  mac := Hash.Blake2b.hash256Keyed

/-- Lioness over ChaCha20 and keyed BLAKE2b-256: 128-byte key, 48-byte IV. -/
def chacha20Blake2b : WideBlockCipher := lioness chacha20 blake2b256

end Cryptlib.Primitives.WideBlockCipher.Lioness
