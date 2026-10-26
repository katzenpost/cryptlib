/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Lean.Data.Json
import Cryptlib.Primitives.Cipher.AESGCMSIV
import Cryptlib.Primitives.Cipher.GHash
import Cryptlib.Util.HexBytes

/-!
# AES-256-GCM-SIV known-answer tests

Checks against `testdata/aes_gcm_siv.json` (including RFC 8452 Appendix C.2), plus tampered
ciphertexts that must be rejected. The underlying primitives get their own vectors.
-/

open Lean
open Cryptlib.Util.HexBytes
open Cryptlib.Primitives.Cipher

structure SIVVector where
  name       : String
  key        : Vector UInt8 32
  nonce      : Vector UInt8 12
  aad        : ByteArray
  plaintext  : ByteArray
  ciphertext : ByteArray

def field (j : Json) (k : String) : Except String ByteArray := do
  let s ← (← j.getObjVal? k).getStr?
  match hexStringToByteArray s with
  | some b => pure b
  | none   => throw s!"field {k}: not valid hex: {s}"

def fixed (n : Nat) (k : String) (b : ByteArray) : Except String (Vector UInt8 n) :=
  if h : b.data.size = n then pure ⟨b.data, h⟩
  else throw s!"field {k}: expected {n} bytes, got {b.size}"

def parseVec (j : Json) : Except String SIVVector := do
  pure {
    name       := ← (← j.getObjVal? "name").getStr?
    key        := ← fixed 32 "key_hex" (← field j "key_hex")
    nonce      := ← fixed 12 "nonce_hex" (← field j "nonce_hex")
    aad        := ← field j "aad_hex"
    plaintext  := ← field j "plaintext_hex"
    ciphertext := ← field j "ciphertext_hex"
  }

def parseFile (s : String) : Except String (Array SIVVector) := do
  let j ← Json.parse s
  let prim ← (← j.getObjVal? "primitive").getStr?
  if prim ≠ "aes_gcm_siv" then
    throw s!"unexpected primitive: {prim}"
  (← (← j.getObjVal? "vectors").getArr?).mapM parseVec

def hexOf {n : Nat} (v : Vector UInt8 n) : String := byteArrayToHex ⟨v.toArray⟩

/-- FIPS-197 C.3: AES-256 on one block, key `00 01 … 1f`, input `00 11 … ff`. -/
def aesBlockOk : Bool :=
  let key   : Vector UInt8 32 := Vector.ofFn fun i : Fin 32 => UInt8.ofNat i.val
  let input : Vector UInt8 16 := Vector.ofFn fun i : Fin 16 => UInt8.ofNat (17 * i.val)
  hexOf (AES.encryptBlockWithKey key input) == "8ea2b7ca516745bfeafc49904b496089"

/-- FIPS-197 C.1: AES-128 on one block, key `00 01 … 0f`, input `00 11 … ff`. -/
def aes128BlockOk : Bool :=
  let key   : Vector UInt8 16 := Vector.ofFn fun i : Fin 16 => UInt8.ofNat i.val
  let input : Vector UInt8 16 := Vector.ofFn fun i : Fin 16 => UInt8.ofNat (17 * i.val)
  hexOf (AES.encryptBlockWithKey128 key input) == "69c4e0d86a7b0430d8cdb78070b4c55a"

/-- A byte stream from a 64-bit LCG, for comparing implementations on arbitrary inputs. -/
def lcgBytes (seed : UInt64) (n : Nat) : ByteArray := Id.run do
  let mut x := seed
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    x := x * 6364136223846793005 + 1442695040888963407
    out := out.push (x >>> 56).toUInt8
  return out

def vec16 (b : ByteArray) : Vector UInt8 16 := Vector.ofFn fun i : Fin 16 => b.data.getD i.val 0

/-- The circuit-S-box cipher against the table specification on `n` random keys and blocks. -/
def aesAgreesWithSpec (n : Nat) : Bool := (List.range n).all fun i =>
  let r := lcgBytes (UInt64.ofNat i) 64
  let k128 := vec16 r
  let k256 : Vector UInt8 32 := Vector.ofFn fun j : Fin 32 => r.data.getD (16 + j.val) 0
  let x := vec16 (r.extract 48 64)
  AES.encryptBlock (AES.expandKey128 k128) x == AES.encryptBlockSpec (AES.expandKey128Spec k128) x &&
    AES.encryptBlock (AES.expandKey k256) x == AES.encryptBlockSpec (AES.expandKeySpec k256) x

/-- Two-word GHASH against the `Nat` specification on `n` random keys and lengths. -/
def ghashAgreesWithSpec (n : Nat) : Bool := (List.range n).all fun i =>
  let h := vec16 (lcgBytes (UInt64.ofNat (1000 + i)) 16)
  let msg := lcgBytes (UInt64.ofNat (2000 + i)) (i * 7 % 100)
  GHash.ghash h msg == GHash.ghashSpec h msg

/-- Two-word POLYVAL against the `Nat` specification on `n` random keys and lengths. -/
def polyvalAgreesWithSpec (n : Nat) : Bool := (List.range n).all fun i =>
  let h := vec16 (lcgBytes (UInt64.ofNat (3000 + i)) 16)
  let msg := lcgBytes (UInt64.ofNat (4000 + i)) (i * 7 % 100)
  Polyval.polyval h msg == Polyval.polyvalSpec h msg

/-- Decode an inline hex literal. -/
def hex (s : String) : Except String ByteArray :=
  match hexStringToByteArray s with
  | some b => pure b
  | none   => throw s!"not valid hex: {s}"

def unwrap {α : Type} : Except String α → IO α
  | .ok v    => pure v
  | .error e => throw (IO.userError e)

/-- Flip one bit of the first byte. -/
def tamper (b : ByteArray) : ByteArray := ⟨b.data.set! 0 (b.data.getD 0 0 ^^^ 1)⟩

def main : IO UInt32 := do
  let mut ok := true

  IO.println "AES-256 block (FIPS-197 C.3)"
  if aesBlockOk then
    IO.println "  ok    single block"
  else
    ok := false
    IO.println "  FAIL  single block"

  IO.println ""
  IO.println "AES-128 block (FIPS-197 C.1)"
  if aes128BlockOk then
    IO.println "  ok    single block"
  else
    ok := false
    IO.println "  FAIL  single block"

  IO.println ""
  IO.println "Constant-time implementations against their specifications"
  if aesAgreesWithSpec 200 then
    IO.println "  ok    AES-128 and AES-256, 200 random keys and blocks"
  else
    ok := false
    IO.println "  FAIL  AES against the table specification"
  if ghashAgreesWithSpec 200 then
    IO.println "  ok    GHASH, 200 random keys and lengths"
  else
    ok := false
    IO.println "  FAIL  GHASH against the Nat specification"
  if polyvalAgreesWithSpec 200 then
    IO.println "  ok    POLYVAL, 200 random keys and lengths"
  else
    ok := false
    IO.println "  FAIL  POLYVAL against the Nat specification"

  IO.println ""
  IO.println "POLYVAL (RFC 8452 §3 worked example)"
  let h ← unwrap (do fixed 16 "H" (← hex "25629347589242761d31f826ba4b757b"))
  let xs ← unwrap (hex ("4f4f95668c83dfb6401762bb2d01a262d1a24ddd2721d006bbe45f20d3c9f362"))
  let got := hexOf (Polyval.polyval h xs)
  if got == "f7a3b47b846119fae5b7866cf5e5b77e" then
    IO.println "  ok    two blocks"
  else
    ok := false
    IO.println s!"  FAIL  two blocks: got {got}"

  let path := "testdata/aes_gcm_siv.json"
  let raw ← IO.FS.readFile path
  let vs ← unwrap (parseFile raw)
  IO.println ""
  IO.println s!"AES-256-GCM-SIV ({vs.size} vectors from hpqc)"
  for v in vs do
    let sealed := AESGCMSIV.encrypt v.key v.nonce v.aad v.plaintext
    let want := byteArrayToHex v.ciphertext
    let blocks := (v.plaintext.size + 15) / 16
    if byteArrayToHex sealed == want then
      IO.println s!"  ok    seal    {v.plaintext.size}B plaintext, {v.aad.size}B AD, \
{blocks} counter block(s)  {v.name}"
    else
      ok := false
      IO.println s!"  FAIL  seal    {v.name}"
      IO.println s!"          want {want}"
      IO.println s!"          got  {byteArrayToHex sealed}"
    match AESGCMSIV.decrypt v.key v.nonce v.aad v.ciphertext with
    | some pt =>
      if pt == v.plaintext then
        IO.println s!"  ok    open    {v.name}"
      else
        ok := false
        IO.println s!"  FAIL  open    {v.name}: recovered the wrong plaintext"
    | none =>
      ok := false
      IO.println s!"  FAIL  open    {v.name}: rejected a valid ciphertext"
    -- Rejection.
    if (AESGCMSIV.decrypt v.key v.nonce v.aad (tamper v.ciphertext)).isNone then
      IO.println s!"  ok    reject  flipped ciphertext bit  {v.name}"
    else
      ok := false
      IO.println s!"  FAIL  reject  accepted a tampered ciphertext  {v.name}"
    if (AESGCMSIV.decrypt v.key v.nonce (v.aad ++ "x".toUTF8) v.ciphertext).isNone then
      IO.println s!"  ok    reject  altered associated data  {v.name}"
    else
      ok := false
      IO.println s!"  FAIL  reject  accepted altered associated data  {v.name}"

  IO.println ""
  if ok then
    IO.println "all AES-256-GCM-SIV vectors passed"
    pure 0
  else
    IO.eprintln "AES-256-GCM-SIV known-answer tests FAILED"
    pure 1
