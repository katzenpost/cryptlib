/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Lean.Data.Json
import Cryptlib.Primitives.WideBlockCipher.Lioness
import Cryptlib.Util.HexBytes

/-!
# Lioness known-answer tests

Checks `Lioness.chacha20Blake2b` against the rust-lioness vectors in
`lioness_chacha20_blake2b.json`.
-/

open Lean
open Cryptlib.Util.HexBytes
open Cryptlib.Primitives.WideBlockCipher.Lioness

def field (j : Json) (k : String) : Except String ByteArray := do
  let s ← (← j.getObjVal? k).getStr?
  match hexStringToByteArray s with
  | some b => pure b
  | none   => throw s!"field {k}: not valid hex: {s}"

def main : IO UInt32 := do
  let path := "testdata/lioness_chacha20_blake2b.json"
  let raw ← IO.FS.readFile path
  match Json.parse raw with
  | .error e => do IO.eprintln s!"failed to parse {path}: {e}"; pure 1
  | .ok j =>
    match j.getObjVal? "primitive" >>= Json.getStr? with
    | .error e => do IO.eprintln e; pure 1
    | .ok prim =>
      if prim ≠ "lioness_chacha20_blake2b" then do
        IO.eprintln s!"unexpected primitive: {prim}"; pure 1
      else match j.getObjVal? "vectors" >>= Json.getArr? with
        | .error e => do IO.eprintln e; pure 1
        | .ok arr => do
          IO.println s!"Lioness ChaCha20+BLAKE2b ({arr.size} vectors)"
          let mut ok := true
          for v in arr do
            match (do
              let name ← (← v.getObjVal? "name").getStr?
              let key ← field v "key_hex"
              let iv ← field v "iv_hex"
              let pt ← field v "plaintext_hex"
              let ct ← field v "ciphertext_hex"
              pure (name, key, iv, pt, ct) : Except String _) with
            | .error e => do IO.eprintln e; ok := false
            | .ok (name, key, iv, pt, wantCt) =>
              let gotCt := chacha20Blake2b.encrypt key.data iv pt
              let gotPt := chacha20Blake2b.decrypt key.data iv wantCt
              let encOk := byteArrayToHex gotCt == byteArrayToHex wantCt
              let decOk := byteArrayToHex gotPt == byteArrayToHex pt
              if encOk && decOk then
                IO.println s!"  ok    {name} ({pt.size}B)"
              else
                ok := false
                IO.println s!"  FAIL  {name} ({pt.size}B)"
                if !encOk then
                  IO.println s!"          encrypt want {byteArrayToHex wantCt}"
                  IO.println s!"          encrypt got  {byteArrayToHex gotCt}"
                if !decOk then
                  IO.println s!"          decrypt want {byteArrayToHex pt}"
                  IO.println s!"          decrypt got  {byteArrayToHex gotPt}"
          IO.println ""
          if ok then
            IO.println s!"all {arr.size} Lioness vectors passed (both encrypt and decrypt)"
            pure 0
          else
            IO.eprintln "Lioness vectors FAILED"
            pure 1
