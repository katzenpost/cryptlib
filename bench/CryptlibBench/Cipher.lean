/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Primitives.Cipher.ChaChaPoly
import Cryptlib.Primitives.Cipher.Polyval
import Cryptlib.Primitives.Cipher.AESGCMSIV
import Cryptlib.Primitives.Cipher.AESGCM
import LeanBench

/-! # ChaCha20, Poly1305, POLYVAL and AES-GCM-SIV benchmarks at growing message sizes

Inputs are read from refs so the compiler cannot hoist the work out of the timed action. -/

namespace CryptlibBench.Cipher

open Cryptlib.Primitives.Cipher.ChaChaPoly (chacha20 poly1305)
open Cryptlib.Primitives.Cipher.Polyval (polyval)
open Cryptlib.Util.Bytes (ofVector)
open Cryptlib.Primitives.Cipher.AES (encryptBlock expandKey expandKey128)
open Cryptlib.Primitives.Cipher.GHash (ghash)

private def cfg : LeanBench.BenchConfig := { suite := some "cipher", samples := 10, warmup := 1 }

def sizes : List (Nat × String) := [(1024, "1KiB"), (4096, "4KiB"), (16384, "16KiB"), (65536, "64KiB")]

def benches : IO (Array LeanBench.Bench) := do
  let key ← IO.mkRef (Vector.replicate 32 (1 : UInt8))
  let nonce ← IO.mkRef (Vector.replicate 12 (0 : UInt8))
  let h ← IO.mkRef (Vector.replicate 16 (3 : UInt8))
  let out ← IO.mkRef ByteArray.empty
  let mut bs := #[]
  for (size, label) in sizes do
    let msg ← IO.mkRef (ByteArray.mk (Array.ofFn fun (i : Fin size) => (i.val * 7 % 251).toUInt8))
    bs := bs.push { name := s!"chacha20 {label}", config := cfg,
                    action := do out.set (chacha20 (← key.get) (← nonce.get) (← msg.get)) }
    bs := bs.push { name := s!"poly1305 {label}", config := cfg,
                    action := do out.set (ofVector (poly1305 (← key.get) (← msg.get))) }
    bs := bs.push { name := s!"polyval {label}", config := cfg,
                    action := do out.set (ofVector (polyval (← h.get) (← msg.get))) }
    bs := bs.push { name := s!"aes-gcm-siv encrypt {label}", config := cfg,
                    action := do
                      out.set (Cryptlib.Primitives.Cipher.AESGCMSIV.encrypt (← key.get) (← nonce.get)
                        ByteArray.empty (← msg.get)) }
  let blk ← IO.mkRef (Vector.replicate 16 (5 : UInt8))
  let blkOut ← IO.mkRef (Vector.replicate 16 (0 : UInt8))
  let rk128 ← IO.mkRef (expandKey128 (Vector.replicate 16 (1 : UInt8)))
  let rk256 ← IO.mkRef (expandKey (Vector.replicate 32 (1 : UInt8)))
  bs := bs.push { name := "aes-128 block", config := cfg,
                  action := do blkOut.set (encryptBlock (← rk128.get) (← blk.get)) }
  bs := bs.push { name := "aes-256 block", config := cfg,
                  action := do blkOut.set (encryptBlock (← rk256.get) (← blk.get)) }
  let packet ← IO.mkRef (ByteArray.mk (Array.ofFn fun (i : Fin 1200) => (i.val * 7 % 251).toUInt8))
  let ghashIn ← IO.mkRef (ByteArray.mk (Array.ofFn fun (i : Fin 1232) => (i.val * 7 % 251).toUInt8))
  bs := bs.push { name := "ghash 1232B", config := cfg,
                  action := do blkOut.set (ghash (← h.get) (← ghashIn.get)) }
  bs := bs.push { name := "aes-128-gcm encrypt 1200B", config := cfg,
                  action := do
                    out.set (Cryptlib.Primitives.Cipher.AESGCM.encrypt (← rk128.get) (← nonce.get)
                      ByteArray.empty (← packet.get)) }
  pure bs

end CryptlibBench.Cipher
