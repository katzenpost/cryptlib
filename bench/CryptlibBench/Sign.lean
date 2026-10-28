/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Primitives.Sign.MLDSA.MLDSA
import LeanBench

/-! # ML-DSA-65 benchmarks: signing, with and without the key expanded beforehand -/

namespace CryptlibBench.Sign

open Cryptlib.Primitives.Sign.FIPS204

private def cfg : LeanBench.BenchConfig := { suite := some "sign", samples := 20, warmup := 2 }

def benches : IO (Array LeanBench.Bench) := do
  let p := MLDSA.mldsa65
  let bs ← IO.getRandomBytes 32
  let seed ← IO.mkRef (Vector.ofFn fun i : Fin 32 => bs[i.val]!)
  let msg ← IO.mkRef (ByteArray.mk (Array.ofFn fun (i : Fin 1024) => (i.val * 7 % 251).toUInt8))
  let pk ← IO.mkRef (mldsa65Signature.pub (← seed.get))
  let sig ← IO.mkRef (Vector.replicate p.signatureBytes (0 : UInt8))
  let expanded ← IO.mkRef (expand p (← seed.get))
  let counter ← IO.mkRef (0 : Nat)
  let out ← IO.mkRef ByteArray.empty
  let ok ← IO.mkRef false
  match mldsa65Signature.sign (← seed.get) (← msg.get) (0, ← seed.get) with
  | .ok s _ => sig.set s
  | .error _ _ => throw (IO.userError "sign failed")
  pure #[
    { name := "mldsa65 keys", config := cfg
      action := do out.set (pkBytes p (keys p (← seed.get)).1) },
    { name := "mldsa65 expandA", config := cfg
      action := do
        let a := (prims p).expandA (keys p (← seed.get)).1.rho
        ok.set (a == a) },
    { name := "mldsa65 sign", config := cfg
      action := do
        let n ← counter.modifyGet fun n => (n, n + 1)
        match mldsa65Signature.sign (← seed.get) (← msg.get) (n, ← seed.get) with
        | .ok s _ => sig.set s
        | .error _ _ => pure () },
    { name := "mldsa65 sign, expanded", config := cfg
      action := do
        let n ← counter.modifyGet fun n => (n, n + 1)
        match signExpanded p (← expanded.get) (← msg.get) (n, ← seed.get) with
        | .ok s _ => sig.set s
        | .error _ _ => pure () },
    { name := "mldsa65 verify", config := cfg
      action := do ok.set (mldsa65Signature.verify (← pk.get) (← msg.get) (← sig.get)) }]

end CryptlibBench.Sign
