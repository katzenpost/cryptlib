/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import CryptlibBench.NIKE
import CryptlibBench.KEM
import CryptlibBench.Sphinx
import CryptlibBench.MLKEMSteps
import CryptlibBench.Field25519
import CryptlibBench.Cipher
import CryptlibBench.KDF

/-! # Benchmark driver for all registered schemes and suites -/

def main (args : List String) : IO UInt32 := do
  for e in Cryptlib.Primitives.NIKE.registry do
    (← CryptlibBench.NIKE.benches e.hpqcName e.scheme).forM LeanBench.register
  for e in Cryptlib.Primitives.KEM.registry do
    (← CryptlibBench.KEM.benches e.name e.scheme).forM LeanBench.register
  (← CryptlibBench.Sphinx.benches).forM LeanBench.register
  (← CryptlibBench.MLKEMSteps.benches).forM LeanBench.register
  (← CryptlibBench.Field25519.benches).forM LeanBench.register
  (← CryptlibBench.Cipher.benches).forM LeanBench.register
  (← CryptlibBench.KDF.benches).forM LeanBench.register
  LeanBench.runMain args
