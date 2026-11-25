/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.OracleComp.Constructions.SampleableType
import Cryptlib.Primitives.WideBlockCipher.WideBlockCipher
import Cryptlib.Util.Bytes

/-! # A wide-block cipher under a key used for one block

The game for a wide-block cipher under a uniform key that encrypts one block and decrypts one.
The adversary chooses a block and is given its encryption; it then names a block and is given
its decryption. In the ideal world the encryption is uniform, and the decryption is the chosen
block if the adversary named the encryption, and uniform otherwise.

This is what a strong pseudorandom permutation gives for one query each way. A Sphinx relay uses
a hop's payload key exactly so: the sender encrypts one payload under it, and the relay, which
processes a header once, decrypts one. -/

namespace Cryptlib.Primitives.WideBlockCipher

open OracleComp
open Cryptlib.Util.Bytes (ofVector toVecN)

/-- An adversary against a wide-block cipher on blocks of `L` bytes, with one encryption and one
decryption. It is given the IV. -/
structure OneQueryAdversary (L : Nat) where
  St₁ : Type
  St₂ : Type
  /-- The block to encrypt. -/
  choose : Vector UInt8 16 → ProbComp (Vector UInt8 L × St₁)
  /-- The block to decrypt, given the encryption. -/
  ask : St₁ → Vector UInt8 L → ProbComp (Vector UInt8 L × St₂)
  guess : St₂ → Vector UInt8 L → ProbComp Bool

/-- The experiment for `OneQueryAdversary`, with the cipher for `b = true`. -/
def oneQueryExp (cipher : WideBlockCipher) (L : Nat) (B : OneQueryAdversary L) (b : Bool) :
    ProbComp Bool := do
  let k ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let ms ← B.choose iv
  let u ← $ᵗ (Vector UInt8 L)
  let v ← $ᵗ (Vector UInt8 L)
  let c := if b then toVecN L (cipher.encrypt k.toArray (ofVector iv) (ofVector ms.1)) else u
  let cs ← B.ask ms.2 c
  B.guess cs.2 (if b then toVecN L (cipher.decrypt k.toArray (ofVector iv) (ofVector cs.1))
    else if cs.1 = c then ms.1 else v)

end Cryptlib.Primitives.WideBlockCipher
