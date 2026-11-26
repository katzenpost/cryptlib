/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append.Core
import Cryptlib.Primitives.WideBlockCipher.WideBlockCipher
import Cryptlib.Util.Bytes

/-! # A wide-block cipher under a key used for one block

The game for a wide-block cipher under a uniform key that encrypts one block and decrypts one.
The adversary chooses a block and is given its encryption, and a decryption oracle that answers
for one block: the first it is asked about. In the ideal world the encryption is uniform, and
the decryption is the chosen block if the adversary asks about the encryption, and uniform
otherwise.

This is what a strong pseudorandom permutation gives for one query each way. A Sphinx relay uses
a hop's payload key exactly so: the sender encrypts one payload under it, and the relay, which
processes a header once, decrypts one. -/

namespace Cryptlib.Primitives.WideBlockCipher

open OracleComp
open Cryptlib.Util.Bytes (ofVector toVecN)

/-- The oracles of the game: uniform sampling and decryption. -/
abbrev decSpec (L : Nat) := unifSpec + (Vector UInt8 L →ₒ Vector UInt8 L)

/-- An adversary against a wide-block cipher on blocks of `L` bytes, with one encryption and one
decryption. It is given the IV. -/
structure OneQueryAdversary (L : Nat) where
  St : Type
  /-- The block to encrypt. -/
  choose : Vector UInt8 16 → ProbComp (Vector UInt8 L × St)
  guess : St → Vector UInt8 L → OracleComp (decSpec L) Bool

/-- Decryption for one block: the first block asked about is remembered and answered by `dec`,
and any other block is returned unchanged. -/
def decFirst {L : Nat} (dec : Vector UInt8 L → Vector UInt8 L) :
    QueryImpl (Vector UInt8 L →ₒ Vector UInt8 L) (StateT (Option (Vector UInt8 L)) ProbComp) :=
  fun x => do
    match ← get with
    | none =>
      set (some x)
      return dec x
    | some y => return if x = y then dec x else x

/-- The game's oracles, with decryption for one block. -/
def decOnce {L : Nat} (dec : Vector UInt8 L → Vector UInt8 L) :
    QueryImpl (decSpec L) (StateT (Option (Vector UInt8 L)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Option (Vector UInt8 L)) ProbComp)
    + decFirst dec

/-- The experiment for `OneQueryAdversary`, with the cipher for `b = true`. -/
def oneQueryExp (cipher : WideBlockCipher) (L : Nat) (B : OneQueryAdversary L) (b : Bool) :
    ProbComp Bool := do
  let k ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let ms ← B.choose iv
  let u ← $ᵗ (Vector UInt8 L)
  let v ← $ᵗ (Vector UInt8 L)
  let c := if b then toVecN L (cipher.encrypt k.toArray (ofVector iv) (ofVector ms.1)) else u
  (simulateQ (decOnce fun x =>
      if b then toVecN L (cipher.decrypt k.toArray (ofVector iv) (ofVector x))
      else if x = c then ms.1 else v)
    (B.guess ms.2 c)).run' none

end Cryptlib.Primitives.WideBlockCipher
