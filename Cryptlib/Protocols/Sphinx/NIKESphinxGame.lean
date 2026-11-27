/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxHeaderFn
import Cryptlib.Protocols.Sphinx.KEMSphinxTailOracle

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.KEMSphinx (ProcResult procSpec KeyTuple)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Util.Bytes (ofVector)

/-! # The key game of NIKE Sphinx

Scherer, Weis and Strufe prove Sphinx's properties from one game on its key derivation,
Sphinx-KEM-IND-CCA: an honest relay's keys for the sender's group element, its blinding factor
among them, are replaced by uniform ones, and the hops after it are derived from the replacement.
They prove that game hard under Gap Diffie-Hellman with the hashes as random oracles. Here the
keys come from a KDF, so the game is stated for the NIKE and the KDF, and its advantage is the
term the properties of NIKE Sphinx carry.

The paper's relay refuses the challenge element. Here it answers that element with the keys the
adversary is handed, which the adversary could do itself. -/

section Game

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- What a relay returns for a packet, its keys had from the packet's group element by
`keysOf`. -/
def procWith (keysOf : ByteArray → Except String HopKeys) (pkt : ByteArray) : ProcResult :=
  match unwrapNIKEWith nike cipher macS streamS geom keysOf pkt with
  | .ok (p, t, c, f) => some (p, t, c, f.map ofVector)
  | .error _ => none

/-- The keys a relay derives for a group element. -/
def relayKeys (sk : nike.PrivateKey) (ge : ByteArray) : Except String HopKeys :=
  deriveHopKeys kdfS <$> nikeDH nike sk ge

/-- A relay's keys, except that for the element `a` they are `t`. -/
def keysExcept (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys) (ge : ByteArray) :
    Except String HopKeys :=
  if ge = a then pure t else relayKeys nike kdfS sk ge

/-- **A relay is `procWith` on the keys it derives.** -/
theorem unwrap_eq_procWith (sk : nike.PrivateKey) (pkt : ByteArray) :
    RSOR.unwrap nike cipher macS kdfS streamS geom sk pkt
      = (procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt).map
        fun r => (r.1, r.2.2.1, r.2.2.2) := by
  unfold RSOR.unwrap procWith
  rw [unwrapNIKE_eq_unwrapNIKEWith]
  have e : (fun ge => do
        let sk' ← nikeDecodePrivateKey nike (ofVector (nike.encodePrivateKey sk))
        let ss ← nikeDH nike sk' ge
        pure (deriveHopKeys kdfS ss)) = relayKeys nike kdfS sk := by
    funext ge
    unfold nikeDecodePrivateKey relayKeys
    rw [Common.toVecN_ofVector, nike.decode_encode_priv]
    rfl
  rw [e]
  cases unwrapNIKEWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt <;> rfl

/-- The relay's oracle, answering the element `a` with the keys `t`. -/
def procImplK (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys) : QueryImpl procSpec ProbComp :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    pure (procWith nike cipher macS streamS geom (keysExcept nike kdfS sk a t) pkt)

/-- The relay's oracle. -/
def procImpl (sk : nike.PrivateKey) : QueryImpl procSpec ProbComp :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    pure (procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt)

/-- Hop keys from uniform draws: four keys, and the seed of the blinding factor. -/
def keysOfDraw (u : KeyTuple × Vector UInt8 32) : HopKeys where
  payloadEncryption := u.1.1
  headerEncryptionIV := u.1.2.1
  headerMAC := u.1.2.2.1
  headerEncryption := u.1.2.2.2
  blindingFactor := blindingFactorPrivKey u.2

/-- An adversary on the key game. With the relay's oracle it chooses a path and the relay's
place on it; then it is given the sender's group element and every hop's keys. -/
structure KeyAdversary where
  St : Type
  pre : RSOR.Key nike → OracleComp procSpec ((Array PathHop × ℕ) × St)
  post : St → ByteArray → List HopKeys → OracleComp procSpec Bool

variable {nike}

/-- **The key game.** The honest relay is put at the place the adversary chose. With `b` the
hops' keys are the sender's; without, the relay's keys are uniform and the hops after it are
derived from them. The relay answers the element it receives with the keys of its place. -/
def keyGame (A : KeyAdversary nike) (b : Bool) : ProbComp Bool := do
  let u ← $ᵗ (KeyTuple × Vector UInt8 32)
  let k ← RSOR.keygen nike
  let cs ← simulateQ (procImpl nike cipher macS kdfS streamS geom k.2) (A.pre k.1)
  let d ← $ᵗ Vector UInt8 nike.privateKeySize
  let c := (nike.decodePrivateKey d).getD default
  let hops := cs.1.1.modify cs.1.2 fun h =>
    { h with publicKey := ofVector (nike.encodePublicKey k.1.1) }
  let keys := hopKeysWith nike kdfS c hops cs.1.2
    (if b then RSOR.hopKey nike kdfS c hops cs.1.2 else keysOfDraw u) hops.size
  simulateQ (procImplK nike cipher macS kdfS streamS geom k.2
      (groupElem nike c keys.toArray cs.1.2) keys.toArray[cs.1.2]!)
    (A.post cs.2 (groupElem nike c keys.toArray 0) keys)

/-- The adversary's advantage in the key game. -/
noncomputable def keyAdvantage (A : KeyAdversary nike) : ℝ :=
  |(Pr{let x ← keyGame cipher macS kdfS streamS geom A true}[x = true]).toReal
    - (Pr{let x ← keyGame cipher macS kdfS streamS geom A false}[x = true]).toReal|

end Game

end Cryptlib.Protocols.Sphinx.NIKESphinx
