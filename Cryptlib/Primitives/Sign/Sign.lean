/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Std.Tactic.Do
import Cryptlib.Util.Triple

open Std.Do
open Cryptlib.Util.Triple

namespace Cryptlib.Primitives.Sign.Sign

/-! # Digital signature schemes

Signing randomness lives in the `State` of `EStateM`. Signing may fail with `aborted`: a lattice
signer rejects candidate signatures until one passes its norm checks, and a total function can try
only so many. The law `verify_sign` is partial correctness: whatever signature `sign` returns
verifies, from every private key and every signing state. A perfectly correct scheme, such as
Ed25519, proves on its own that it never aborts. Key generation is a pure function of a seed.
Signatures are fixed-size, which excludes stateful schemes such as XMSS.
-/

inductive SignError where
  /-- The signer gave up without finding a signature. -/
  | aborted
deriving DecidableEq

structure Signature where
  State      : Type
  PublicKey  : Type
  PrivateKey : Type
  Sig        : Type

  seedSize       : Nat
  publicKeySize  : Nat
  privateKeySize : Nat
  sigSize        : Nat

  encodePublicKey  : PublicKey  → Vector UInt8 publicKeySize
  decodePublicKey  : Vector UInt8 publicKeySize  → Option PublicKey
  encodePrivateKey : PrivateKey → Vector UInt8 privateKeySize
  decodePrivateKey : Vector UInt8 privateKeySize → Option PrivateKey
  encodeSig        : Sig        → Vector UInt8 sigSize
  decodeSig        : Vector UInt8 sigSize        → Option Sig

  /-- Key generation from a caller-supplied seed. -/
  privateKeyFromSeed : Vector UInt8 seedSize → PrivateKey

  pub : PrivateKey → PublicKey

  /-- Stateful only to carry signing randomness. -/
  sign : PrivateKey → ByteArray → EStateM SignError State Sig

  verify : PublicKey → ByteArray → Sig → Bool

  decode_encode_pub  : ∀ pk, decodePublicKey  (encodePublicKey  pk) = some pk
  decode_encode_priv : ∀ sk, decodePrivateKey (encodePrivateKey sk) = some sk
  decode_encode_sig  : ∀ s,  decodeSig        (encodeSig        s)  = some s

  /-- Correctness: a signature `sign` returns verifies, for every private key and signing state. -/
  verify_sign : ∀ sk m s σ s', sign sk m s = .ok σ s' → verify (pub sk) m σ = true

/-- The trivial scheme: one key, one signature, everything verifies. Insecure. -/
instance : Inhabited Signature := ⟨{
  State      := Unit
  PublicKey  := Unit
  PrivateKey := Unit
  Sig        := Unit

  seedSize       := 0
  publicKeySize  := 0
  privateKeySize := 0
  sigSize        := 0

  encodePublicKey  := fun _ => #v[]
  decodePublicKey  := fun _ => some ()
  encodePrivateKey := fun _ => #v[]
  decodePrivateKey := fun _ => some ()
  encodeSig        := fun _ => #v[]
  decodeSig        := fun _ => some ()

  privateKeyFromSeed := fun _ => ()
  pub                := id
  sign               := fun _ _ => pure ()
  verify             := fun _ _ _ => true

  decode_encode_pub  := fun _ => rfl
  decode_encode_priv := fun _ => rfl
  decode_encode_sig  := fun _ => rfl
  verify_sign        := fun _ _ _ _ _ _ => rfl
}⟩

/-- What a signer that cannot fail returned. -/
theorem ok_pure {ε σ α} {a b : α} {s t : σ} (h : (pure a : EStateM ε σ α) s = .ok b t) :
    a = b ∧ s = t := by
  simpa [pure, EStateM.pure] using h

/-- Whatever `sign` returns verifies under the signer's public key. -/
@[spec] theorem sign_ok (S : Signature) (sk : S.PrivateKey) (m : ByteArray) :
    ⦃⌜True⌝⦄ S.sign sk m ⦃post⟨fun σ => ⌜S.verify (S.pub sk) m σ = true⌝, fun _ => ⌜True⌝⟩⦄ :=
  EStateM_triple_ok fun t σ t' h => S.verify_sign sk m t σ t' h

end Cryptlib.Primitives.Sign.Sign
