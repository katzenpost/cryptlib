/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.Constants
import Cryptlib.Protocols.Sphinx.Geometry
import Cryptlib.Protocols.Sphinx.Commands
import Cryptlib.Protocols.Sphinx.Types
import Cryptlib.Protocols.Sphinx.Interface
import Cryptlib.Protocols.Sphinx.Common
import Cryptlib.Protocols.Sphinx.NIKESphinxTheorems
import Cryptlib.Protocols.Sphinx.SURB
import Cryptlib.Primitives.WideBlockCipher.WideBlockCipher
import Cryptlib.Primitives.WideBlockCipher.AEZ
import Cryptlib.Primitives.MAC.MAC
import Cryptlib.Primitives.KDF.KDF
import Cryptlib.Primitives.KDF.HKDF
import Cryptlib.Protocols.Sphinx.KDF
import Cryptlib.Primitives.StreamCipher.StreamCipher
import Cryptlib.Primitives.StreamCipher.AES256CTR
import Cryptlib.Primitives.KEM.KEM
import Cryptlib.Primitives.KEM.Schemes
import Cryptlib.Primitives.Hash.Sha512
import Cryptlib.Util.Bytes

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.NIKESphinx (HopKeys deriveHopKeys)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Primitives.Hash.Sha512 (sha512_256)
open Cryptlib.Util.Bytes (ofVector extract_append_le extract_append_of_le extract_append_of_ge
  extract_append_left extract_append_right append_extract)

/-! # KEM-Sphinx scheme type

Constructions and proofs are in `KEMSphinxTheorems.lean` and `KEMSphinxTail.lean`. -/

/-- KEM-Sphinx has no wrap-resistance field: it has no blinding step, so it is not
wrap-resistant. See `unwrapKEM_routingInfoBlock_not_wrap_resistant` in `KEMSphinxTheorems.lean`. -/
structure KEMSphinxScheme extends Cryptlib.Protocols.Sphinx.Interface.Sphinx where
  kem : KEM
  /-- The exact half of tail indistinguishability (Kuhn, Beck and Strufe, S&P 2020): what the
  first hop forwards from a wrapped packet is what `wrap` itself returns on the rest of the
  path, from some state. See `wrapKEM_unwrapKEM_tail` in `KEMSphinxTail.lean`. -/
  unwrap_tail : ∀ (hop0 : PathHop) (rest : List PathHop) (privKey : PrivateKey)
      (payload : Vector UInt8 geometry.forwardPayloadLength) (st : State)
      (pkt : Vector UInt8 geometry.packetLength) (st' : State),
    rest ≠ [] →
    unwrapReliable st →
    derivePublicKey privKey = hop0.publicKey →
    (∀ c ∈ hop0.commands, c ≠ .null ∧ (∀ id m, c ≠ .nextNodeHop id m)) →
    wrap (hop0 :: rest) payload st = .ok pkt st' →
    ∃ (replayTag : Vector UInt8 32) (cmds : List Command)
      (fwd : Vector UInt8 (ofVector pkt).size) (st0 st1 : State)
      (fresh : Vector UInt8 geometry.packetLength),
      unwrap privKey (ofVector pkt) = .ok (none, replayTag, cmds, some fwd) ∧
      wrap rest payload st0 = .ok fresh st1 ∧ ofVector fresh = ofVector fwd

end Cryptlib.Protocols.Sphinx.KEMSphinx
