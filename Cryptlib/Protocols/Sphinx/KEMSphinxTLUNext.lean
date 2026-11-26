/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTLUStream

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp OracleSpec ENNReal
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
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # The original's next layer in world 1 of TLU→

In world 1 the honest relay answers the replacement with the layer the adversary's original
onion has after the relay. That layer depends on the keys of the original's own layer at the
relay, which the adversary is never shown, through one keystream. Here those keys are replaced
as the relay's keys for the replacement were. -/

section ForwardNext

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

variable (names : Role → RSOR.Name)

/-- The layer the original has after the honest relay, from the header keystream `U` of its
layer at the relay; `mine` when the relay is last. -/
def nextU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (mine : RSOR.Onion geom) (U : ByteArray) : RSOR.Onion geom :=
  if ch.c.pos + 1 < ch.c.req.fwd.hops.length then
    match layerPast kem cipher macS kdfS streamS geom
        (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1
        (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos U (ch.c.pos + 1) with
    | .ok pkt => RSOR.split geom pkt
    | .error _ => default
  else mine

/-- **The original's next layer depends on the keys of its layer at the relay through their
keystream only.** With the seed `s` at the relay's position, it is `nextU` at the keystream of
the keys `s` gives. -/
theorem next_setSeed {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (mine : RSOR.Onion geom) (s : Vector UInt8 32)
    (c ss : ByteArray)
    (henc : kemEncap kem ((RSOR.path kem ch.c.req.fwd
      [.recipient ch.c.req.receiver])[(ch.c.pos : ℕ)]!).publicKey s = .ok (c, ss)) :
    ch.c.next (setSeed geom r ch.c.pos s) mine
      = nextU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r mine
        (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss))) := by
  have hsz := RSOR.path_size kem ch.c.req.fwd [.recipient ch.c.req.receiver]
  have hle : ch.c.req.fwd.hops.length ≤ geom.nrHops := ch.c.req.fwd.length_le
  unfold Protocols.RSOR.ForwardChallenge.next nextU
  by_cases hn : (ch.c.pos : ℕ) + 1 < ch.c.req.fwd.hops.length
  · simp only [hn, ↓reduceDIte, ↓reduceIte]
    show RSOR.form kem cipher macS kdfS streamS geom ch.c.req (setSeed geom r ch.c.pos s)
      ⟨_, hn⟩ = _
    unfold RSOR.form
    rw [layerPast_real kem cipher macS kdfS streamS geom _ r.1 _ ch.c.pos (ch.c.pos + 1) s c ss
      (Nat.lt_succ_self _) (lt_of_lt_of_le hn hsz.ge).le (hsz.le.trans hle) henc]
    rfl
  · simp only [hn, ↓reduceDIte, ↓reduceIte]
    rfl

end ForwardNext

end Cryptlib.Protocols.Sphinx.KEMSphinx
