/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.RSOROnce

/-! # The payload key of a relay that answers one header, whatever the scheme

A game in which an honest relay answers under one header only uses that relay's payload key
twice: the sender encrypts one block, and the relay, which processes a header once, decrypts
one. So the game is the one-query game of the payload cipher. Here that is stated for any
scheme of the RSOR games; the scheme enters through what the relay does with the decrypted
block. -/

namespace Cryptlib.Protocols.RSOR

open OracleComp OracleSpec
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Util.Bytes (ofVector)

/-- A game in which the honest relay `role` decrypts under one header only, cut where its
payload key is used: everything drawn besides that key, given the IV; the block the sender
encrypts under it; what the relay does with a decrypted block; and how the game goes on from
the encrypted block. -/
structure PayloadGame (S : Scheme) (L : ℕ) where
  role : Role := .relay
  X : Type
  draw : Vector UInt8 16 → ProbComp X
  header : X → S.Header
  /-- The block of an onion that the relay decrypts. -/
  key : S.Onion → Vector UInt8 L
  step : X → S.Onion → Vector UInt8 L → Option S.Step
  rep : X → S.Msg → S.Onion → Vector UInt8 L → Option (S.Name × S.Onion)
  /-- The honest relays' answers without that decryption. -/
  proc : X → Role → S.Onion → Option S.Step
  reply : X → Role → S.Msg → S.Onion → Option (S.Name × S.Onion)
  plain : X → Vector UInt8 L
  log : X → Log S
  patch : X → Vector UInt8 L → Patch S
  rest : X → Vector UInt8 L → OracleComp (oracleSpec S) Bool

namespace PayloadGame

variable {S : Scheme} {L : ℕ} (cipher : WideBlockCipher) (G : PayloadGame S L)

/-- The game, with the cipher for `b = true`. For `b = false` the encrypted block is uniform,
and the relay decrypts it to the sender's block and any other block to one uniform block. -/
def exp (b : Bool) : ProbComp Bool := do
  let kp ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let x ← G.draw iv
  let u ← $ᵗ (Vector UInt8 L)
  let v ← $ᵗ (Vector UInt8 L)
  let e := if b then
    Util.Bytes.toVecN _ (cipher.encrypt kp.toArray (ofVector iv) (ofVector (G.plain x))) else u
  (simulateQ (withDec G.role (G.header x) G.key (G.step x) (G.rep x) (G.proc x) (G.reply x)
      (fun y => if b then
          Util.Bytes.toVecN _ (cipher.decrypt kp.toArray (ofVector iv) (ofVector y))
        else if y = e then G.plain x else v)
      (G.patch x e)) (G.rest x e)).run' (G.log x)

/-- The adversary against the cipher that plays the game: it asks for the sender's block to be
encrypted, and the relay asks the decryption oracle. -/
def adv : Primitives.WideBlockCipher.OneQueryAdversary L where
  St := G.X
  choose iv := (fun x => (G.plain x, x)) <$> G.draw iv
  guess st e :=
    (simulateQ (viaDec G.role (G.header st) G.key (G.step st) (G.rep st) (G.proc st)
      (G.reply st) (G.patch st e)) (G.rest st e)).run' (G.log st)

/-- **The game is the cipher game played by `adv`**, when its logs are well-formed. -/
theorem exp_eq (hwf : ∀ iv, ∀ x ∈ support (G.draw iv), (G.log x).WF) (b : Bool) :
    G.exp cipher b = Primitives.WideBlockCipher.oneQueryExp cipher _ G.adv b := by
  unfold exp Primitives.WideBlockCipher.oneQueryExp adv
  simp only [bind_map_left]
  refine bind_congr fun kp => bind_congr fun iv =>
    bind_congr_of_forall_mem_support _ fun x hx => bind_congr fun u => bind_congr fun v => ?_
  exact (viaDec_decOnce _ _ _ _ _ _ _ _ _ _ _ (hwf iv x hx)).symm

end PayloadGame

end Cryptlib.Protocols.RSOR
