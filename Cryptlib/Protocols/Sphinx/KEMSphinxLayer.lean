/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTailOracle

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
open Cryptlib.Util.Bytes (ofVector)

/-! # Payload tagging

A mix checks the MAC over the header only. The payload is checked once, at the final hop, by the
zero tag inside the decrypted payload. This file states what follows for a packet whose payload
was changed in flight.

`procWith_payload_congr`: a mix forwards such a packet exactly as it forwards the original. The
replay tag, the commands and the forwarded header are the same. So a mix without a replay cache
links the two packets, which is the attack of Kuhn, Beck and Strufe (Section V) on layer
unlinkability. With a replay cache the second packet is refused, since the replay tag is the
same. -/

section Tagging

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- The length of everything before the payload. -/
abbrev payloadOffset : Nat := 2 + kem.ciphertextSize + geom.routingInfoLength + macLength

theorem extract_of_prefix_eq {a b : ByteArray} {n : Nat} (h : a.extract 0 n = b.extract 0 n)
    (i j : Nat) (hj : j ≤ n) : a.extract i j = b.extract i j := by
  have h' := congrArg (fun x => x.extract i j) h
  simp only [ByteArray.extract_extract] at h'
  rwa [Nat.zero_add, Nat.zero_add, Nat.min_eq_left hj] at h'

/-- A mix forwards a packet with a changed payload as it forwards the original: same replay tag,
same commands, same forwarded header. -/
theorem procWith_payload_congr (dec : ByteArray → Except String ByteArray) (pkt pkt' : ByteArray)
    (hsz : pkt'.size = pkt.size)
    (hhdr : pkt'.extract 0 (payloadOffset kem geom) = pkt.extract 0 (payloadOffset kem geom))
    (tag : Vector UInt8 32) (cmds : List RoutingCommand) (fwd : ByteArray)
    (h : procWith kem cipher macS kdfS streamS geom dec pkt = some (none, tag, cmds, some fwd)) :
    ∃ fwd', procWith kem cipher macS kdfS streamS geom dec pkt' = some (none, tag, cmds, some fwd')
      ∧ fwd'.extract 0 (payloadOffset kem geom) = fwd.extract 0 (payloadOffset kem geom) := by
  have hmacL : macLength = 32 := rfl
  have e0 := extract_of_prefix_eq hhdr 0 2 (by unfold payloadOffset; omega)
  have e1 := extract_of_prefix_eq hhdr 2 (2 + kem.ciphertextSize) (by unfold payloadOffset; omega)
  have e2 := extract_of_prefix_eq hhdr 0 (2 + kem.ciphertextSize + geom.routingInfoLength)
    (by unfold payloadOffset; omega)
  have e3 := extract_of_prefix_eq hhdr (2 + kem.ciphertextSize + geom.routingInfoLength)
    (2 + kem.ciphertextSize + geom.routingInfoLength + macLength) (by unfold payloadOffset; omega)
  have e4 := extract_of_prefix_eq hhdr (2 + kem.ciphertextSize)
    (2 + kem.ciphertextSize + geom.routingInfoLength) (by unfold payloadOffset; omega)
  unfold procWith unwrapKEMWith at h ⊢
  dsimp only at h ⊢
  simp only [e0, e1, e2, e3, e4]
  by_cases h1 : pkt.size < 2 + kem.ciphertextSize + geom.routingInfoLength + macLength
  · rw [dif_pos h1] at h; cases h
  rw [dif_neg h1] at h; rw [dif_neg (hsz ▸ h1)]
  by_cases h2 : (pkt.extract 0 2).data ≠ v0AD.data
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h ⊢
  cases hd : dec (pkt.extract 2 (2 + kem.ciphertextSize)) with
  | error e => rw [hd] at h; cases h
  | ok ss =>
    rw [hd] at h
    dsimp only [Bind.bind, Except.bind] at h ⊢
    by_cases h3 : (ofVector (macS.mac (ofVector (deriveHopKeys kdfS ss).headerMAC)
        (pkt.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength)))).data
        ≠ (pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
          (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)).data
    · rw [if_pos h3] at h; cases h
    rw [if_neg h3] at h ⊢
    generalize parseAll _ = r at h ⊢
    cases r with
    | error e => cases h
    | ok cmds0 =>
      dsimp only at h ⊢
      generalize List.findSome? _ cmds0 = o at h ⊢
      cases o with
      | none =>
        dsimp only at h
        split_ifs at h <;> cases h
      | some nm =>
        dsimp only [pure, Except.pure] at h ⊢
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨_, rfl, ?_⟩
        have hv0 : v0AD.size = 2 := rfl
        show ((_ : ByteArray) ++ _).extract 0 _ = ((_ : ByteArray) ++ _).extract 0 _
        refine (Cryptlib.Util.Bytes.extract_append_of_le _ _ ?_).trans
          (Cryptlib.Util.Bytes.extract_append_of_le _ _ ?_).symm
        all_goals
          have hpad : (⟨Array.replicate geom.perHopRoutingInfoLength (0 : UInt8)⟩ : ByteArray).size
              = geom.perHopRoutingInfoLength := Array.size_replicate
          simp only [ByteArray.size_append, size_xorBytes, Util.Bytes.size_ofVector,
            ByteArray.size_extract, hpad, hv0, payloadOffset, hmacL, Nat.min_self] at h1 ⊢
          omega

end Tagging

end Cryptlib.Protocols.Sphinx.KEMSphinx
