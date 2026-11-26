/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxKeyed
import Cryptlib.Protocols.RSOROnce

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # The payload key of a relay that answers one header

Once the honest relay answers the challenge ciphertext under one header only, it uses its
payload key for one thing: to decrypt the payload that comes with that header. -/

section Payload

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- **A relay that answers one header decrypts one payload.** Under the header `Hv` it answers
from the decryption of the onion's payload under its payload key; under any other header it
does not use that key. -/
theorem relayAns_header (hvalid : geom.ValidForKEM kem) (sk : kem.PrivateKey)
    (c : kem.Ciphertext) (u : KeyTuple) (Hv : Vector UInt8 geom.headerLength)
    (hcar : ∀ pkt, pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
      → carries kem c pkt = true)
    (o : RSOR.Onion geom) :
    relayAns kem cipher macS kdfS streamS geom sk c
        (fun pkt => if pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
          then procKeys kem cipher macS streamS geom u pkt else none) (RSOR.join o)
      = if o.1 = Hv then
          procKeysD kem macS streamS geom
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              (cipher.decrypt u.1.toArray (ofVector u.2.1) (ofVector o.2)))) u (RSOR.join o)
        else relayAns kem cipher macS kdfS streamS geom sk c (fun _ => none) (RSOR.join o) := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have hoff : payloadOffset kem geom = geom.headerLength := by
    unfold payloadOffset
    rw [hhdr]
    rfl
  have e1 : (RSOR.join o).extract 0 (payloadOffset kem geom) = ofVector o.1 := by
    unfold RSOR.join
    rw [hoff]
    simpa using Cryptlib.Util.Bytes.extract_append_left (ofVector o.1) (ofVector o.2)
  have e2 : (RSOR.join o).extract (payloadOffset kem geom) (RSOR.join o).size = ofVector o.2 := by
    unfold RSOR.join
    rw [hoff]
    simpa using Cryptlib.Util.Bytes.extract_append_right (ofVector o.1) (ofVector o.2)
  by_cases ho : o.1 = Hv
  · have hc := hcar _ (e1.trans (by rw [ho]))
    unfold relayAns
    simp only [hc, ho, e1, ↓reduceIte]
    rw [procKeys_eq_procKeysD, e2, Cryptlib.Util.Bytes.ofVector_toVecN _
      (by rw [cipher.decrypt_size, Cryptlib.Util.Bytes.size_ofVector])]
  · have hne : (RSOR.join o).extract 0 (payloadOffset kem geom) ≠ ofVector Hv := fun h =>
      ho (by simpa using congrArg (Util.Bytes.toVecN geom.headerLength) (e1.symm.trans h))
    unfold relayAns
    simp only [hne, ho, ↓reduceIte]

open Cryptlib.Protocols.RSOR (Role)

variable (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

/-- The honest relays of a game where `.relay` holds the keys `u` for the ciphertext `c` and
answers it under the header `Hv` only, with the payload under that header decrypted by `dec`. -/
def headerRelays (sk : Role → kem.PrivateKey) (c : kem.Ciphertext) (u : KeyTuple)
    (Hv : Vector UInt8 geom.headerLength)
    (dec : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (patch : Protocols.RSOR.Patch
      (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) :
    QueryImpl
      (Protocols.RSOR.oracleSpec (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
      (StateT
        (Protocols.RSOR.Log (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
        ProbComp) :=
  Protocols.RSOR.withDec (S := sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)
    Hv (fun o => o.2)
    (fun o x => RSOR.stepOf geom
      (procKeysD kem macS streamS geom (ofVector x) u (RSOR.join o)))
    (fun msg o x => RSOR.replyOf cipher geom msg
      (procKeysD kem macS streamS geom (ofVector x) u (RSOR.join o)))
    (fun h o => if h = .relay then
        RSOR.stepOf geom
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
      else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o)
    (fun h msg o => if h = .relay then
        RSOR.replyOf cipher geom msg
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
      else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o)
    dec patch

/-- **The relay that answers one header, in the game.** Answering the relay's oracle for a
handler that accepts the header `Hv` only gives `headerRelays` with the cipher's decryption
under the payload key. -/
theorem viaOracle_onlyHeader (sk : Role → kem.PrivateKey) (c : kem.Ciphertext) (u : KeyTuple)
    (Hv : Vector UInt8 geom.headerLength)
    (hcar : ∀ pkt, pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
      → carries kem c pkt = true)
    (patch : Protocols.RSOR.Patch
      (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
    {α : Type}
    (oa : OracleComp
      (Protocols.RSOR.oracleSpec (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) α)
    (log : Protocols.RSOR.Log (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) :
    simulateQ (relayImpl (relayAns kem cipher macS kdfS streamS geom (sk .relay) c
          (fun pkt => if pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
            then procKeys kem cipher macS streamS geom u pkt else none)))
        ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 sk patch)
          oa).run log)
      = (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk c u Hv
          (fun x => Util.Bytes.toVecN _
            (cipher.decrypt u.1.toArray (ofVector u.2.1) (ofVector x)))
          patch) oa).run log := by
  have hstep : ∀ (h : Role) (o : RSOR.Onion geom),
      (if h = .relay then RSOR.stepOf geom (relayAns kem cipher macS kdfS streamS geom (sk .relay) c
          (fun pkt => if pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
            then procKeys kem cipher macS streamS geom u pkt else none) (RSOR.join o))
        else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o)
      = if h = .relay ∧ o.1 = Hv then
          RSOR.stepOf geom (procKeysD kem macS streamS geom
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              (cipher.decrypt u.1.toArray (ofVector u.2.1) (ofVector o.2)))) u (RSOR.join o))
        else if h = .relay then
          RSOR.stepOf geom
            (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
        else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o := by
    intro h o
    by_cases hr : h = .relay
    · subst hr
      rw [relayAns_header kem cipher macS kdfS streamS geom hvalid (sk .relay) c u Hv hcar o]
      by_cases ho : o.1 = Hv <;> simp [ho]
    · simp [hr]
  have hreply : ∀ (h : Role) (msg : RSOR.Msg geom) (o : RSOR.Onion geom),
      (if h = .relay then RSOR.replyOf cipher geom msg
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) c
          (fun pkt => if pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
            then procKeys kem cipher macS streamS geom u pkt else none) (RSOR.join o))
        else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o)
      = if h = .relay ∧ o.1 = Hv then
          RSOR.replyOf cipher geom msg (procKeysD kem macS streamS geom
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              (cipher.decrypt u.1.toArray (ofVector u.2.1) (ofVector o.2)))) u (RSOR.join o))
        else if h = .relay then
          RSOR.replyOf cipher geom msg
            (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
        else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o := by
    intro h msg o
    by_cases hr : h = .relay
    · subst hr
      rw [relayAns_header kem cipher macS kdfS streamS geom hvalid (sk .relay) c u Hv hcar o]
      by_cases ho : o.1 = Hv <;> simp [ho]
    · simp [hr]
  rw [viaOracle_relayImpl]
  unfold headerRelays Protocols.RSOR.withDec
  congr 3
  · funext h o
    exact congrArg pure (hstep h o)
  · funext h msg o
    exact congrArg pure (hreply h msg o)

end Payload

end Cryptlib.Protocols.Sphinx.KEMSphinx
