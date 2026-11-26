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
          procKeysD kem macS geom u.2.2.1
            (streamS.keystream (ofVector u.2.2.2) (ofVector u.2.1)
              (geom.routingInfoLength + geom.perHopRoutingInfoLength))
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              (cipher.decrypt u.1.toArray (ofVector u.2.1) (ofVector o.2)))) (RSOR.join o)
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

/-- The honest relays of a game where `.relay` answers the ciphertext `c` under the header `Hv`
only, with the MAC key `km` and the header keystream `ks`, and with the payload under that
header decrypted by `dec`. -/
def headerRelays (sk : Role → kem.PrivateKey) (c : kem.Ciphertext) (km : Vector UInt8 32)
    (ks : ByteArray)
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
    .relay Hv (fun o => o.2)
    (fun o x => RSOR.stepOf geom
      (procKeysD kem macS geom km ks (ofVector x) (RSOR.join o)))
    (fun msg o x => RSOR.replyOf cipher geom msg
      (procKeysD kem macS geom km ks (ofVector x) (RSOR.join o)))
    (fun h o => if h = .relay then
        RSOR.stepOf geom
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
      else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o)
    (fun h msg o => if h = .relay then
        RSOR.replyOf cipher geom msg
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
      else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o)
    dec patch

/-- **The relay that answers one header, in the game.** If the relay's answers `f` to the
ciphertext `c` are, on an onion with the header `Hv`, what its MAC key and keystream give from
the decryption `D` of the payload, and nothing under any other header, then answering the
relay's oracle with them gives `headerRelays`. -/
theorem viaOracle_header (sk : Role → kem.PrivateKey) (c : kem.Ciphertext)
    (f : ByteArray → ProcResult) (km : Vector UInt8 32) (U : ByteArray)
    (Hv : Vector UInt8 geom.headerLength)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hf : ∀ o : RSOR.Onion geom,
      relayAns kem cipher macS kdfS streamS geom (sk .relay) c f (RSOR.join o)
        = if o.1 = Hv then procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o)
          else relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none)
            (RSOR.join o))
    (patch : Protocols.RSOR.Patch
      (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
    {α : Type}
    (oa : OracleComp
      (Protocols.RSOR.oracleSpec (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) α)
    (log : Protocols.RSOR.Log (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) :
    simulateQ (relayImpl (relayAns kem cipher macS kdfS streamS geom (sk .relay) c f))
        ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 sk patch)
          oa).run log)
      = (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk c km U Hv D
          patch) oa).run log := by
  have hstep : ∀ (h : Role) (o : RSOR.Onion geom),
      (if h = .relay then
          RSOR.stepOf geom
            (relayAns kem cipher macS kdfS streamS geom (sk .relay) c f (RSOR.join o))
        else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o)
      = if h = .relay ∧ o.1 = Hv then
          RSOR.stepOf geom (procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o))
        else if h = .relay then
          RSOR.stepOf geom
            (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
        else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o := by
    intro h o
    by_cases hr : h = .relay
    · subst hr
      rw [hf o]
      by_cases ho : o.1 = Hv <;> simp [ho]
    · simp [hr]
  have hreply : ∀ (h : Role) (msg : RSOR.Msg geom) (o : RSOR.Onion geom),
      (if h = .relay then RSOR.replyOf cipher geom msg
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) c f (RSOR.join o))
        else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o)
      = if h = .relay ∧ o.1 = Hv then
          RSOR.replyOf cipher geom msg
            (procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o))
        else if h = .relay then
          RSOR.replyOf cipher geom msg
            (relayAns kem cipher macS kdfS streamS geom (sk .relay) c (fun _ => none) (RSOR.join o))
        else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o := by
    intro h msg o
    by_cases hr : h = .relay
    · subst hr
      rw [hf o]
      by_cases ho : o.1 = Hv <;> simp [ho]
    · simp [hr]
  rw [viaOracle_relayImpl]
  unfold headerRelays Protocols.RSOR.withDec
  congr 3
  · funext h o
    exact congrArg pure (hstep h o)
  · funext h msg o
    exact congrArg pure (hreply h msg o)

/-- The relay with the keys `u` that accepts the header `Hv` only is `headerRelays` with the
cipher's decryption under the payload key. -/
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
      = (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk c
          u.2.2.1 (streamS.keystream (ofVector u.2.2.2) (ofVector u.2.1)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)) Hv
          (fun x => Util.Bytes.toVecN _
            (cipher.decrypt u.1.toArray (ofVector u.2.1) (ofVector x)))
          patch) oa).run log :=
  viaOracle_header kem cipher macS kdfS streamS geom hvalid hmactag h16 sk c _ _ _ Hv _
    (relayAns_header kem cipher macS kdfS streamS geom hvalid (sk .relay) c u Hv hcar) patch oa log

/-- The relay's answers under the header `Hv` only, from its MAC key, its header keystream and
a decryption `D` of the payload. -/
def headerHand (km : Vector UInt8 32) (U : ByteArray) (Hv : Vector UInt8 geom.headerLength)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (pkt : ByteArray) : ProcResult :=
  if pkt.extract 0 (payloadOffset kem geom) = ofVector Hv then
    procKeysD kem macS geom km U
      (ofVector (D (Util.Bytes.toVecN _ (pkt.extract (payloadOffset kem geom) pkt.size)))) pkt
  else none

omit hmactag h16 in
include hvalid in
/-- What a relay with the answers `headerHand` does with an onion. -/
theorem relayAns_headerHand (sk : kem.PrivateKey) (c : kem.Ciphertext) (km : Vector UInt8 32)
    (U : ByteArray) (Hv : Vector UInt8 geom.headerLength)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hcar : ∀ pkt, pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
      → carries kem c pkt = true)
    (o : RSOR.Onion geom) :
    relayAns kem cipher macS kdfS streamS geom sk c (headerHand kem macS geom km U Hv D)
        (RSOR.join o)
      = if o.1 = Hv then procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o)
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
    unfold relayAns headerHand
    simp only [hc, ho, e1, ↓reduceIte]
    rw [e2, Cryptlib.Util.Bytes.toVecN_ofVector]
  · have hne : (RSOR.join o).extract 0 (payloadOffset kem geom) ≠ ofVector Hv := fun h =>
      ho (by simpa using congrArg (Util.Bytes.toVecN geom.headerLength) (e1.symm.trans h))
    unfold relayAns headerHand
    simp only [hne, ho, ↓reduceIte]

/-! ## The cipher game for a relay that answers one header -/

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- A payload: the block the payload cipher works on. -/
abbrev Block (geom : Geometry) := Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)

/-- A game in which the honest relay answers its challenge ciphertext under one header only,
cut where its payload key is used: everything drawn besides that key, given the IV; the block
the sender encrypts under it; and how the game goes on from the encrypted block. -/
structure PayloadGame where
  X : Type
  draw : Vector UInt8 16 → ProbComp X
  sk : X → Role → kem.PrivateKey
  c : X → kem.Ciphertext
  /-- The relay's MAC key. -/
  macKey : X → Vector UInt8 32
  /-- The relay's header keystream. -/
  ks : X → ByteArray
  header : X → Vector UInt8 geom.headerLength
  plain : X → Block geom
  log : X → Protocols.RSOR.Log 𝒮
  patch : X → Block geom → Protocols.RSOR.Patch 𝒮
  rest : X → Block geom → OracleComp (Protocols.RSOR.oracleSpec 𝒮) Bool

namespace PayloadGame

variable {kem cipher macS kdfS streamS geom hvalid hmactag h16}
  (G : PayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16)

/-- The game, with the cipher for `b = true`. For `b = false` the encrypted block is uniform,
and the relay decrypts it to the sender's block and any other block to one uniform block. -/
def exp (b : Bool) : ProbComp Bool := do
  let kp ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let x ← G.draw iv
  let u ← $ᵗ (Block geom)
  let v ← $ᵗ (Block geom)
  let e := if b then
    Util.Bytes.toVecN _ (cipher.encrypt kp.toArray (ofVector iv) (ofVector (G.plain x))) else u
  (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 (G.sk x) (G.c x)
      (G.macKey x) (G.ks x) (G.header x)
      (fun y => if b then
          Util.Bytes.toVecN _ (cipher.decrypt kp.toArray (ofVector iv) (ofVector y))
        else if y = e then G.plain x else v)
      (G.patch x e)) (G.rest x e)).run' (G.log x)

/-- The adversary against the cipher that plays the game: it asks for the sender's block to be
encrypted, and the relay asks the decryption oracle. -/
def adv : Primitives.WideBlockCipher.OneQueryAdversary
    (geom.payloadTagLength + geom.forwardPayloadLength) where
  St := G.X
  choose iv := (fun x => (G.plain x, x)) <$> G.draw iv
  guess st e :=
    (simulateQ (Protocols.RSOR.viaDec (S := 𝒮)
        .relay (G.header st) (fun o => o.2)
        (fun o x => RSOR.stepOf geom
          (procKeysD kem macS geom (G.macKey st) (G.ks st) (ofVector x)
            (RSOR.join o)))
        (fun msg o x => RSOR.replyOf cipher geom msg
          (procKeysD kem macS geom (G.macKey st) (G.ks st) (ofVector x)
            (RSOR.join o)))
        (fun h o => if h = .relay then
            RSOR.stepOf geom (relayAns kem cipher macS kdfS streamS geom
              (G.sk st .relay) (G.c st) (fun _ => none) (RSOR.join o))
          else RSOR.proc kem cipher macS kdfS streamS geom (G.sk st h) o)
        (fun h msg o => if h = .relay then
            RSOR.replyOf cipher geom msg (relayAns kem cipher macS kdfS streamS geom
              (G.sk st .relay) (G.c st) (fun _ => none) (RSOR.join o))
          else RSOR.reply kem cipher macS kdfS streamS geom (G.sk st h) msg o)
        (G.patch st e)) (G.rest st e)).run' (G.log st)

/-- **The game is the cipher game played by `adv`**, when its logs are well-formed. -/
theorem exp_eq (hwf : ∀ iv, ∀ x ∈ support (G.draw iv), (G.log x).WF) (b : Bool) :
    G.exp b = Primitives.WideBlockCipher.oneQueryExp cipher _ G.adv b := by
  unfold exp Primitives.WideBlockCipher.oneQueryExp adv
  simp only [bind_map_left]
  refine bind_congr fun kp => bind_congr fun iv =>
    bind_congr_of_forall_mem_support _ fun x hx => bind_congr fun u => bind_congr fun v => ?_
  exact (Protocols.RSOR.viaDec_decOnce _ _ _ _ _ _ _ _ _ _ _ (hwf iv x hx)).symm

end PayloadGame

end Payload

end Cryptlib.Protocols.Sphinx.KEMSphinx
