/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxHeaderFn
import Cryptlib.Protocols.Sphinx.KEMSphinxRSOR

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
open Cryptlib.Util.Bytes (ofVector)

/-! # A packet over a route builds

`newKEMPacket` fails on a wrong size, on a failed encapsulation, or on commands that do not fit
a hop's routing fragment. A route of the scheme has none of these: its keys are derived ones,
to which encapsulation does not fail (`KEM.encap_derived`), and only its last hop has commands.
So the first layer over a route builds, for any draw. -/

section Builds

variable (kem : KEM) (geom : Geometry)

/-- A hop's routing fragment builds when its commands fit its budget. -/
theorem kemRiFragment_builds (path : Array PathHop) (ke : Array ByteArray) (mac : ByteArray)
    (i : ℕ)
    (h : ∃ b, commandsToBytes
        (if (i == path.size - 1) = true then geom.perHopRoutingInfoLength - kem.ciphertextSize
          else geom.perHopRoutingInfoLength - geom.nextNodeHopLength - kem.ciphertextSize)
        (path[i]!).commands = .ok b) :
    ∃ f, kemRiFragment kem geom path ke mac path.size i = .ok f := by
  obtain ⟨b, hb⟩ := h
  unfold kemRiFragment
  simp only [hb]
  by_cases hc : (!i == path.size - 1) = true <;> simp only [hc] <;> exact ⟨_, rfl⟩

variable {geom} in
/-- **Every routing fragment of a route builds.** Only the last hop has commands, and a
recipient or a reply ID fits its budget. -/
theorem path_fragment_builds (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (RSOR.Key kem)) (last : List RoutingCommand)
    (hlast : (∃ r, last = [.recipient r]) ∨ ∃ id, last = [.surbReply id])
    (ke : Array ByteArray) (mac : ByteArray) (i : ℕ) (hi : i < R.hops.length) :
    ∃ f, kemRiFragment kem geom (RSOR.path kem R last) ke mac (RSOR.path kem R last).size i
      = .ok f := by
  obtain ⟨hnnh, hperhopEq, -, -⟩ := id hvalid
  have hnn : Constants.nextNodeHopLength = 65 := by decide
  refine kemRiFragment_builds kem geom _ ke mac i ?_
  rw [RSOR.path_getElem! kem R last i hi, RSOR.path_size]
  by_cases hl : i + 1 = R.hops.length
  · have hterm : (i == R.hops.length - 1) = true := by simp; omega
    simp only [hl, hterm, ite_true]
    cases h : commandsToBytes (geom.perHopRoutingInfoLength - kem.ciphertextSize) last with
    | ok b => exact ⟨b, rfl⟩
    | error e =>
      exfalso
      rcases hlast with ⟨r, rfl⟩ | ⟨id, rfl⟩
      · have hb : ¬ (geom.perHopRoutingInfoLength - kem.ciphertextSize < 33) := by
          rw [hperhopEq, hnnh, hnn]
          omega
        simp [commandsToBytes, RoutingCommand.toBytes, hb] at h
      · have hb : ¬ (geom.perHopRoutingInfoLength - kem.ciphertextSize < 17) := by
          rw [hperhopEq, hnnh, hnn]
          omega
        simp [commandsToBytes, RoutingCommand.toBytes, hb] at h
  · simp only [hl, ite_false]
    exact ⟨ByteArray.empty, by simp [commandsToBytes]⟩

/-- The header trace builds when every routing fragment does. -/
theorem hdrTrace_builds (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ke : Array ByteArray) (filler : ByteArray) (path : Array PathHop)
    (h : ∀ i, i < path.size → ∀ mac, ∃ f, kemRiFragment kem geom path ke mac path.size i = .ok f)
    (j : ℕ) (hj : j ≤ path.size) :
    ∃ s, hdrTrace kem geom ks tag ke filler path j = .ok s := by
  induction j with
  | zero => exact ⟨_, rfl⟩
  | succ j ih =>
    obtain ⟨s, hs⟩ := ih (by omega)
    obtain ⟨f, hf⟩ := h (path.size - 1 - j) (by omega) s.2
    rw [hdrTrace, hs]
    simp only [hf]
    exact ⟨_, rfl⟩

variable (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)

/-- **An encapsulation to a relay's key does not fail**: a relay's key is a derived one. -/
theorem kemEncap_key (k : RSOR.Key kem) (s : Vector UInt8 32) :
    ∃ ct ss, kemEncap kem (ofVector (kem.encodePublicKey k.1)) s = .ok (ct, ss) := by
  obtain ⟨sk, hk⟩ := k.2
  obtain ⟨c, p, s', h⟩ := kem.encap_derived sk (kem.stateFromSeed s)
  unfold kemEncap
  rw [Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector, kem.decode_encode_pub, hk]
  dsimp only
  rw [h]
  exact ⟨_, _, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **A packet builds** when its sizes are right, every encapsulation succeeds and every
routing fragment builds. -/
theorem newKEMPacket_builds (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (hops : Array PathHop) (payload : ByteArray) (hpos : hops.size ≠ 0)
    (hle : hops.size ≤ geom.nrHops) (hss : seeds.size = hops.size)
    (hfs : geom.nrHops > hops.size →
      filler.size = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)
    (hp : payload.size = geom.forwardPayloadLength)
    (henc : ∀ i, i < hops.size → ∃ ct ss,
      kemEncap kem (hops[i]!).publicKey (seeds[i]!) = .ok (ct, ss))
    (hfrag : ∀ i, i < hops.size → ∀ ke mac,
      ∃ f, kemRiFragment kem geom hops ke mac hops.size i = .ok f) :
    ∃ pkt, newKEMPacket kem cipher macS kdfS streamS geom seeds filler hops payload = .ok pkt := by
  -- the ciphertexts and keys of the hops' encapsulations
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ByteArray × ByteArray, E = fun i =>
      match kemEncap kem (hops[i]!).publicKey (seeds[i]!) with
      | .ok x => x
      | .error _ => (ByteArray.empty, ByteArray.empty) := ⟨_, rfl⟩
  have hkc : ∀ i (_ : i < hops.size), ∃ ct ss,
      kemEncap kem (hops[i]!).publicKey (seeds[i]!) = Except.ok (ct, ss)
        ∧ (Array.ofFn fun i : Fin hops.size => (E i).1)[i]! = ct
        ∧ (Array.ofFn fun i : Fin hops.size => deriveHopKeys kdfS (E i).2)[i]! = deriveHopKeys kdfS
            ss := fun i hi => by
    obtain ⟨ct, ss, h⟩ := henc i hi
    have h2 := h
    rw [getElem!_pos hops i hi] at h2
    refine ⟨ct, ss, h, ?_, ?_⟩
    · rw [getElem!_pos _ _ (by simpa using hi)]
      simp [hE, h2]
    · rw [getElem!_pos _ _ (by simpa using hi)]
      simp [hE, h2]
  have hcreate := createKEMHeader_eq_createKEMHeaderFrom kem macS kdfS streamS geom seeds filler
    hops (Array.ofFn fun i : Fin hops.size => (E i).1) (Array.ofFn fun i : Fin hops.size =>
        deriveHopKeys kdfS (E i).2)
    hpos hle hss hfs (by simp) (by simp) hkc
  obtain ⟨st, hst⟩ := hdrTrace_builds kem geom
    (keysKs geom streamS (Array.ofFn fun i : Fin hops.size => deriveHopKeys kdfS (E i).2)) (keysTag
        macS (Array.ofFn fun i : Fin hops.size => deriveHopKeys kdfS (E i).2)) (Array.ofFn fun i :
        Fin hops.size => (E i).1) filler hops
    (fun i hi mac => hfrag i hi _ mac) hops.size le_rfl
  have hF := hdrTrace_createKEMHeaderFrom kem geom macS streamS (Array.ofFn fun i : Fin hops.size
      => (E i).1) (Array.ofFn fun i : Fin hops.size => deriveHopKeys kdfS (E i).2) filler hops st
      hst
  unfold newKEMPacket
  simp only [hp, ne_eq, not_true_eq_false, ↓reduceIte, hcreate, hF,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  exact ⟨_, rfl⟩

variable {geom} in
/-- **The first layer over a route builds**, for any draw and any payload of the right
length. -/
theorem layer_zero_builds (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (RSOR.Key kem)) (hR : 0 < R.hops.length)
    (last : List RoutingCommand)
    (hlast : (∃ r, last = [.recipient r]) ∨ ∃ id, last = [.surbReply id])
    (d : RSOR.Draw geom) (payload : ByteArray) (hp : payload.size = geom.forwardPayloadLength) :
    ∃ pkt, RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload 0
      = .ok pkt := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hn := RSOR.path_size kem R last
  have hle := R.length_le
  have hb : (geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  unfold RSOR.layer
  simp only [RSOR.fillerAt, Array.extract_size]
  refine newKEMPacket_builds kem geom cipher macS kdfS streamS _ _ _ payload (by omega)
    (by omega) (by simp; omega)
    (fun _ => by rw [ByteArray.size_extract, Util.Bytes.size_ofVector]; omega) hp
    (fun i hi => ?_)
    (fun i hi ke mac => path_fragment_builds kem hvalid R last hlast ke mac i (by omega))
  rw [RSOR.path_getElem! kem R last i (by omega)]
  exact kemEncap_key kem _ _

variable {geom} in
/-- **Reliable seeds are all a route needs to build.** -/
theorem builds_of_reliable (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (RSOR.Key kem)) (last : List RoutingCommand)
    (hlast : (∃ r, last = [.recipient r]) ∨ ∃ id, last = [.surbReply id])
    (d : RSOR.Draw geom) (payload : ByteArray) (hp : payload.size = geom.forwardPayloadLength)
    (hrel : ∀ i < R.hops.length, kem.Reliable (kem.stateFromSeed d.1.toArray[i]!)) :
    RSOR.Builds kem cipher macS kdfS streamS geom R last d payload :=
  ⟨hrel, fun h => layer_zero_builds kem cipher macS kdfS streamS hvalid R h last hlast d payload
    hp⟩

end Builds

end Cryptlib.Protocols.Sphinx.KEMSphinx
