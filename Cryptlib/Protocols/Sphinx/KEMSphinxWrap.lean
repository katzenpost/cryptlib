/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxPad

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

/-! # A wrapped layer is a wrapped header and a wrapped payload

A hop wraps what it forwards in two parts that do not mix: the header from the forwarded
header, and the payload from the forwarded payload under its payload key (`wrapHop_append`).
So does a run of hops (`wrapUp_append`). The header part does not use the payload cipher. -/

section Wrap

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- A hop's header from the header it forwards. -/
def hdrHop (path : Array PathHop) (ct : ByteArray) (K : HopKeys) (H : ByteArray) : ByteArray :=
  v0AD ++ ct
    ++ xorBytes
      ((match kemRiFragment kem geom path
          #[ByteArray.empty, H.extract 2 (2 + kem.ciphertextSize)]
          (H.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
            (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)) path.size 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ H.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength))
      ((streamS.keystream (ofVector K.headerEncryption) (ofVector K.headerEncryptionIV)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0 geom.routingInfoLength)
    ++ ofVector (macS.mac (ofVector K.headerMAC) (v0AD ++ ct
      ++ xorBytes
        ((match kemRiFragment kem geom path
            #[ByteArray.empty, H.extract 2 (2 + kem.ciphertextSize)]
            (H.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
              (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)) path.size 0 with
          | .ok f => f
          | .error _ => ByteArray.empty)
          ++ H.extract (2 + kem.ciphertextSize)
            (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength))
        ((streamS.keystream (ofVector K.headerEncryption) (ofVector K.headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
            geom.routingInfoLength)
      ++ ByteArray.empty))

/-- **One hop wraps the header and the payload apart.** -/
theorem wrapHop_append (path : Array PathHop) (ct : ByteArray) (K : HopKeys) (H P : ByteArray)
    (hH : H.size = payloadOffset kem geom) :
    wrapHop kem cipher macS streamS geom path ct K (H ++ P)
      = hdrHop kem macS streamS geom path ct K H
        ++ cipher.encrypt K.payloadEncryption.toArray (ofVector K.headerEncryptionIV) P := by
  have e1 : ∀ lo hi, hi ≤ payloadOffset kem geom → (H ++ P).extract lo hi = H.extract lo hi :=
    fun lo hi h => Cryptlib.Util.Bytes.extract_append_of_le H P (hH ▸ h)
  have e2 : (H ++ P).extract (payloadOffset kem geom) (H ++ P).size = P := by
    rw [ByteArray.size_append, ← hH]
    exact Cryptlib.Util.Bytes.extract_append_right H P
  unfold wrapHop layerIn hdrHop
  rw [e2, e1 2 (2 + kem.ciphertextSize) (by unfold payloadOffset; omega),
    e1 (2 + kem.ciphertextSize + geom.routingInfoLength)
      (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
      (by unfold payloadOffset; omega),
    e1 (2 + kem.ciphertextSize)
      (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength)
      (by unfold payloadOffset; omega)]
  rfl

set_option maxHeartbeats 1000000 in
/-- A hop with no commands of its own, before the end of its path, wraps a header into a
header. -/
theorem hdrHop_size (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (path : Array PathHop) (ct : ByteArray) (K : HopKeys) (H : ByteArray)
    (h2 : 2 ≤ path.size) (hlen : path.size ≤ geom.nrHops) (hcmd : (path[0]!).commands = [])
    (hct : ct.size = kem.ciphertextSize) (hH : H.size = payloadOffset kem geom) :
    (hdrHop kem macS streamS geom path ct K H).size = payloadOffset kem geom := by
  obtain ⟨hnnh, hperhopEq, hrouting, -, -, -⟩ := id hvalid
  have hv0 : v0AD.size = 2 := rfl
  have hpR : geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hH' : H.size = 2 + kem.ciphertextSize + geom.routingInfoLength + macLength := hH
  have hke1 : (Array.replicate path.size (H.extract 2 (2 + kem.ciphertextSize)))[1]!
      = H.extract 2 (2 + kem.ciphertextSize) := by
    rw [getElem!_pos _ 1 (by simp; omega)]
    simp
  have hksz : ∀ i (hi : i < (Array.replicate path.size
        (H.extract 2 (2 + kem.ciphertextSize))).size),
      ((Array.replicate path.size (H.extract 2 (2 + kem.ciphertextSize)))[i]'hi).size
        = kem.ciphertextSize := fun i hi => by
    simp only [Array.getElem_replicate, ByteArray.size_extract]
    omega
  unfold hdrHop
  cases hfr : kemRiFragment kem geom path
      #[ByteArray.empty, H.extract 2 (2 + kem.ciphertextSize)]
      (H.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)) path.size 0 with
  | error e =>
    exfalso
    unfold kemRiFragment at hfr
    simp [hcmd, commandsToBytes, show ¬ (0 = path.size - 1) by omega] at hfr
  | ok frag =>
    have hfr' : kemRiFragment kem geom path
        (Array.replicate path.size (H.extract 2 (2 + kem.ciphertextSize)))
        (H.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
          (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)) path.size 0
        = .ok frag := by
      rw [kemRiFragment_zero_congr, hke1]
      exact hfr
    have hfsz' := kemRiFragment_size kem geom _ _ _ _ 0 (by omega) (by omega) hnnh
      (by simp) hksz frag hfr'
    simp only [ByteArray.size_append, size_xorBytes, ByteArray.size_extract, hfsz', hct, hv0,
      Cryptlib.Util.Bytes.size_ofVector, hmactag]
    unfold payloadOffset
    omega

/-- A run of hops' headers from the header the last of them forwards. -/
def hdrUp (hops : Array PathHop) (d : RSOR.Draw geom) : ℕ → ℕ → ByteArray → ByteArray
  | _, 0, H => H
  | i, n + 1, H => hdrHop kem macS streamS geom (hops.extract i hops.size)
      (kemHopCt kem (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size) 0)
      (kemHopKeys kem kdfS (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size) 0)
      (hdrUp hops d (i + 1) n H)

/-- A run of hops' payloads from the payload the last of them forwards. -/
def payUp (hops : Array PathHop) (d : RSOR.Draw geom) : ℕ → ℕ → ByteArray → ByteArray
  | _, 0, P => P
  | i, n + 1, P => cipher.encrypt
      (kemHopKeys kem kdfS (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size)
            0).payloadEncryption.toArray
      (ofVector (kemHopKeys kem kdfS (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size)
            0).headerEncryptionIV)
      (payUp hops d (i + 1) n P)

/-- A run of hops with no commands of their own, before the end of the path, wraps a header
into a header. -/
theorem hdrUp_size (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (n i : ℕ) (H : ByteArray)
    (hn : i + n < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hcmd : ∀ m, i ≤ m → m < i + n → (hops[m]!).commands = [])
    (hct : ∀ m, i ≤ m → m < i + n → (kemHopCt kem (hops.extract m hops.size)
      ((d.1.toArray.extract 0 hops.size).extract m (d.1.toArray.extract 0 hops.size).size) 0).size
          = kem.ciphertextSize)
    (hH : H.size = payloadOffset kem geom) :
    (hdrUp kem macS kdfS streamS geom hops d i n H).size = payloadOffset kem geom := by
  induction n generalizing i with
  | zero => exact hH
  | succ n ih =>
    have h0 : (hops.extract i hops.size)[0]! = hops[i]! := by
      have := getElem!_extract_from hops i 0 (by omega)
      rwa [Nat.add_zero] at this
    exact hdrHop_size kem macS streamS geom hvalid hmactag _ _ _ _ (by simp; omega)
      (by simp; omega)
      (by rw [h0]; exact hcmd i le_rfl (by omega)) (hct i le_rfl (by omega))
      (ih (i + 1) (by omega) (fun m h1 h2 => hcmd m (by omega) (by omega))
        (fun m h1 h2 => hct m (by omega) (by omega)))

/-- **A run of hops wraps the header and the payload apart.** -/
theorem wrapUp_append (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (n i : ℕ) (H P : ByteArray)
    (hn : i + n < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hcmd : ∀ m, i ≤ m → m < i + n → (hops[m]!).commands = [])
    (hct : ∀ m, i ≤ m → m < i + n → (kemHopCt kem (hops.extract m hops.size)
      ((d.1.toArray.extract 0 hops.size).extract m (d.1.toArray.extract 0 hops.size).size) 0).size
          = kem.ciphertextSize)
    (hH : H.size = payloadOffset kem geom) :
    wrapUp kem cipher macS kdfS streamS geom hops d i n (H ++ P)
      = hdrUp kem macS kdfS streamS geom hops d i n H
        ++ payUp kem cipher kdfS geom hops d i n P := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    show wrapHop kem cipher macS streamS geom _ _ _
      (wrapUp kem cipher macS kdfS streamS geom hops d (i + 1) n (H ++ P)) = _
    rw [ih (i + 1) (by omega) (fun m h1 h2 => hcmd m (by omega) (by omega))
        (fun m h1 h2 => hct m (by omega) (by omega)),
      wrapHop_append kem cipher macS streamS geom _ _ _ _ _
        (hdrUp_size kem macS kdfS streamS geom hvalid hmactag hops d n (i + 1) H (by omega) hlen
          (fun m h1 h2 => hcmd m (by omega) (by omega))
          (fun m h1 h2 => hct m (by omega) (by omega)) hH)]
    rfl

end Wrap

end Cryptlib.Protocols.Sphinx.KEMSphinx
