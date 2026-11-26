/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxPad

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

/-- **The headers in front read the hops in front.** Wrapping a header in the headers of hops
`i` to `i + n` gives the same bytes on two paths with two draws that agree on those hops, on
the name of the hop after each, and on their seeds. -/
theorem hdrUp_congr (hops hops' : Array PathHop) (d d' : RSOR.Draw geom)
    (hlen : hops.size ≤ geom.nrHops) (hlen' : hops'.size ≤ geom.nrHops) (i n : ℕ)
    (H : ByteArray)
    (h : ∀ k, i ≤ k → k < i + n → k + 1 < hops.size ∧ k + 1 < hops'.size
      ∧ hops[k]! = hops'[k]! ∧ (hops[k + 1]!).id = (hops'[k + 1]!).id
      ∧ d.1.toArray[k]! = d'.1.toArray[k]!) :
    hdrUp kem macS kdfS streamS geom hops d i n H
      = hdrUp kem macS kdfS streamS geom hops' d' i n H := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hk, hk', e0, e1, es⟩ := h i le_rfl (by omega)
    have hS : (d.1.toArray.extract 0 hops.size).size = hops.size := by simp; omega
    have hS' : (d'.1.toArray.extract 0 hops'.size).size = hops'.size := by simp; omega
    have p0 : (hops.extract i hops.size)[0]! = (hops'.extract i hops'.size)[0]! := by
      rw [getElem!_extract_from hops i 0 (by omega), getElem!_extract_from hops' i 0 (by omega)]
      exact e0
    have p1 : ((hops.extract i hops.size)[1]!).id = ((hops'.extract i hops'.size)[1]!).id := by
      rw [getElem!_extract_from hops i 1 (by omega), getElem!_extract_from hops' i 1 (by omega)]
      exact e1
    have s0 : ((d.1.toArray.extract 0 hops.size).extract i
          (d.1.toArray.extract 0 hops.size).size)[0]!
        = ((d'.1.toArray.extract 0 hops'.size).extract i
          (d'.1.toArray.extract 0 hops'.size).size)[0]! := by
      have hx : ∀ (a : Array (Vector UInt8 32)) (m : ℕ), i < m → m ≤ a.size →
          (a.extract 0 m)[i + 0]! = a[i]! := fun a m h1 h2 => by
        rw [Nat.add_zero, getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
        simp
      rw [getElem!_extract_from _ i 0 (by omega), getElem!_extract_from _ i 0 (by omega),
        hx _ _ (by omega) (by simp; omega), hx _ _ (by omega) (by simp; omega)]
      exact es
    unfold hdrUp
    rw [ih (i + 1) fun k hk1 hk2 => h k (by omega) (by omega)]
    unfold hdrHop kemHopCt kemHopKeys
    rw [p0, s0, kemRiFragment_path_congr geom kem _ (hops'.extract i hops'.size) _ _ _
      (hops'.extract i hops'.size).size p0 p1 (by simp; omega)]

omit kem cipher macS kdfS streamS geom in
/-- A uniform draw pushed through a bijection is a uniform draw. -/
theorem evalDistEq_of_bijective {γ δ : Type} [SampleableType γ] {g : γ → γ}
    (hg : Function.Bijective g) (K : γ → ProbComp δ) :
    ($ᵗ γ >>= fun x => K (g x)) =ᵈ ($ᵗ γ >>= K) := by
  have hb : Function.Bijective (Function.uncurry fun (_ : Vector UInt8 0) (x : γ) => g x) :=
    ⟨fun a b h => Prod.ext (Vector.ext fun i hi => absurd hi (Nat.not_lt_zero i)) (hg.1 h),
      fun y => (hg.2 y).elim fun x hx => ⟨(default, x), hx⟩⟩
  exact (OracleComp.EvalDistEq.bind_const _ _).symm.trans (evalDistEq_pair_of_bijective hb K)

omit kem cipher macS kdfS streamS geom in
/-- **One answer of the ideal cipher's decryption is a uniform draw.** For a fixed block `y`,
the block `w` when `y` is the uniform `u`, and the block `v` otherwise, is uniform when `u`,
`w` and `v` are. -/
theorem evalDistEq_ite_fresh {γ δ : Type} [SampleableType γ] [DecidableEq γ] (y : γ)
    (K : γ → ProbComp δ) :
    (do
      let u ← $ᵗ γ
      let w ← $ᵗ γ
      let v ← $ᵗ γ
      K (if y = u then w else v)) =ᵈ ($ᵗ γ >>= K) := by
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun u => ?_)
    (OracleComp.EvalDistEq.bind_const ($ᵗ γ) ($ᵗ γ >>= K))
  by_cases h : y = u
  · simp only [h, ↓reduceIte]
    exact EvalDistEq.bind_right _ fun w => OracleComp.EvalDistEq.bind_const _ _
  · simp only [h, ↓reduceIte]
    exact OracleComp.EvalDistEq.bind_const _ _

omit macS streamS in
/-- A run of hops' payload encryptions keeps the payload's length. -/
theorem payUp_size (hops : Array PathHop) (d : RSOR.Draw geom) (n i : ℕ) (P : ByteArray) :
    (payUp kem cipher kdfS geom hops d i n P).size = P.size := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    show (cipher.encrypt _ _ _).size = _
    rw [cipher.encrypt_size, ih]

omit macS streamS in
/-- A run of hops' payload encryptions loses nothing, on payloads of at least 16 bytes. -/
theorem payUp_injective (hops : Array PathHop) (d : RSOR.Draw geom) (n i : ℕ)
    (P P' : ByteArray) (hP : 16 ≤ P.size) (hP' : 16 ≤ P'.size)
    (h : payUp kem cipher kdfS geom hops d i n P = payUp kem cipher kdfS geom hops d i n P') :
    P = P' := by
  induction n generalizing i with
  | zero => exact h
  | succ n ih =>
    have h' := congrArg (cipher.decrypt
      (kemHopKeys kem kdfS (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size)
            0).payloadEncryption.toArray
      (ofVector (kemHopKeys kem kdfS (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size)
            0).headerEncryptionIV)) h
    change cipher.decrypt _ _ (cipher.encrypt _ _ _) = cipher.decrypt _ _ (cipher.encrypt _ _ _)
      at h'
    rw [cipher.roundTrip _ _ _ (by rw [payUp_size]; exact hP),
      cipher.roundTrip _ _ _ (by rw [payUp_size]; exact hP')] at h'
    exact ih (i + 1) h'

omit macS streamS in
/-- **A uniform payload stays uniform under a run of hops' payload encryptions.** -/
theorem evalDistEq_payUp {δ : Type}
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (n i : ℕ)
    (K : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → ProbComp δ) :
    ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun e =>
        K (toVecN _ (payUp kem cipher kdfS geom hops d i n (ofVector e))))
      =ᵈ ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= K) := by
  refine evalDistEq_of_bijective (Finite.injective_iff_bijective.1 fun e e' h => ?_) K
  have hs : ∀ x : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength),
      (payUp kem cipher kdfS geom hops d i n (ofVector x)).size
        = geom.payloadTagLength + geom.forwardPayloadLength := fun x => by
    rw [payUp_size, Util.Bytes.size_ofVector]
  have h' := congrArg ofVector h
  rw [ofVector_toVecN _ (hs e), ofVector_toVecN _ (hs e')] at h'
  have h2 := payUp_injective kem cipher kdfS geom hops d n i _ _
    (by rw [Util.Bytes.size_ofVector]; exact h16) (by rw [Util.Bytes.size_ofVector]; exact h16) h'
  have h3 := congrArg (toVecN (geom.payloadTagLength + geom.forwardPayloadLength)) h2
  rwa [toVecN_ofVector,
    toVecN_ofVector] at h3

/-- **A wrapped layer splits into the wrapped header and the wrapped payload.** -/
theorem wrapUp_split (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (n i : ℕ) (H P : ByteArray)
    (hn : i + n < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hcmd : ∀ m, i ≤ m → m < i + n → (hops[m]!).commands = [])
    (hct : ∀ m, i ≤ m → m < i + n → (kemHopCt kem (hops.extract m hops.size)
      ((d.1.toArray.extract 0 hops.size).extract m (d.1.toArray.extract 0 hops.size).size)
        0).size = kem.ciphertextSize)
    (hH : H.size = payloadOffset kem geom) :
    RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom hops d i n (H ++ P))
      = (toVecN _ (hdrUp kem macS kdfS streamS geom hops d i n H),
        toVecN _ (payUp kem cipher kdfS geom hops d i n P)) := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hsz := hdrUp_size kem macS kdfS streamS geom hvalid hmactag hops d n i H hn hlen hcmd hct
    hH
  have hsz' : (hdrUp kem macS kdfS streamS geom hops d i n H).size = geom.headerLength := by
    rw [hsz, hhdr, had]
  rw [wrapUp_append kem cipher macS kdfS streamS geom hvalid hmactag hops d n i H P hn hlen hcmd
    hct hH]
  have e1 : (hdrUp kem macS kdfS streamS geom hops d i n H
      ++ payUp kem cipher kdfS geom hops d i n P).extract 0 geom.headerLength
      = hdrUp kem macS kdfS streamS geom hops d i n H := by
    rw [← hsz']
    exact Util.Bytes.extract_append_left _ _
  have e2 : (hdrUp kem macS kdfS streamS geom hops d i n H
      ++ payUp kem cipher kdfS geom hops d i n P).extract geom.headerLength
        (hdrUp kem macS kdfS streamS geom hops d i n H
          ++ payUp kem cipher kdfS geom hops d i n P).size
      = payUp kem cipher kdfS geom hops d i n P := by
    rw [ByteArray.size_append, ← hsz']
    exact Util.Bytes.extract_append_right _ _
  unfold RSOR.split
  rw [e1, e2]

end Wrap

end Cryptlib.Protocols.Sphinx.KEMSphinx
