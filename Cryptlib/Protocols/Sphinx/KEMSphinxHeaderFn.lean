/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTail

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.NIKESphinx (HopKeys deriveHopKeys)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Util.Bytes (ofVector)

/-! # The header as a function of each hop's keystream and MAC

`createKEMHeaderFrom` uses a hop's keys in two ways: it draws the hop's header keystream, and it
computes one MAC. `hdrTrace` is the header written from those two things given directly, a
keystream and a tagging function per hop. `createKEMHeaderFrom_hdrTrace` and
`hdrTrace_createKEMHeaderFrom` say the two agree. So a header built with uniform keys at one hop
is the same function of that hop's keystream and of its tagging function as a real one, which is
what lets the stream cipher and the MAC be replaced one at a time. -/

section HeaderFn

variable (kem : KEM) (geom : Geometry)

/-- The padding after hop `i`: the tail of its keystream, with the padding after the hop before
it folded into the front. -/
def padAt (ks : ℕ → ByteArray) : ℕ → ByteArray
  | 0 => (ks 0).extract
      (geom.routingInfoLength + geom.perHopRoutingInfoLength
        - (0 + 1) * geom.perHopRoutingInfoLength)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)
  | i + 1 =>
    xorBytes (((ks (i + 1)).extract
        (geom.routingInfoLength + geom.perHopRoutingInfoLength
          - (i + 1 + 1) * geom.perHopRoutingInfoLength)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0 (padAt ks i).size)
      (padAt ks i)
    ++ ((ks (i + 1)).extract
        (geom.routingInfoLength + geom.perHopRoutingInfoLength
          - (i + 1 + 1) * geom.perHopRoutingInfoLength)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract (padAt ks i).size
      ((ks (i + 1)).extract
        (geom.routingInfoLength + geom.perHopRoutingInfoLength
          - (i + 1 + 1) * geom.perHopRoutingInfoLength)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size

/-- The routing info and the MAC after the last `j` hops of the path, from each hop's keystream
`ks` and tagging function `tag`. -/
def hdrTrace (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ke : Array ByteArray)
    (filler : ByteArray) (path : Array PathHop) : ℕ → Except String (ByteArray × ByteArray)
  | 0 => .ok (if geom.nrHops > path.size then filler else ByteArray.empty, ByteArray.empty)
  | j + 1 =>
    match hdrTrace ks tag ke filler path j with
    | .error e => .error e
    | .ok s =>
      match kemRiFragment kem geom path ke s.2 path.size (path.size - 1 - j) with
      | .error e => .error e
      | .ok frag =>
        .ok (xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)),
          tag (path.size - 1 - j) (v0AD ++ ke[path.size - 1 - j]!
            ++ xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
              (geom.routingInfoLength + geom.perHopRoutingInfoLength
                - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength))
            ++ (if path.size - 1 - j > 0 then padAt geom ks (path.size - 1 - j - 1)
              else ByteArray.empty)))

/-- `padAt` reads the keystreams of the hops up to `i` only. -/
theorem padAt_congr (ks ks' : ℕ → ByteArray) (i : ℕ) (h : ∀ m ≤ i, ks m = ks' m) :
    padAt geom ks i = padAt geom ks' i := by
  induction i with
  | zero => simp only [padAt, h 0 le_rfl]
  | succ i ih => simp only [padAt, h (i + 1) le_rfl, ih fun m hm => h m (Nat.le_succ_of_le hm)]

/-- `hdrTrace` reads the keystreams and tagging functions of the path's hops only. -/
theorem hdrTrace_congr (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ke : Array ByteArray) (filler : ByteArray) (path : Array PathHop)
    (h : ∀ i, i < path.size → ks i = ks' i ∧ tag i = tag' i) (j : ℕ) (hj : j ≤ path.size) :
    hdrTrace kem geom ks tag ke filler path j = hdrTrace kem geom ks' tag' ke filler path j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [hdrTrace, hdrTrace, ih (by omega)]
    simp only [(h (path.size - 1 - j) (by omega)).1, (h (path.size - 1 - j) (by omega)).2,
      padAt_congr geom ks ks' (path.size - 1 - j - 1) fun m _ => (h m (by omega)).1]

/-- A step of `hdrTrace` that succeeds: the steps before it succeeded, and so did the routing
fragment. -/
theorem hdrTrace_succ_ok (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ke : Array ByteArray) (filler : ByteArray) (path : Array PathHop) (j : ℕ)
    (x : ByteArray × ByteArray)
    (h : hdrTrace kem geom ks tag ke filler path (j + 1) = .ok x) :
    ∃ s frag, hdrTrace kem geom ks tag ke filler path j = .ok s ∧
      kemRiFragment kem geom path ke s.2 path.size (path.size - 1 - j) = .ok frag ∧
      x = (xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
          (geom.routingInfoLength + geom.perHopRoutingInfoLength
            - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)),
        tag (path.size - 1 - j) (v0AD ++ ke[path.size - 1 - j]!
          ++ xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength))
          ++ (if path.size - 1 - j > 0 then padAt geom ks (path.size - 1 - j - 1)
            else ByteArray.empty))) := by
  rw [hdrTrace] at h
  split at h
  · cases h
  · next s hs =>
    split at h
    · cases h
    · next frag hf => exact ⟨s, frag, hs, hf, (Except.ok.inj h).symm⟩

/-- Whether a hop's routing fragment can be built depends on the path only: its commands must
fit their slot. -/
theorem kemRiFragment_ok_congr (path : Array PathHop) (ke ke' : Array ByteArray)
    (mac mac' : ByteArray) (n i : ℕ) (f : ByteArray)
    (h : kemRiFragment kem geom path ke mac n i = .ok f) :
    ∃ f', kemRiFragment kem geom path ke' mac' n i = .ok f' := by
  unfold kemRiFragment at h ⊢
  dsimp only at h ⊢
  obtain ⟨b, hb, -⟩ := Cryptlib.Protocols.Sphinx.Common.Except.eq_ok_of_bind_eq_ok h
  rw [hb]
  by_cases ht : (!i == n - 1) = true
  · simp only [ht, ↓reduceIte]
    exact ⟨_, rfl⟩
  · simp only [ht]
    exact ⟨_, rfl⟩

/-- Whether `hdrTrace` succeeds depends on the path only. -/
theorem hdrTrace_ok_congr (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ke ke' : Array ByteArray) (filler filler' : ByteArray) (path : Array PathHop) (j : ℕ)
    (s : ByteArray × ByteArray) (h : hdrTrace kem geom ks tag ke filler path j = .ok s) :
    ∃ s', hdrTrace kem geom ks' tag' ke' filler' path j = .ok s' := by
  induction j generalizing s with
  | zero => exact ⟨_, rfl⟩
  | succ j ih =>
    obtain ⟨s0, frag, hs0, hf, -⟩ := hdrTrace_succ_ok kem geom ks tag ke filler path j s h
    obtain ⟨s0', hs0'⟩ := ih s0 hs0
    obtain ⟨frag', hf'⟩ := kemRiFragment_ok_congr kem geom path ke ke' s0.2 s0'.2 path.size
      (path.size - 1 - j) frag hf
    rw [hdrTrace, hs0']
    dsimp only
    rw [hf']
    exact ⟨_, rfl⟩

variable (macS : MAC) (streamS : StreamCipher)

/-- Each hop's header keystream, from its keys. -/
def keysKs (keys : Array HopKeys) (i : ℕ) : ByteArray :=
  streamS.keystream (ofVector (keys[i]!).headerEncryption) (ofVector (keys[i]!).headerEncryptionIV)
    (geom.routingInfoLength + geom.perHopRoutingInfoLength)

/-- Each hop's tagging function, from its keys. -/
def keysTag (keys : Array HopKeys) (i : ℕ) (m : ByteArray) : ByteArray :=
  ofVector (macS.mac (ofVector (keys[i]!).headerMAC) m)

/-- The header `createKEMHeaderFrom` builds is `hdrTrace`'s, on the keystreams and tagging
functions of its keys. -/
theorem createKEMHeaderFrom_hdrTrace (kemElements : Array ByteArray) (keys : Array HopKeys)
    (filler : ByteArray) (path : Array PathHop) (hdr : ByteArray) (sprpKeys : Array SPRPKey)
    (h : createKEMHeaderFrom kem macS streamS geom kemElements keys filler path
      = .ok (hdr, sprpKeys)) :
    ∃ s, hdrTrace kem geom (keysKs geom streamS keys) (keysTag macS keys) kemElements filler path
        path.size = .ok s ∧
      hdr = v0AD ++ kemElements[0]! ++ s.1 ++ s.2 ∧
      sprpKeys = Array.ofFn (fun i : Fin path.size =>
        { key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV }) := by
  obtain ⟨riKeyStream, riPadding, s, -, -, hcont, hs0, hstep, hhdr, hsprp⟩ :=
    createKEMHeaderFrom_unfold kem macS streamS geom kemElements keys filler path hdr sprpKeys h
  have hpad : ∀ i, i < path.size → riPadding[i]! = padAt geom (keysKs geom streamS keys) i := by
    intro i
    induction i with
    | zero =>
      intro hi
      have := (hcont 0 hi).2
      simp only [gt_iff_lt, lt_self_iff_false, ↓reduceIte] at this
      rw [this]
      rfl
    | succ i ih =>
      intro hi
      have := (hcont (i + 1) hi).2
      simp only [gt_iff_lt, Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel] at this
      rw [this, ih (by omega)]
      rfl
  have htr : ∀ j, j ≤ path.size →
      hdrTrace kem geom (keysKs geom streamS keys) (keysTag macS keys) kemElements filler path j
        = .ok (s j) := by
    intro j
    induction j with
    | zero => intro _; rw [hs0]; rfl
    | succ j ih =>
      intro hj
      obtain ⟨frag, hfrag, h1, h2⟩ := hstep j (by omega)
      rw [hdrTrace, ih (by omega)]
      dsimp only
      rw [hfrag]
      dsimp only
      rw [(hcont (path.size - 1 - j) (by omega)).1] at h1
      have h1' : (s (j + 1)).1 = xorBytes (frag ++ (s j).1)
          ((keysKs geom streamS keys (path.size - 1 - j)).extract 0
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)) := h1
      rw [← h1']
      congr 1
      refine Prod.ext rfl ?_
      rw [h2]
      by_cases hp : path.size - 1 - j > 0
      · simp only [hp, ↓reduceIte]
        rw [hpad _ (by omega)]
        rfl
      · simp only [hp, ↓reduceIte]
        rfl
  exact ⟨s path.size, htr _ le_rfl, hhdr, hsprp⟩

/-- The converse: where `hdrTrace` succeeds on the keystreams and tagging functions of the keys,
`createKEMHeaderFrom` builds its header. -/
theorem hdrTrace_createKEMHeaderFrom (kemElements : Array ByteArray) (keys : Array HopKeys)
    (filler : ByteArray) (path : Array PathHop) (s : ByteArray × ByteArray)
    (h : hdrTrace kem geom (keysKs geom streamS keys) (keysTag macS keys) kemElements filler path
      path.size = .ok s) :
    createKEMHeaderFrom kem macS streamS geom kemElements keys filler path
      = .ok (v0AD ++ kemElements[0]! ++ s.1 ++ s.2,
          Array.ofFn (fun i : Fin path.size =>
            ({ key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV }
              : SPRPKey))) := by
  have hpre : ∀ k j, j + k = path.size → ∃ x,
      hdrTrace kem geom (keysKs geom streamS keys) (keysTag macS keys) kemElements filler path j
        = .ok x := by
    intro k
    induction k with
    | zero => intro j hj; exact ⟨s, by rw [show j = path.size by omega]; exact h⟩
    | succ k ih =>
      intro j hj
      obtain ⟨x, hx⟩ := ih (j + 1) (by omega)
      obtain ⟨s', -, hs', -, -⟩ := hdrTrace_succ_ok kem geom _ _ _ _ _ j x hx
      exact ⟨s', hs'⟩
  obtain ⟨tr, htr⟩ : ∃ tr : ℕ → ByteArray × ByteArray, ∀ j, j ≤ path.size →
      hdrTrace kem geom (keysKs geom streamS keys) (keysTag macS keys) kemElements filler path j
        = .ok (tr j) := by
    refine ⟨fun j => match hdrTrace kem geom (keysKs geom streamS keys) (keysTag macS keys)
      kemElements filler path j with | .ok x => x | .error _ => (.empty, .empty), fun j hj => ?_⟩
    obtain ⟨x, hx⟩ := hpre (path.size - j) j (by omega)
    simp only [hx]
  obtain ⟨RK, hRK⟩ : ∃ RK : Array ByteArray, RK = Array.ofFn (fun i : Fin path.size =>
      (keysKs geom streamS keys i).extract 0
        (geom.routingInfoLength + geom.perHopRoutingInfoLength
          - (i.val + 1) * geom.perHopRoutingInfoLength)) := ⟨_, rfl⟩
  obtain ⟨RP, hRP⟩ : ∃ RP : Array ByteArray, RP = Array.ofFn (fun i : Fin path.size =>
      padAt geom (keysKs geom streamS keys) i) := ⟨_, rfl⟩
  have hrk : ∀ m, m < path.size → RK[m]! = (keysKs geom streamS keys m).extract 0
      (geom.routingInfoLength + geom.perHopRoutingInfoLength
        - (m + 1) * geom.perHopRoutingInfoLength) := fun m hm => by
    rw [hRK, getElem!_pos _ m (by simpa using hm)]
    simp only [Array.getElem_ofFn]
  have hrp : ∀ m, m < path.size → RP[m]! = padAt geom (keysKs geom streamS keys) m :=
    fun m hm => by
      rw [hRP, getElem!_pos _ m (by simpa using hm)]
      simp only [Array.getElem_ofFn]
  have hsn : tr path.size = s := Except.ok.inj ((htr _ le_rfl).symm.trans h)
  have := createKEMHeaderFrom_fold kem macS streamS geom kemElements keys filler path RK RP tr
    (by rw [hRK, Array.size_ofFn]) (by rw [hRP, Array.size_ofFn])
    (fun i hi => ⟨hrk i hi, by
      rw [hrp i hi]
      cases i with
      | zero =>
        simp only [gt_iff_lt, lt_self_iff_false, ↓reduceIte]
        rfl
      | succ i =>
        simp only [gt_iff_lt, Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel]
        rw [hrp i (by omega)]
        rfl⟩)
    (Except.ok.inj ((htr 0 (Nat.zero_le _)).symm.trans rfl))
    (fun j hj => by
      obtain ⟨s0, frag, hs0, hf, hx⟩ := hdrTrace_succ_ok kem geom _ _ _ _ _ j _ (htr (j + 1) hj)
      obtain rfl : s0 = tr j := Except.ok.inj (hs0.symm.trans (htr j (by omega)))
      refine ⟨frag, hf, ?_, ?_⟩
      · rw [hx, hrk _ (by omega)]
      · rw [hx]
        by_cases hp : path.size - 1 - j > 0
        · simp only [hp, ↓reduceIte, hrp _ (show path.size - 1 - j - 1 < path.size by omega)]
          rfl
        · simp only [hp, ↓reduceIte]
          rfl)
  rwa [hsn] at this

/-! ## The packet -/

variable (cipher : WideBlockCipher)

/-- The packet, from each hop's keystream `ks`, tagging function `tag` and payload encryption
`enc`. -/
def pktFn (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray) (ke : Array ByteArray)
    (filler : ByteArray) (path : Array PathHop) (payload : ByteArray) : Option ByteArray :=
  if payload.size = geom.forwardPayloadLength then
    match hdrTrace kem geom ks tag ke filler path path.size with
    | .error _ => none
    | .ok s => some (v0AD ++ ke[0]! ++ s.1 ++ s.2
        ++ (List.range' 0 path.size).foldl (fun b iRev => enc (path.size - 1 - iRev) b)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload))
  else none

/-- `pktFn` reads the keystreams, tagging functions and payload encryptions of the path's hops
only. -/
theorem pktFn_congr (ks ks' : ℕ → ByteArray) (tag tag' enc enc' : ℕ → ByteArray → ByteArray)
    (ke : Array ByteArray) (filler : ByteArray) (path : Array PathHop) (payload : ByteArray)
    (h : ∀ i, i < path.size → ks i = ks' i ∧ tag i = tag' i ∧ enc i = enc' i) :
    pktFn kem geom ks tag enc ke filler path payload
      = pktFn kem geom ks' tag' enc' ke filler path payload := by
  have hf : (List.range' 0 path.size).foldl (fun b iRev => enc (path.size - 1 - iRev) b)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)
      = (List.range' 0 path.size).foldl (fun b iRev => enc' (path.size - 1 - iRev) b)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload) :=
    List.foldl_ext _ _ _ fun b iRev hi => by
      have hlt : iRev < path.size := by simpa using hi
      rw [(h (path.size - 1 - iRev) (by omega)).2.2]
  unfold pktFn
  rw [hdrTrace_congr kem geom ks ks' tag tag' ke filler path
    (fun i hi => ⟨(h i hi).1, (h i hi).2.1⟩) _ le_rfl, hf]

/-- Whether `pktFn` gives a packet depends on the path and the payload's length only. -/
theorem pktFn_isSome_congr (ks ks' : ℕ → ByteArray) (tag tag' enc enc' : ℕ → ByteArray → ByteArray)
    (ke ke' : Array ByteArray) (filler filler' : ByteArray) (path : Array PathHop)
    (payload p : ByteArray) (h : pktFn kem geom ks tag enc ke filler path payload = some p) :
    ∃ p', pktFn kem geom ks' tag' enc' ke' filler' path payload = some p' := by
  unfold pktFn at h ⊢
  by_cases hp : payload.size = geom.forwardPayloadLength
  · simp only [hp, ↓reduceIte] at h ⊢
    cases ht : hdrTrace kem geom ks tag ke filler path path.size with
    | error e =>
      rw [ht] at h
      cases h
    | ok s =>
      obtain ⟨s', hs'⟩ := hdrTrace_ok_congr kem geom ks ks' tag tag' ke ke' filler filler' path
        path.size s ht
      rw [hs']
      exact ⟨_, rfl⟩
  · simp only [hp, ↓reduceIte] at h
    cases h

/-- **The header of a packet does not use the payload encryptions.** With other payload
encryptions `pktFn` gives a packet with the same bytes in front of the payload. -/
theorem pktFn_header (ks : ℕ → ByteArray) (tag enc enc' : ℕ → ByteArray → ByteArray)
    (ke : Array ByteArray) (filler : ByteArray) (path : Array PathHop) (payload x : ByteArray)
    (h : pktFn kem geom ks tag enc ke filler path payload = some x)
    (henc : ∀ i b, (enc i b).size = b.size) :
    ∃ x', pktFn kem geom ks tag enc' ke filler path payload = some x' ∧
      x'.extract 0 (x.size - (geom.payloadTagLength + geom.forwardPayloadLength))
        = x.extract 0 (x.size - (geom.payloadTagLength + geom.forwardPayloadLength)) := by
  unfold pktFn at h ⊢
  by_cases hp : payload.size = geom.forwardPayloadLength
  · simp only [hp, ↓reduceIte] at h ⊢
    cases ht : hdrTrace kem geom ks tag ke filler path path.size with
    | error e =>
      rw [ht] at h
      cases h
    | ok s =>
      rw [ht] at h
      dsimp only at h ⊢
      generalize v0AD ++ ke[0]! ++ s.1 ++ s.2 = H at h ⊢
      obtain rfl := Option.some.inj h
      refine ⟨_, rfl, ?_⟩
      have hsz : ∀ (l : List ℕ) (b : ByteArray),
          (l.foldl (fun b iRev => enc (path.size - 1 - iRev) b) b).size = b.size := by
        intro l
        induction l with
        | nil => intro b; rfl
        | cons a l ih => intro b; rw [List.foldl_cons, ih, henc]
      have hinit : ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload).size
          = geom.payloadTagLength + geom.forwardPayloadLength := by
        rw [ByteArray.size_append, hp]
        exact congrArg (· + geom.forwardPayloadLength) Array.size_replicate
      rw [ByteArray.size_append, hsz, hinit, Nat.add_sub_cancel,
        Cryptlib.Util.Bytes.extract_append_left, Cryptlib.Util.Bytes.extract_append_left]
  · simp only [hp, ↓reduceIte] at h
    cases h

/-- Each hop's payload encryption, from its keys. -/
def keysEnc (keys : Array HopKeys) (i : ℕ) (b : ByteArray) : ByteArray :=
  cipher.encrypt (keys[i]!).payloadEncryption.toArray (ofVector (keys[i]!).headerEncryptionIV) b

/-- **A packet uses a hop's keys in three ways only**: the hop's header keystream, its MAC, and
one encryption of the payload. -/
theorem newKEMPacketFrom_pktFn (kemElements : Array ByteArray) (keys : Array HopKeys)
    (filler : ByteArray) (path : Array PathHop) (payload : ByteArray) :
    (newKEMPacketFrom kem cipher macS streamS geom kemElements keys filler path payload).toOption
      = pktFn kem geom (keysKs geom streamS keys) (keysTag macS keys) (keysEnc cipher keys)
          kemElements filler path payload := by
  unfold newKEMPacketFrom pktFn
  dsimp only
  by_cases hp : payload.size = geom.forwardPayloadLength
  · simp only [hp, ne_eq, not_true_eq_false, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      List.forIn_pure_yield_eq_foldl, pure_bind]
    cases hc : createKEMHeaderFrom kem macS streamS geom kemElements keys filler path with
    | error e =>
      cases ht : hdrTrace kem geom (keysKs geom streamS keys) (keysTag macS keys) kemElements
          filler path path.size with
      | error _ => rfl
      | ok s =>
        rw [hdrTrace_createKEMHeaderFrom kem geom macS streamS kemElements keys filler path s ht]
          at hc
        cases hc
    | ok x =>
      obtain ⟨hdr, sprp⟩ := x
      obtain ⟨s, hs, rfl, rfl⟩ := createKEMHeaderFrom_hdrTrace kem geom macS streamS kemElements
        keys filler path hdr sprp hc
      rw [hs]
      show some _ = some _
      congr 2
      rw [Array.size_ofFn]
      refine List.foldl_ext _ _ _ fun b iRev hi => ?_
      have hlt : iRev < path.size := by simpa using hi
      simp only [keysEnc]
      rw [getElem!_pos _ _ (by simpa using (by omega : path.size - 1 - iRev < path.size))]
      simp only [Array.getElem_ofFn]
  · simp only [hp, ne_eq, not_false_eq_true, ↓reduceIte]
    rfl

end HeaderFn

end Cryptlib.Protocols.Sphinx.KEMSphinx
