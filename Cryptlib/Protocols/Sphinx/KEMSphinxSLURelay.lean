/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLUSender

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

/-! # SLU← for KEM Sphinx: the reply's next layer

With the honest relay's keys used up, world 0 of SLU← is compared with the world where the
relay sends on an onion built like a reply layer (`replySwap`). On the backward path the reply's
next layer is a first layer over the rest of the path. -/

section Uniform

/-- **The two parts of a uniform string are uniform.** -/
theorem evalDistEq_split {δ : Type} {a b n : ℕ} (hn : a + b = n)
    (K : ByteArray → ByteArray → ProbComp δ) :
    ($ᵗ (Vector UInt8 n) >>= fun u => K ((ofVector u).extract 0 a) ((ofVector u).extract a n))
      =ᵈ (do
        let x ← $ᵗ (Vector UInt8 a)
        let y ← $ᵗ (Vector UInt8 b)
        K (ofVector x) (ofVector y)) := by
  have e0 : ∀ (x : Vector UInt8 a) (y : Vector UInt8 b),
      (ofVector (padFiller hn (zeroBytes 0) x y)).extract 0 a = ofVector x
        ∧ (ofVector (padFiller hn (zeroBytes 0) x y)).extract a n = ofVector y := by
    intro x y
    rw [ofVector_padFiller, xorBytes_zeroBytes]
    constructor
    · have h1 := Util.Bytes.extract_append_left (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector] at h1
    · have h1 := Util.Bytes.extract_append_right (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector, hn] at h1
  have h := (evalDistEq_pair_of_bijective (padFiller_bijective hn (zeroBytes 0))
    (fun u : Vector UInt8 n => K ((ofVector u).extract 0 a) ((ofVector u).extract a n))).symm
  simpa only [(e0 _ _).1, (e0 _ _).2] using h

/-- **A region of a uniform string as the tail of a keystream.** A keystream whose head is a
uniform string under any mask, and whose tail is `t` bytes of another uniform string under a
fixed mask, is a uniform keystream. -/
theorem evalDistEq_headRegion {δ : Type} {n a t h m : ℕ} (hat : a + t ≤ n) (hm : h + t = m)
    (A : Vector UInt8 n → ByteArray → ByteArray) (B : ByteArray)
    (K : Vector UInt8 m → ProbComp δ) :
    (do
      let P ← $ᵗ (Vector UInt8 n)
      let U ← $ᵗ (Vector UInt8 m)
      K (Util.Bytes.toVecN m
        (xorBytes ((ofVector U).extract 0 h) (A P ((ofVector U).extract h m))
          ++ xorBytes ((ofVector P).extract a (a + t)) B)))
      =ᵈ ($ᵗ (Vector UInt8 m) >>= K) := by
  have hc : a + (n - a) = n := by omega
  have hr : t + (n - a - t) = n - a := by omega
  have e0 : ∀ (x : Vector UInt8 a) (r : Vector UInt8 (n - a)),
      (ofVector (padFiller hc (zeroBytes 0) x r)).extract a (a + t)
        = (ofVector r).extract 0 t := by
    intro x r
    rw [ofVector_padFiller, xorBytes_zeroBytes,
      Util.Bytes.extract_append_of_ge _ _ (by rw [Util.Bytes.size_ofVector]),
      Util.Bytes.size_ofVector, Nat.sub_self, Nat.add_sub_cancel_left]
  -- the head: a uniform string under any mask
  have head : ∀ (P : Vector UInt8 n) (C : ByteArray),
      ($ᵗ (Vector UInt8 m) >>= fun U => K (Util.Bytes.toVecN m
        (xorBytes ((ofVector U).extract 0 h) (A P ((ofVector U).extract h m)) ++ C)))
      =ᵈ ($ᵗ (Vector UInt8 h) >>= fun x => K (Util.Bytes.toVecN m (ofVector x ++ C))) :=
    fun P C => by
    refine EvalDistEq.trans (evalDistEq_split hm fun X Y =>
      K (Util.Bytes.toVecN m (xorBytes X (A P Y) ++ C))) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => ?_)
      (OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 t)) _)
    have h5 := evalDistEq_otp h (A P (ofVector y))
      (fun z => K (Util.Bytes.toVecN m (ofVector z ++ C)))
    simpa only [Util.Bytes.ofVector_toVecN _
      ((size_xorBytes _ _).trans (Util.Bytes.size_ofVector _))] using h5
  -- the region: `t` bytes of a uniform string are uniform
  have region : ∀ J : ByteArray → ProbComp δ,
      ($ᵗ (Vector UInt8 n) >>= fun P => J ((ofVector P).extract a (a + t)))
      =ᵈ ($ᵗ (Vector UInt8 t) >>= fun y => J (ofVector y)) := fun J => by
    refine EvalDistEq.trans (evalDistEq_pair_of_bijective
      (padFiller_bijective hc (zeroBytes 0))
      (fun P : Vector UInt8 n => J ((ofVector P).extract a (a + t)))).symm ?_
    simp only [e0]
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 a)) _) ?_
    refine EvalDistEq.trans (evalDistEq_split hr fun X _ => J X) ?_
    exact EvalDistEq.bind_right _ fun y =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 (n - a - t))) _
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun P => head P _) ?_
  refine EvalDistEq.trans (region fun T =>
    $ᵗ (Vector UInt8 h) >>= fun x => K (Util.Bytes.toVecN m (ofVector x ++ xorBytes T B))) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_pair_of_bijective (padFiller_bijective hm B) K

end Uniform

section Fresh

variable {S : Protocols.RSOR.Scheme} {L : ℕ} (ρ : Protocols.RSOR.Role) (H : S.Header)
  (key : S.Onion → Vector UInt8 L) (step : S.Onion → Vector UInt8 L → Option S.Step)
  (rep : S.Msg → S.Onion → Vector UInt8 L → Option (S.Name × S.Onion))

/-- A patch that first gives the relay `ρ`, under the header `H`, the answer it has when its
payload decrypts by `dec`. -/
def decPatch (dec : Vector UInt8 L → Vector UInt8 L) (patch : Protocols.RSOR.Patch S) :
    Protocols.RSOR.Patch S where
  proc h o out :=
    if h = ρ ∧ o.1 = H then patch.proc h o (step o (dec (key o))) else patch.proc h o out
  reply h m o out :=
    if h = ρ ∧ o.1 = H then patch.reply h m o (rep m o default) else patch.reply h m o out

/-- A patch that first gives the relay `ρ`, under the header `H`, the answer it has when its
payload decrypts to a block drawn then. -/
def drawPatch (patch : Protocols.RSOR.Patch S) : Protocols.RSOR.Patch S where
  proc h o out :=
    if h = ρ ∧ o.1 = H then $ᵗ (Vector UInt8 L) >>= fun g => patch.proc h o (step o g)
    else patch.proc h o out
  reply := (decPatch ρ H key step rep id patch).reply

variable (proc : Protocols.RSOR.Role → S.Onion → Option S.Step)
  (reply : Protocols.RSOR.Role → S.Msg → S.Onion → Option (S.Name × S.Onion))

/-- A relay that decrypts by `dec` under one header is a relay patched with `decPatch`, when
its patched reply under that header does not depend on the decrypted block. -/
theorem withDec_decPatch (dec : Vector UInt8 L → Vector UInt8 L)
    (patch : Protocols.RSOR.Patch S)
    (hrep : ∀ m o x, o.1 = H →
      patch.reply ρ m o (rep m o x) = patch.reply ρ m o (rep m o default)) :
    Protocols.RSOR.withDec ρ H key step rep proc reply dec patch
      = Protocols.RSOR.oracle (fun h o => pure (proc h o)) (fun h m o => pure (reply h m o))
        (decPatch ρ H key step rep dec patch) := by
  refine Protocols.RSOR.oracle_patch_congr patch _ _ _ _ _ (fun h o => ?_) (fun h m o => ?_)
  · by_cases hc : h = ρ ∧ o.1 = H
    · exact (congrArg (patch.proc h o) (ite_eq_left hc)).trans (ite_eq_left hc).symm
    · exact (congrArg (patch.proc h o) (ite_eq_right hc)).trans (ite_eq_right hc).symm
  · by_cases hc : h = ρ ∧ o.1 = H
    · have e : patch.reply h m o (rep m o (dec (key o)))
          = patch.reply h m o (rep m o default) := by
        obtain ⟨rfl, ho⟩ := hc
        exact hrep m o _ ho
      exact (congrArg (patch.reply h m o) (ite_eq_left hc)).trans (e.trans (ite_eq_left hc).symm)
    · exact (congrArg (patch.reply h m o) (ite_eq_right hc)).trans (ite_eq_right hc).symm

/-- **The ideal cipher's one answer under a header is a fresh block.** An honest relay
processes a header once. So a relay whose payload under one header decrypts as the ideal
cipher does after one encryption (to the block `w` for the block `u`, to the block `v` for any
other) is, with `u`, `w` and `v` uniform, a relay whose payload decrypts to one uniform
block. -/
theorem withDec_fresh (patch : Protocols.RSOR.Patch S)
    (hrep : ∀ m o x, o.1 = H →
      patch.reply ρ m o (rep m o x) = patch.reply ρ m o (rep m o default))
    {α : Type} (oa : OracleComp (Protocols.RSOR.oracleSpec S) α) (log : Protocols.RSOR.Log S) :
    (do
      let u ← $ᵗ (Vector UInt8 L)
      let w ← $ᵗ (Vector UInt8 L)
      let v ← $ᵗ (Vector UInt8 L)
      (simulateQ (Protocols.RSOR.withDec ρ H key step rep proc reply
        (fun y => if y = u then w else v) patch) oa).run log)
      =ᵈ ($ᵗ (Vector UInt8 L) >>= fun g =>
        (simulateQ (Protocols.RSOR.withDec ρ H key step rep proc reply (fun _ => g) patch)
          oa).run log) := by
  simp only [withDec_decPatch ρ H key step rep proc reply _ patch hrep]
  have h1 := Protocols.RSOR.oracle_draw ρ H
    (do
      let u ← $ᵗ (Vector UInt8 L)
      let w ← $ᵗ (Vector UInt8 L)
      let v ← $ᵗ (Vector UInt8 L)
      pure (u, w, v))
    (drawPatch ρ H key step rep patch)
    (fun x : Vector UInt8 L × Vector UInt8 L × Vector UInt8 L =>
      decPatch ρ H key step rep (fun y => if y = x.1 then x.2.1 else x.2.2) patch)
    (fun h o => pure (proc h o)) (fun h m o => pure (reply h m o))
    (fun h o out => by
      by_cases hc : h = ρ ∧ o.1 = H
      · have e : (drawPatch ρ H key step rep patch).proc h o out
            = $ᵗ (Vector UInt8 L) >>= fun g => patch.proc h o (step o g) := ite_eq_left hc
        have e2 : ∀ x : Vector UInt8 L × Vector UInt8 L × Vector UInt8 L,
            (decPatch ρ H key step rep (fun y => if y = x.1 then x.2.1 else x.2.2)
              patch).proc h o out
              = patch.proc h o (step o (if key o = x.1 then x.2.1 else x.2.2)) :=
          fun x => ite_eq_left hc
        rw [e]
        simp only [e2, bind_assoc, pure_bind]
        exact (evalDistEq_ite_fresh (key o) fun g => patch.proc h o (step o g)).symm
      · have e : (drawPatch ρ H key step rep patch).proc h o out = patch.proc h o out :=
          ite_eq_right hc
        have e2 : ∀ x : Vector UInt8 L × Vector UInt8 L × Vector UInt8 L,
            (decPatch ρ H key step rep (fun y => if y = x.1 then x.2.1 else x.2.2)
              patch).proc h o out = patch.proc h o out := fun x => ite_eq_right hc
        rw [e]
        simp only [e2]
        exact (OracleComp.EvalDistEq.bind_const _ _).symm)
    (fun g g' h o out hc => (ite_eq_right hc).trans (ite_eq_right hc).symm) (fun g => rfl) oa log
  have h2 := Protocols.RSOR.oracle_draw ρ H ($ᵗ (Vector UInt8 L))
    (drawPatch ρ H key step rep patch)
    (fun g : Vector UInt8 L => decPatch ρ H key step rep (fun _ => g) patch)
    (fun h o => pure (proc h o)) (fun h m o => pure (reply h m o))
    (fun h o out => by
      by_cases hc : h = ρ ∧ o.1 = H
      · have e : (drawPatch ρ H key step rep patch).proc h o out
            = $ᵗ (Vector UInt8 L) >>= fun g => patch.proc h o (step o g) := ite_eq_left hc
        have e2 : ∀ g : Vector UInt8 L,
            (decPatch ρ H key step rep (fun _ => g) patch).proc h o out
              = patch.proc h o (step o g) := fun g => ite_eq_left hc
        rw [e]
        simp only [e2]
        exact EvalDistEq.rfl
      · have e : (drawPatch ρ H key step rep patch).proc h o out = patch.proc h o out :=
          ite_eq_right hc
        have e2 : ∀ g : Vector UInt8 L,
            (decPatch ρ H key step rep (fun _ => g) patch).proc h o out
              = patch.proc h o out := fun g => ite_eq_right hc
        rw [e]
        simp only [e2]
        exact (OracleComp.EvalDistEq.bind_const _ _).symm)
    (fun g g' h o out hc => (ite_eq_right hc).trans (ite_eq_right hc).symm) (fun g => rfl) oa log
  simp only [bind_assoc, pure_bind] at h1
  exact h1.symm.trans h2

end Fresh

section Parts

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- **A packet is a header and a payload block, and only the block uses the payload cipher.**
A packet that can be built with one cipher can be built with any, with the same header. With
the cipher that changes nothing, the block is the zero tag and the payload. -/
theorem newKEMPacket_parts (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload x : ByteArray)
    (h : newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload = .ok x) :
    ∃ hdr : ByteArray, hdr.size = geom.headerLength
      ∧ (∀ c : WideBlockCipher, ∃ b : ByteArray,
        b.size = geom.payloadTagLength + geom.forwardPayloadLength
        ∧ newKEMPacket kem c macS kdfS streamS geom seeds filler path payload = .ok (hdr ++ b))
      ∧ newKEMPacket kem default macS kdfS streamS geom seeds filler path payload
        = .ok (hdr ++ ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)) := by
  obtain ⟨-, -, -, -, hpacket, -⟩ := id hvalid
  by_cases hp : payload.size = geom.forwardPayloadLength
  · have hx := newKEMPacket_size kem cipher macS kdfS streamS geom seeds filler path payload x
      hvalid hmactag h hp
    unfold newKEMPacket at h ⊢
    simp only [hp, ne_eq, not_true_eq_false, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      List.forIn_pure_yield_eq_foldl, pure_bind] at h ⊢
    cases hc : createKEMHeader kem macS kdfS streamS geom seeds filler path with
    | error e =>
      rw [hc] at h
      cases h
    | ok s =>
      rw [hc] at h
      have hsz : ∀ (c : WideBlockCipher) (l : List ℕ) (b : ByteArray),
          (l.foldl (fun b a => c.encrypt s.2[s.2.size - 1 - a]!.key.toArray
            (ofVector s.2[s.2.size - 1 - a]!.iv) b) b).size = b.size := by
        intro c l
        induction l with
        | nil => intro b; rfl
        | cons a l ih => intro b; rw [List.foldl_cons, ih, c.encrypt_size]
      have hid : ∀ (l : List ℕ) (b : ByteArray),
          l.foldl (fun b a => (default : WideBlockCipher).encrypt
            s.2[s.2.size - 1 - a]!.key.toArray (ofVector s.2[s.2.size - 1 - a]!.iv) b) b = b := by
        intro l
        induction l with
        | nil => intro b; rfl
        | cons a l ih => intro b; rw [List.foldl_cons, ih]; rfl
      have hinit : ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload).size
          = geom.payloadTagLength + geom.forwardPayloadLength := by
        rw [ByteArray.size_append, hp]
        exact congrArg (· + geom.forwardPayloadLength) Array.size_replicate
      obtain rfl : s.1 ++ List.foldl (fun b a => cipher.encrypt s.2[s.2.size - 1 - a]!.key.toArray
          (ofVector s.2[s.2.size - 1 - a]!.iv) b)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)
          (List.range' 0 s.2.size) = x := Except.ok.inj h
      rw [ByteArray.size_append, hsz, hinit] at hx
      exact ⟨s.1, by omega, fun c => ⟨_, (hsz c _ _).trans hinit, rfl⟩,
        congrArg (fun b => Except.ok (s.1 ++ b)) (hid _ _)⟩
  · exfalso
    unfold newKEMPacket at h
    simp only [hp, ne_eq, not_false_eq_true, ↓reduceIte] at h
    cases h

/-- **A packet's header is the same with any payload cipher**, and a packet that cannot be
built with one cipher cannot be built with another. -/
theorem newKEMPacket_header (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (c c' : WideBlockCipher) (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload : ByteArray) :
    (match newKEMPacket kem c macS kdfS streamS geom seeds filler path payload with
      | .ok p => (RSOR.split geom p).1
      | .error _ => (default : RSOR.Onion geom).1)
      = (match newKEMPacket kem c' macS kdfS streamS geom seeds filler path payload with
        | .ok p => (RSOR.split geom p).1
        | .error _ => (default : RSOR.Onion geom).1) := by
  cases h : newKEMPacket kem c macS kdfS streamS geom seeds filler path payload with
  | ok x =>
    obtain ⟨hdr, hs, hall, -⟩ := newKEMPacket_parts kem c macS kdfS streamS geom hvalid hmactag
      seeds filler path payload x h
    obtain ⟨b, -, e⟩ := hall c
    obtain ⟨b', -, e'⟩ := hall c'
    rw [h] at e
    obtain rfl := Except.ok.inj e
    rw [e']
    unfold RSOR.split
    dsimp only
    rw [Util.Bytes.extract_append_of_le _ _ (le_of_eq hs.symm),
      Util.Bytes.extract_append_of_le _ _ (le_of_eq hs.symm)]
  | error e =>
    cases h' : newKEMPacket kem c' macS kdfS streamS geom seeds filler path payload with
    | error e' => rfl
    | ok x' =>
      obtain ⟨hdr, -, hall, -⟩ := newKEMPacket_parts kem c' macS kdfS streamS geom hvalid hmactag
        seeds filler path payload x' h'
      obtain ⟨b, -, e2⟩ := hall c
      rw [h] at e2
      cases e2

/-- A packet that can be built with the cipher that changes nothing can be built with any
cipher, with the same header. -/
theorem newKEMPacket_ok_header (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength) (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload x : ByteArray)
    (h : newKEMPacket kem default macS kdfS streamS geom seeds filler path payload = .ok x) :
    ∃ p, newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload = .ok p
      ∧ (RSOR.split geom p).1 = Util.Bytes.toVecN _ (x.extract 0 geom.headerLength) := by
  obtain ⟨hdr, hs, hall, -⟩ := newKEMPacket_parts kem default macS kdfS streamS geom hvalid
    hmactag seeds filler path payload x h
  obtain ⟨b, -, e⟩ := hall cipher
  obtain ⟨b', -, e'⟩ := hall default
  rw [h] at e'
  obtain rfl := Except.ok.inj e'
  refine ⟨_, e, ?_⟩
  unfold RSOR.split
  dsimp only
  rw [Util.Bytes.extract_append_of_le _ _ (le_of_eq hs.symm),
    Util.Bytes.extract_append_of_le _ _ (le_of_eq hs.symm)]
  rfl

/-- **Behind the tag of a hop in the middle of a path, with the cipher that changes nothing,
is the zero tag and the payload.** -/
theorem relayBack_default (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (U fwd : ByteArray)
    (hfwd : layerPast kem default macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd) :
    relayBack kem default macS kdfS streamS geom hops d payload j U id
      = (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  unfold relayBack
  rw [hfwd]
  unfold layerPast at hfwd
  obtain ⟨hdr, hs, -, hd⟩ := newKEMPacket_parts kem default macS kdfS streamS geom hvalid hmactag
    _ _ _ _ _ hfwd
  rw [hfwd] at hd
  obtain rfl := Except.ok.inj hd
  have ho : payloadOffset kem geom = hdr.size := by
    rw [hs, hhdr, had]
  show (hdr ++ _).extract (payloadOffset kem geom) (hdr ++ _).size = _
  rw [ho, ByteArray.size_append]
  exact Util.Bytes.extract_append_right hdr _

end Parts

section RestOfPath

variable (kem : KEM) (geom : Geometry)

/-- The hops of a route from position `j` on are the hops of the rest of the route. -/
theorem path_extract_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (j : ℕ) (hj : j ≤ R.hops.length) :
    (RSOR.path kem R last).extract j (RSOR.path kem R last).size
      = RSOR.path kem (R.drop j) last := by
  apply Array.ext
  · simp [RSOR.path_size, Protocols.RSOR.Route.drop]
  · intro i h1 h2
    have hi : j + i < R.hops.length := by
      simp [RSOR.path_size] at h1
      omega
    simp only [RSOR.path, Protocols.RSOR.Route.drop, Array.getElem_extract,
      List.getElem_toArray, List.getElem_mapIdx, List.getElem_drop, List.length_drop]
    congr 1
    have e : (j + i + 1 = R.hops.length) = (i + 1 = R.hops.length - j) := by
      apply propext
      omega
    simp only [e]

variable (kdfS : KDF) (streamS : StreamCipher)

/-- **Past the keyed hop the fillers are those of the rest of the path.** If the keyed filler
of the layer after the keyed hop is the filler `filler'`, then the keyed fillers of the layers
from there on are the fillers built on the rest of the path from `filler'`. -/
theorem fillerAtF_drop (hops : Array PathHop) (seeds : Array (Vector UInt8 32))
    (filler filler' : ByteArray) (j : ℕ) (U : ByteArray) (hsz : seeds.size = hops.size)
    (h0 : fillerAtF kem kdfS streamS geom hops seeds filler j U (j + 1) = filler') (i : ℕ)
    (hi : j + 1 + i ≤ hops.size) :
    fillerAtF kem kdfS streamS geom hops seeds filler j U (j + 1 + i)
      = RSOR.fillerAt kem kdfS streamS geom (hops.extract (j + 1) hops.size)
        (seeds.extract (j + 1) seeds.size) filler' i := by
  induction i with
  | zero => exact h0
  | succ i ih =>
    show fillerAtF kem kdfS streamS geom hops seeds filler j U (j + 1 + i + 1) = _
    simp only [fillerAtF, RSOR.fillerAt]
    rw [ih (by omega)]
    unfold tailFillerOf tailFiller
    rw [show ((hops.extract (j + 1) hops.size).extract i (hops.extract (j + 1) hops.size).size).size
      = hops.size - (j + 1 + i) by simp; omega]
    congr 1
    rw [← tailPadOf_kemHopKeys kem kdfS streamS geom]
    apply tailPadOf_congr
    intro m hm
    have hlt : j + 1 + i + m < hops.size := by omega
    have hne : ¬ j + 1 + i + m = j := by omega
    show (if j + 1 + i + m = j then _ else _) = _
    rw [ite_eq_right hne]
    congr 1
    unfold kemHopKeys
    rw [getElem!_extract_from _ i m (by simp; omega),
      getElem!_extract_from _ (j + 1) (i + m) (by omega),
      getElem!_extract_from _ i m (by simp; omega),
      getElem!_extract_from _ (j + 1) (i + m) (by omega),
      show j + 1 + (i + m) = j + 1 + i + m by omega]

/-- **The tail of the keyed hop's keystream sets the next layer's filler.** The keyed filler
of the layer after the keyed hop is the sender's filler and then any `j + 1` blocks `T`, for
the keystream whose tail is `T` under the filler at a zero keystream. The head of the keystream
is not read. -/
theorem fillerAtF_target (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength *
    geom.nrHops)
    (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (j : ℕ)
    (H T : ByteArray) (hH : H.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j +
        1) * geom.perHopRoutingInfoLength) (hT : T.size = (j + 1) * geom.perHopRoutingInfoLength)
    (hlen : hops.size ≤ geom.nrHops) (hj : j + 1 < hops.size)
    (hf : filler.size = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) :
    fillerAtF kem kdfS streamS geom hops seeds filler j
        (H ++ xorBytes T ((fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).extract filler.size
            (filler.size + (j + 1) * geom.perHopRoutingInfoLength))) (j + 1)
      = filler ++ T := by
  have hm : (j + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := by
    have h1 : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.nrHops * geom.perHopRoutingInfoLength
        := Nat.mul_le_mul_right _ (by omega)
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    omega
  have hZsz : (fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).size = filler.size + (j +
      1) * geom.perHopRoutingInfoLength := by
    rw [fillerAtF_size kem kdfS streamS geom hrouting hops seeds filler j _ hlen hf
      (zeroBytes_size _) (j + 1) hj, hf, Nat.add_mul]
  have hZ : (fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes (geom.routingInfoLength
      + geom.perHopRoutingInfoLength)) (j + 1)) = filler ++ (fillerAtF kem kdfS streamS geom hops
      seeds filler j (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j +
      1)).extract filler.size (filler.size + (j + 1) * geom.perHopRoutingInfoLength) := by
    have h := Util.Bytes.append_extract (fillerAtF kem kdfS streamS geom hops seeds filler j
        (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)) filler.size
        (by rw [hZsz]; omega)
    rw [fillerAtF_head geom kem kdfS streamS hrouting hops seeds filler j _ (zeroBytes_size _)
      hlen hf (j + 1) (by omega), hZsz] at h
    exact h.symm
  obtain ⟨Zt, hZt⟩ : ∃ Zt, Zt
      = (fillerAtF kem kdfS streamS geom hops seeds filler j (zeroBytes (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)) (j + 1)).extract filler.size (filler.size + (j + 1) *
          geom.perHopRoutingInfoLength) := ⟨_, rfl⟩
  have hZts : Zt.size = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [hZt, ByteArray.size_extract, hZsz]
    omega
  rw [← hZt] at hZ ⊢
  have hV : (H ++ xorBytes T Zt).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
      by
    rw [ByteArray.size_append, size_xorBytes, hH, hT]
    omega
  rw [fillerAtF_affine geom kem kdfS streamS hrouting hops seeds filler j _ hV hlen (by omega)
      hf (j + 1) le_rfl, Nat.sub_self, Nat.zero_mul, Nat.sub_zero,
    Util.Bytes.extract_append_of_ge _ _ (by rw [hH]), hH, Nat.sub_self,
    show (geom.routingInfoLength + geom.perHopRoutingInfoLength) - ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) = (j + 1) *
        geom.perHopRoutingInfoLength by omega,
    extract_all _ _ (by rw [size_xorBytes, hT]), hZ,
    xorBytes_append filler Zt _ _ (by rw [zeroBytes_size, hf]),
    xorBytes_zeroBytes, xorBytes_comm_of_size_eq Zt (xorBytes T Zt)
      (by rw [size_xorBytes, hZts, hT]), xorBytes_xorBytes]

omit kem geom kdfS streamS in
/-- Taking a tail of a tail of an array is taking one tail. -/
theorem extract_tail_tail {α : Type} (a : Array α) (j i : ℕ) :
    a.extract (j + i) a.size = (a.extract j a.size).extract i (a.extract j a.size).size := by
  apply Array.ext
  · simp
    omega
  · intro k h1 h2
    simp [Nat.add_assoc]

variable (cipher : WideBlockCipher) (macS : MAC)

/-- **A layer past the keyed hop is a layer over the rest of the path**, when the seeds after
the keyed hop are the rest's seeds and the keyed filler of the layer after the keyed hop is the
rest's padding. -/
theorem layerPast_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (d d' : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (U : ByteArray)
    (hseeds : (d.1.toArray.extract 0 (RSOR.path kem R last).size).extract (j + 1)
        (d.1.toArray.extract 0 (RSOR.path kem R last).size).size
      = d'.1.toArray.extract 0 (RSOR.path kem (R.drop (j + 1)) last).size)
    (hfill : fillerAtF kem kdfS streamS geom (RSOR.path kem R last) (d.1.toArray.extract 0
        (RSOR.path kem R last).size)
        ((ofVector d.2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength))
        j U (j + 1)
      = (ofVector d'.2).extract 0
        ((geom.nrHops - (RSOR.path kem (R.drop (j + 1)) last).size) * geom.perHopRoutingInfoLength))
    (i : ℕ) (hi : j + 1 + i ≤ R.hops.length) :
    layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload j U (j + 1 + i)
      = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) d'
          payload i := by
  have hle := R.length_le
  have hsz : (d.1.toArray.extract 0 (RSOR.path kem R last).size).size = (RSOR.path kem R last).size
      := by
    rw [RSOR.path_size]
    simp
    omega
  unfold layerPast RSOR.layer
  dsimp only
  rw [fillerAtF_drop kem geom kdfS streamS _ _ _ _ j U hsz hfill i
      (by rw [RSOR.path_size]; exact hi),
    extract_tail_tail (d.1.toArray.extract 0 (RSOR.path kem R last).size) (j + 1) i,
    extract_tail_tail (RSOR.path kem R last) (j + 1) i, hseeds,
    path_extract_drop kem geom R last (j + 1) (by omega)]

set_option maxHeartbeats 2000000 in
/-- **A middle hop's header under a shifted keystream.** Two paths of one length, each with a
draw, give the keyed hop two headers. With the head of the keystream shifted by the difference
of the two routing informations, the first gives the second's header bytes, and still its own
next layer. -/
theorem relayFront_headShift (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops hops' : Array PathHop) (d d' : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U U' fwd fwd' : ByteArray) (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hsz : hops'.size = hops.size)
    (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hU' : U'.size =
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hc : c.size = kem.ciphertextSize)
    (hcmd : (hops[j]!).commands = []) (hcmd' : (hops'[j]!).commands = [])
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd)
    (hfwd' : layerPast kem cipher macS kdfS streamS geom hops' d' payload j U' (j + 1) = .ok fwd')
    (htail : (midPad geom kem kdfS streamS hops d j).extract ((geom.nrHops - hops.size) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) +
        j * geom.perHopRoutingInfoLength)
      = (midPad geom kem kdfS streamS hops' d' j).extract ((geom.nrHops - hops'.size) *
          geom.perHopRoutingInfoLength) (((geom.nrHops - hops'.size) *
          geom.perHopRoutingInfoLength) + j * geom.perHopRoutingInfoLength)) :
    (xorBytes (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)))
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size = (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)
    ∧ layerPast kem cipher macS kdfS streamS geom hops d payload j
      (xorBytes (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)))
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1) = .ok fwd
    ∧ relayFront kem cipher macS kdfS streamS geom hops d payload j c
      (xorBytes (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)))
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))
      = relayFront kem cipher macS kdfS streamS geom hops' d' payload j c U' := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hj' : j + 1 < hops'.size := lt_of_lt_of_eq hj hsz.symm
  have hlen' : hops'.size ≤ geom.nrHops := le_of_eq_of_le hsz hlen
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at hjp
  have hUh : (U'.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)).size =
      (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_extract, hU']
    omega
  obtain ⟨X0, hX0⟩ : ∃ X0, X0 = (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)) := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X1, X1 = (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d' j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength)) := ⟨_, rfl⟩
  rw [← hX0, ← hX1]
  obtain ⟨V, hV⟩ : ∃ V, V = xorBytes (U'.extract 0 (geom.routingInfoLength - j *
      geom.perHopRoutingInfoLength)) (xorBytes X1 X0)
      ++ U.extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength) := ⟨_, rfl⟩
  rw [← hV]
  have hVs : V.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := by
    rw [hV, ByteArray.size_append, size_xorBytes, hUh, ByteArray.size_extract, hU]
    omega
  have hVt : U.extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      = V.extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
          geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
          by
    rw [show (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength = (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
        by rw [Nat.succ_mul]; omega, hV,
      Util.Bytes.extract_append_of_ge _ _ (by rw [size_xorBytes, hUh]), size_xorBytes, hUh,
      Nat.sub_self, show (geom.routingInfoLength + geom.perHopRoutingInfoLength) -
          (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) = (U.extract
          (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)).size by
        rw [ByteArray.size_extract, hU]; omega]
    exact (extract_all _ _ rfl).symm
  have hfV : layerPast kem cipher macS kdfS streamS geom hops d payload j V (j + 1) = .ok fwd :=
    (layerPast_tail geom kem kdfS streamS cipher macS hrouting hops d payload j U V hU hVs hlen
      hj hVt).symm.trans hfwd
  refine ⟨hVs, hfV, ?_⟩
  have hs := relayFront_size geom kem kdfS streamS cipher macS hvalid hmactag hops d payload j c
    V fwd hj hlen hc hfV hcmd
  have hs' := relayFront_size geom kem kdfS streamS cipher macS hvalid hmactag hops' d' payload
    j c U' fwd' hj' hlen' hc hfwd' hcmd'
  have h0 := relayFront_canon geom kem kdfS streamS cipher macS hvalid hmactag hops d payload j
    c V fwd hj hlen hVs hc hfV hs
  have h1 := relayFront_canon geom kem kdfS streamS cipher macS hvalid hmactag hops' d' payload
    j c U' fwd' hj' hlen' hU' hc hfwd' hs'
  rw [← hX0] at h0
  rw [← hX1] at h1
  have hv0 : v0AD.size = 2 := rfl
  have hXs : ∀ (X T W : ByteArray), (v0AD ++ c ++ xorBytes X W ++ T).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength → T.size = j * geom.perHopRoutingInfoLength
          →
      X.size = (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) := fun X T W h hT => by
    simp only [ByteArray.size_append, size_xorBytes, hc, hv0, hT] at h
    omega
  have hTs : ∀ (hp : Array PathHop) (dd : RSOR.Draw geom), hp.size ≤ geom.nrHops →
      j + 1 < hp.size →
      ((midPad geom kem kdfS streamS hp dd j).extract ((geom.nrHops - hp.size) *
          geom.perHopRoutingInfoLength)
        ((geom.nrHops - hp.size) * geom.perHopRoutingInfoLength + j *
            geom.perHopRoutingInfoLength)).size = j * geom.perHopRoutingInfoLength :=
    fun hp dd hl hjj => by
    have hap : (geom.nrHops - hp.size) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    unfold midPad
    rw [ByteArray.size_extract, size_xorBytes,
      fillerAtF_size kem kdfS streamS geom hrouting hp _ _ j _ hl (by
        rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
        omega) (zeroBytes_size _) (j + 1) hjj, Nat.add_mul, Nat.succ_mul]
    omega
  have hX0s := hXs X0 _ _ (h0 ▸ hs) (hTs hops d hlen hj)
  have hX1s := hXs X1 _ _ (h1 ▸ hs') (hTs hops' d' hlen' hj')
  rw [h0, h1, htail, hV, Util.Bytes.extract_append_of_le _ _ (by rw [size_xorBytes, hUh]),
    extract_all _ _ (by rw [size_xorBytes, hUh]),
    xorBytes_shift X0 X1 _ (hX0s.trans hX1s.symm) (hUh.trans hX0s.symm)]

/-- A draw whose seeds after position `j` and whose first `a` bytes of padding are another
draw's. -/
def joinDraw (d d' : RSOR.Draw geom) (j a : ℕ) : RSOR.Draw geom :=
  (Vector.ofFn fun i : Fin geom.nrHops =>
    if i.val ≤ j then d.1[i.val]'i.isLt else d'.1[i.val - (j + 1)]'(by have := i.isLt; omega),
    Vector.ofFn fun i : Fin geom.routingInfoLength =>
      if i.val < a then d'.2[i.val]'i.isLt else d.2[i.val]'i.isLt)

omit kem kdfS streamS cipher macS in
/-- The first `a` bytes of a joined draw's padding are the other draw's. -/
theorem joinDraw_prefix (d d' : RSOR.Draw geom) (j a : ℕ) :
    (ofVector (joinDraw geom d d' j a).2).extract 0 a = (ofVector d'.2).extract 0 a := by
  apply ByteArray.ext_getElem
  · simp [ByteArray.size_extract]
  · intro i h1 h2
    have hi : i < a := by
      simp [ByteArray.size_extract] at h1
      omega
    simp [ofVector, ByteArray.getElem_eq_getElem_data, joinDraw, hi]

omit kem kdfS streamS cipher macS in
/-- The seeds of a joined draw after position `j` are the other draw's first seeds. -/
theorem joinDraw_extract_after (d d' : RSOR.Draw geom) (j a n : ℕ) (hn : n ≤ geom.nrHops) :
    ((joinDraw geom d d' j a).1.toArray.extract 0 n).extract (j + 1)
        ((joinDraw geom d d' j a).1.toArray.extract 0 n).size
      = d'.1.toArray.extract 0 (n - (j + 1)) := by
  apply Array.ext
  · simp
    omega
  · intro i h1 h2
    have hi : j + 1 + i < n := by
      simp at h1
      omega
    simp [joinDraw, show ¬ (j + 1 + i ≤ j) by omega]

/-- What joining two draws leaves over: the first draw's seeds after position `j`, moved to
the front of the second draw's, and the second draw's padding with the first `a` bytes of the
first's. -/
def coJoin (d d' : RSOR.Draw geom) (j a : ℕ) : RSOR.Draw geom :=
  (Vector.ofFn fun i : Fin geom.nrHops =>
    if h : i.val + (j + 1) < geom.nrHops then d.1[i.val + (j + 1)]'h else d'.1[i.val]'i.isLt,
    Vector.ofFn fun i : Fin geom.routingInfoLength =>
      if i.val < a then d.2[i.val]'i.isLt else d'.2[i.val]'i.isLt)

omit kem kdfS streamS cipher macS in
/-- Joining twice gives the first draw back. -/
theorem joinDraw_joinDraw (d d' : RSOR.Draw geom) (j a : ℕ) :
    joinDraw geom (joinDraw geom d d' j a) (coJoin geom d d' j a) j a = d := by
  obtain ⟨s, f⟩ := d
  obtain ⟨s', f'⟩ := d'
  unfold joinDraw coJoin
  refine Prod.ext (Vector.ext fun i hi => ?_) (Vector.ext fun i hi => ?_)
  · by_cases h : i ≤ j
    · simp [h]
    · have h2 : i - (j + 1) + (j + 1) = i := by omega
      simp [h, h2, hi]
  · by_cases h : i < a <;> simp [h]

omit kem kdfS streamS cipher macS in
/-- Joining twice gives the second draw back. -/
theorem coJoin_coJoin (d d' : RSOR.Draw geom) (j a : ℕ) :
    coJoin geom (joinDraw geom d d' j a) (coJoin geom d d' j a) j a = d' := by
  obtain ⟨s, f⟩ := d
  obtain ⟨s', f'⟩ := d'
  unfold joinDraw coJoin
  refine Prod.ext (Vector.ext fun i hi => ?_) (Vector.ext fun i hi => ?_)
  · by_cases h : i + (j + 1) < geom.nrHops
    · simp [h, show ¬ (i + (j + 1) ≤ j) by omega]
    · simp [h]
  · by_cases h : i < a <;> simp [h]

omit kem kdfS streamS cipher macS in
/-- Past its first `a` bytes, the leftover's padding is the second draw's. -/
theorem coJoin_region (d d' : RSOR.Draw geom) (j a t : ℕ) :
    (ofVector (coJoin geom d d' j a).2).extract a (a + t) = (ofVector d'.2).extract a (a + t) := by
  apply ByteArray.ext_getElem
  · simp [ByteArray.size_extract]
  · intro i h1 h2
    simp [ofVector, ByteArray.getElem_eq_getElem_data, coJoin]

/-- World 0's randomness, from the randomness of the world where the relay sends on a reply
layer over the rest of the backward path and the randomness of that layer. -/
def backMix (r r' : RSOR.Randomness geom) (j a : ℕ) : RSOR.Randomness geom :=
  (r.1, joinDraw geom r.2.1 r'.1 j a, r.2.2.1, r'.2.2.2)

/-- What `backMix` leaves over. -/
def backCo (r r' : RSOR.Randomness geom) (j a : ℕ) : RSOR.Randomness geom :=
  (coJoin geom r.2.1 r'.1 j a, r'.2.1, r'.2.2.1, r.2.2.2)

omit kem kdfS streamS cipher macS in
/-- **The mixed randomness is uniform.** A game that reads two uniform draws through `backMix`
and `backCo` reads two uniform draws. -/
theorem evalDistEq_backMix {δ : Type} (j a : ℕ)
    (K : RSOR.Randomness geom → RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let r' ← $ᵗ (RSOR.Randomness geom)
      K (backMix geom r r' j a) (backCo geom r r' j a))
      =ᵈ (do
        let r ← $ᵗ (RSOR.Randomness geom)
        let r' ← $ᵗ (RSOR.Randomness geom)
        K r r') := by
  have hb : Function.Bijective (Function.uncurry fun (r r' : RSOR.Randomness geom) =>
      (backMix geom r r' j a, backCo geom r r' j a)) :=
    Function.Involutive.bijective fun p => by
      obtain ⟨r, r'⟩ := p
      simp only [Function.uncurry, backMix, backCo, joinDraw_joinDraw, coJoin_coJoin]
  have hid : Function.Bijective (Function.uncurry fun (x y : RSOR.Randomness geom) => (x, y)) :=
    Function.bijective_id
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hb fun p => K p.1 p.2) ?_
  exact (evalDistEq_pair_of_bijective hid fun p => K p.1 p.2).symm

omit streamS cipher macS in
/-- The keys of the hops up to position `j` under a joined draw are the first draw's, whatever
the last hop's commands. -/
theorem kemHopKeys_joinDraw (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last last' : List RoutingCommand) (d d' : RSOR.Draw geom) (j a m : ℕ) (hm : m ≤ j)
    (hj : j < R.hops.length) :
    kemHopKeys kem kdfS (RSOR.path kem R last)
        ((joinDraw geom d d' j a).1.toArray.extract 0 (RSOR.path kem R last).size) m
      = kemHopKeys kem kdfS (RSOR.path kem R last') (d.1.toArray.extract 0 (RSOR.path kem R
          last').size) m := by
  have hle := R.length_le
  unfold kemHopKeys
  rw [RSOR.path_getElem! kem R last m (by omega), RSOR.path_getElem! kem R last' m (by omega),
    RSOR.path_size, RSOR.path_size, getElem!_pos _ _ (by simp; omega),
    getElem!_pos _ _ (by simp; omega)]
  simp [joinDraw, hm]

/-- The keystream that makes a hop in the middle of one path, under a joined draw, give the
header bytes it has on a second path of the same length under the first draw, and the layers
of the rest of the path under the second draw. Its head is the second path's keystream shifted
by the difference of the two routing informations; its tail sets the next layer's filler to
the second draw's padding. -/
def backShift (hops hops' : Array PathHop) (d0 d dS : RSOR.Draw geom) (j : ℕ)
    (U fwd fwd' : ByteArray) : ByteArray :=
  (xorBytes (U.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem hops' j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops'.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops' d j).extract 0 ((geom.nrHops - hops'.size) *
            geom.perHopRoutingInfoLength))
        (midFrag geom kem hops j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (hops.size - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS hops d0 j).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength))))
    ++ (xorBytes ((ofVector dS.2).extract ((geom.nrHops - hops.size) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength) +
        (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom hops (d0.1.toArray.extract 0 hops.size)
        ((ofVector d0.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)) j
            (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector d0.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)).size
            (((ofVector d0.2).extract 0 ((geom.nrHops - hops.size) *
            geom.perHopRoutingInfoLength)).size + (j + 1) * geom.perHopRoutingInfoLength)))

set_option maxHeartbeats 2000000 in
/-- **The backward path at the honest relay, relabelled.** On a path with the joined draw and
the shifted keystream, the keyed hop has the header bytes it has with the first draw and the
keystream `U`, whatever the two last commands, and the layers after it are the layers over the
rest of the path with the second draw. -/
theorem backShift_spec (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (last last' : List RoutingCommand)
    (d dS : RSOR.Draw geom) (payload : ByteArray) (j a : ℕ) (c U fwd fwd' : ByteArray)
    (ha : a = ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength))
    (hj : j + 1 < R.hops.length) (hU : U.size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) (hc : c.size = kem.ciphertextSize)
    (hfwd' : layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last') d payload j U (j +
        1) = .ok fwd')
    (hfwd : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) dS
        payload 0 = .ok fwd) :
    (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw geom
        d dS j a) d dS j U fwd fwd').size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)
    ∧ relayFront kem cipher macS kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j a)
        payload j c
        (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw
            geom d dS j a) d dS j U fwd fwd')
      = relayFront kem cipher macS kdfS streamS geom (RSOR.path kem R last') d payload j c U
    ∧ ∀ i, j + 1 + i ≤ R.hops.length →
      layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R last) (joinDraw geom d dS j a)
          payload j
          (backShift kem geom kdfS streamS (RSOR.path kem R last) (RSOR.path kem R last') (joinDraw
              geom d dS j a) d dS j U fwd fwd') (j + 1 + i)
        = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) last) dS
            payload i := by
  subst ha
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hsz0 : (RSOR.path kem R last).size = R.hops.length := RSOR.path_size kem R last
  have hsz1 : (RSOR.path kem R last').size = R.hops.length := RSOR.path_size kem R last'
  have hszS : (RSOR.path kem (R.drop (j + 1)) last).size = R.hops.length - (j + 1) := by
    rw [RSOR.path_size]
    simp [Protocols.RSOR.Route.drop]
  have hj0 : j + 1 < (RSOR.path kem R last).size := lt_of_lt_of_eq hj hsz0.symm
  have hlen0 : (RSOR.path kem R last).size ≤ geom.nrHops := le_of_eq_of_le hsz0 hle
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hpad : ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + (j +
      1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [← Nat.add_mul, hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hpadS : ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + (j +
      1) * geom.perHopRoutingInfoLength = ((geom.nrHops - (RSOR.path kem (R.drop (j + 1))
      last).size) * geom.perHopRoutingInfoLength) := by
    rw [← Nat.add_mul, hszS]
    congr 1
    omega
  have hf : ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength)).size = ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hT : ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength)).size
      = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hseeds := joinDraw_extract_after geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (RSOR.path kem R last).size hlen0
  rw [show (RSOR.path kem R last).size - (j + 1) = (RSOR.path kem (R.drop (j + 1)) last).size by rw
      [hszS, hsz0]] at hseeds
  have hfill : ∀ H : ByteArray, H.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) -
      (j + 1) * geom.perHopRoutingInfoLength →
      fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops -
          (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j
        (H ++ (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))) (j + 1)
      = (ofVector dS.2).extract 0 ((geom.nrHops - (RSOR.path kem (R.drop (j + 1)) last).size) *
          geom.perHopRoutingInfoLength) := fun H hH => by
    rw [fillerAtF_target kem geom kdfS streamS hrouting _ _ _ j H _ hH hT hlen0 hj0 hf,
      joinDraw_prefix, ← hpadS]
    exact extract_adjacent _ 0 _ _ (Nat.zero_le _) (Nat.le_add_right _ _)
      (by rw [Util.Bytes.size_ofVector]; exact hpad)
  have hdrop := fun (H : ByteArray) (hH : H.size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) =>
    layerPast_drop kem geom kdfS streamS cipher macS R last (joinDraw geom d dS j ((geom.nrHops -
        (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) dS payload j
      (H ++ (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))) hseeds (hfill H hH)
  have hZ : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)).size =
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength := by
    rw [zeroBytes_size, Nat.succ_mul]
    rw [Nat.succ_mul] at hjp
    omega
  have hTs : (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength))).size = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [size_xorBytes, hT]
  have hU1 : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes
      ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))).size = (geom.routingInfoLength +
            geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_append, hZ, hTs]
    omega
  have hcmd : ∀ l : List RoutingCommand, ((RSOR.path kem R l)[j]!).commands = [] := fun l => by
    rw [RSOR.path_getElem! kem R l j (by omega), ite_eq_right (by omega)]
  have htail : (midPad geom kem kdfS streamS (RSOR.path kem R last) (joinDraw geom d dS j
      ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j).extract
      ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)
        (((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + j *
            geom.perHopRoutingInfoLength)
      = (midPad geom kem kdfS streamS (RSOR.path kem R last') d j).extract ((geom.nrHops -
          (RSOR.path kem R last').size) * geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path
          kem R last').size) * geom.perHopRoutingInfoLength) + j * geom.perHopRoutingInfoLength) :=
          by
    rw [midPad_front geom kem kdfS streamS hvalid _ _ j hj0 hlen0 j le_rfl,
      midPad_front geom kem kdfS streamS hvalid _ _ j (lt_of_lt_of_eq hj hsz1.symm)
        (le_of_eq_of_le hsz1 hle) j le_rfl]
    exact frontPadOf_congr geom kem kdfS streamS _ _ _ _ j
      (fun m hm => kemHopKeys_joinDraw kem geom kdfS R last last' d dS j _ m (by omega)
        (by omega))
      j le_rfl
  have hs := relayFront_headShift kem geom kdfS streamS cipher macS hvalid hmactag (RSOR.path kem R
      last)
    (RSOR.path kem R last') (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
        geom.perHopRoutingInfoLength)) d payload j c
    (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes ((ofVector
        dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)
        (((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength) + (j + 1) *
        geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))) U fwd fwd' hj0 hlen0 (hsz1.trans hsz0.symm) hU1 hU hc
    (hcmd last) (hcmd last') ((hdrop _ hZ 0 (by omega)).trans hfwd) hfwd' htail
  have ht : (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (xorBytes
      ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
      geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)))).extract (geom.routingInfoLength - j *
            geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      = (xorBytes ((ofVector dS.2).extract ((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) (((geom.nrHops - (RSOR.path kem R last).size) *
          geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength))
      ((fillerAtF kem kdfS streamS geom (RSOR.path kem R last) ((joinDraw geom d dS j ((geom.nrHops
          - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)).1.toArray.extract 0
          (RSOR.path kem R last).size)
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector (joinDraw geom d dS j ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size (((ofVector (joinDraw geom d dS j
            ((geom.nrHops - (RSOR.path kem R last).size) *
            geom.perHopRoutingInfoLength)).2).extract 0 ((geom.nrHops - (RSOR.path kem R
            last).size) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength))) := by
    rw [Util.Bytes.extract_append_of_ge _ _ (by rw [zeroBytes_size]), zeroBytes_size,
      Nat.sub_self]
    exact extract_all _ _ (by rw [hTs, Nat.succ_mul]; rw [Nat.succ_mul] at hjp; omega)
  rw [ht] at hs
  have hHs : (xorBytes (U.extract 0 (geom.routingInfoLength - j * geom.perHopRoutingInfoLength))
        (xorBytes (midFrag geom kem (RSOR.path kem R last') j fwd'
        ++ fwd'.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + ((RSOR.path kem R last').size - (j + 1)) *
              geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R last') d j).extract 0 ((geom.nrHops -
            (RSOR.path kem R last').size) * geom.perHopRoutingInfoLength))
        (midFrag geom kem (RSOR.path kem R last) j fwd
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + ((RSOR.path kem R last).size - (j + 1)) *
              geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R last) (joinDraw geom d dS j ((geom.nrHops
            - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j).extract 0
            ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)))).size =
            (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
            geom.perHopRoutingInfoLength := by
    have h := hs.1
    rw [ByteArray.size_append, hTs] at h
    omega
  exact ⟨hs.1, hs.2.2, hdrop _ hHs⟩

omit kem kdfS streamS cipher macS in
theorem backMix_backMix (r r' : RSOR.Randomness geom) (j a : ℕ) :
    backMix geom (backMix geom r r' j a) (backCo geom r r' j a) j a = r := by
  simp only [backMix, backCo, joinDraw_joinDraw]

omit kem kdfS streamS cipher macS in
theorem backCo_backCo (r r' : RSOR.Randomness geom) (j a : ℕ) :
    backCo geom (backMix geom r r' j a) (backCo geom r r' j a) j a = r' := by
  simp only [backMix, backCo, coJoin_coJoin]

set_option maxHeartbeats 4000000 in
/-- **The relabelled draws are uniform, on the backward path.** A game that reads the two
randomness draws through their mix, and the keystream through the shifted keystream, reads one
randomness draw and one keystream. -/
theorem evalDistEq_backShift {δ : Type} (hvalid : geom.ValidForKEM kem)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (payload : ByteArray) (j : ℕ)
    (hj : j + 1 < R.hops.length)
    (K : Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength) → RSOR.Randomness
        geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let r' ← $ᵗ (RSOR.Randomness geom)
      let U ← $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength))
      K (Util.Bytes.toVecN _ (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply
          r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2])
        (backMix geom r r' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.1
            r.2.1 r'.1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply r'.2.2.2])
          r'.1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty)))
        (backMix geom r r' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)))
      =ᵈ (do
        let r ← $ᵗ (RSOR.Randomness geom)
        let U ← $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength))
        K U r) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hat : ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength) + ((j + 1) *
      geom.perHopRoutingInfoLength) ≤ geom.routingInfoLength := by
    rw [← Nat.add_mul, hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  have hm : (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) + ((j + 1) *
      geom.perHopRoutingInfoLength) = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := by
    rw [Nat.succ_mul] at hjp ⊢
    omega
  have e := evalDistEq_backMix geom j ((geom.nrHops - R.hops.length) *
      geom.perHopRoutingInfoLength) (fun r₀ r₀' =>
    $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)) >>= fun U =>
      K (Util.Bytes.toVecN _ (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply (backCo
          geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        (RSOR.path kem R [.surbReply (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
        r₀.2.1 (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length)
            * geom.perHopRoutingInfoLength)).1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).1
              payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
            (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty))) r₀)
  simp only [backMix_backMix, backCo_backCo] at e
  refine EvalDistEq.trans e (EvalDistEq.bind_right _ fun r₀ => ?_)
  have hg : Function.Bijective (Function.uncurry fun (P : Vector UInt8 geom.routingInfoLength)
      (q : Vector (Vector UInt8 32) geom.nrHops
        × (RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16)) =>
      (((q.1, P), q.2) : RSOR.Randomness geom)) :=
    ⟨fun x y h => by
      obtain ⟨P, q1, q2⟩ := x
      obtain ⟨P', q1', q2'⟩ := y
      simp only [Function.uncurry, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst h1 h2 h3
      rfl, fun r => ⟨(r.1.2, (r.1.1, r.2)), rfl⟩⟩
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hg fun r₀' =>
    $ᵗ (Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)) >>= fun U =>
      K (Util.Bytes.toVecN _ (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply (backCo
          geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        (RSOR.path kem R [.surbReply (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
        r₀.2.1 (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length)
            * geom.perHopRoutingInfoLength)).1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).1
              payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ r₀' j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
            (backMix geom r₀ r₀' j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty))) r₀).symm ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun q => ?_)
    (OracleComp.EvalDistEq.bind_const _ _)
  have key : ∀ (P : Vector UInt8 geom.routingInfoLength) (U : Vector UInt8 (geom.routingInfoLength
      + geom.perHopRoutingInfoLength)),
      (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P), q.2)
          j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
        r₀.2.1 (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).1 j (ofVector U)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (ofVector U) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty))
      = xorBytes ((ofVector U).extract 0 (geom.routingInfoLength - j *
          geom.perHopRoutingInfoLength))
          ((fun (P : Vector UInt8 geom.routingInfoLength) (T : ByteArray) => xorBytes
            (midFrag geom kem (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P), q.2) j
                ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
                layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
                geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
                geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j
                ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 j).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength))
            (midFrag geom kem (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P), q.2) j
                ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
                RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
                [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
                geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) r₀.2.1
            j).extract 0 ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength))) P
            ((ofVector U).extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)))
        ++ xorBytes ((ofVector P).extract ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength) (((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength) + ((j + 1) * geom.perHopRoutingInfoLength)))
          ((fillerAtF kem kdfS streamS geom (RSOR.path kem R [.surbReply r₀.2.2.2])
              (r₀.2.1.1.toArray.extract 0 R.hops.length)
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).size (((ofVector r₀.2.1.2).extract 0 ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)) := fun P U => by
    have htl : layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
        geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops -
        R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j (ofVector U) (j + 1)
        = layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix geom r₀
            ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ (ofVector
              U).extract (geom.routingInfoLength - j * geom.perHopRoutingInfoLength)
              (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j + 1) := by
      refine layerPast_tail geom kem kdfS streamS cipher macS hrouting _ _ payload j _ _
        (Util.Bytes.size_ofVector _) ?_ (by rw [RSOR.path_size]; exact hle)
        (by rw [RSOR.path_size]; exact hj) ?_
      · rw [ByteArray.size_append, zeroBytes_size, ByteArray.size_extract,
          Util.Bytes.size_ofVector]
        omega
      · rw [show (geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
          geom.perHopRoutingInfoLength = (geom.routingInfoLength - j *
          geom.perHopRoutingInfoLength) by omega,
          Util.Bytes.extract_append_of_ge _ _ (by rw [zeroBytes_size]), zeroBytes_size,
          Nat.sub_self]
        exact (extract_all _ _ (by
          rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
          omega)).symm
    have hreg : (ofVector (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength)).1.2).extract ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength) (((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength) + (j + 1) * geom.perHopRoutingInfoLength)
        = (ofVector P).extract ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)
            (((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength) + ((j + 1) *
            geom.perHopRoutingInfoLength)) :=
      coJoin_region geom _ _ j _ _
    unfold backShift
    simp only [RSOR.path_size]
    rw [htl, hreg]
    rfl
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun P => EvalDistEq.bind_right _ fun U => ?_)
    (evalDistEq_headRegion hat hm
    (fun (P : Vector UInt8 geom.routingInfoLength) (T : ByteArray) => xorBytes
      (midFrag geom kem (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P), q.2) j
          ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
          layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix geom r₀
          ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2])
          (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
          geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2]) (backMix geom r₀ ((q.1, P), q.2) j ((geom.nrHops
            - R.hops.length) * geom.perHopRoutingInfoLength)).2.1 payload j
          (zeroBytes (geom.routingInfoLength - j * geom.perHopRoutingInfoLength) ++ T) (j + 1) with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backMix geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) (backMix
            geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.1 j).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength))
      (midFrag geom kem (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P), q.2) j
          ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) j (match
          RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) [.surbReply
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
          geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).2.2.2])
          (backCo geom r₀ ((q.1, P), q.2) j ((geom.nrHops - R.hops.length) *
              geom.perHopRoutingInfoLength)).1 payload 0 with
        | .ok f => f
        | .error _ => ByteArray.empty).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + (R.hops.length - (j + 1)) * geom.perHopRoutingInfoLength)
        ++ (midPad geom kem kdfS streamS (RSOR.path kem R [.surbReply (backCo geom r₀ ((q.1, P),
            q.2) j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)).2.2.2]) r₀.2.1
            j).extract 0 ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)))
    ((fillerAtF kem kdfS streamS geom (RSOR.path kem R [.surbReply r₀.2.2.2])
        (r₀.2.1.1.toArray.extract 0 R.hops.length)
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)) j (zeroBytes (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) (j + 1)).extract
        ((ofVector r₀.2.1.2).extract 0 ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)).size (((ofVector r₀.2.1.2).extract 0 ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)).size + (j + 1) *
            geom.perHopRoutingInfoLength)) (fun U₀ => K U₀ r₀))
  rw [key P U]

end RestOfPath

section SentOn

variable {S : Protocols.RSOR.Scheme} {hon : Protocols.RSOR.Honest S}
  (c : Protocols.RSOR.BackwardChallenge hon) (onion : S.Onion) (own exit : Option S.Header)
  (swap : S.Onion) (refuse : S.Header)

/-- Under the header it is told, the relay of the world where an onion is sent on forwards
that onion, when it forwards anything. -/
theorem world1With_proc_own (o : S.Onion) (out : Option S.Step) :
    (c.world1With onion (some o.1) exit swap refuse).patch.proc .relay o out
      = pure (out.map fun _ => .forward (c.req.back.hops[c.pos].name) swap) := by
  simp [Protocols.RSOR.BackwardChallenge.world1With]

/-- Elsewhere the world where an onion is sent on changes one answer: the sender does not
answer the header it is told to refuse. -/
theorem world1With_proc_other (h : Protocols.RSOR.Role) (o : S.Onion) (out : Option S.Step)
    (hne : ¬ (h = .relay ∧ own = some o.1)) :
    (c.world1With onion own exit swap refuse).patch.proc h o out
      = if h = .sender ∧ o.1 = refuse then pure none else pure out := by
  simp [Protocols.RSOR.BackwardChallenge.world1With, hne]

/-- With no exit header given, the world where an onion is sent on changes no reply. -/
theorem world1With_reply (h : Protocols.RSOR.Role) (m : S.Msg) (o : S.Onion)
    (out : Option (S.Name × S.Onion)) :
    (c.world1With onion own none swap refuse).patch.reply h m o out = out := by
  simp [Protocols.RSOR.BackwardChallenge.world1With]

end SentOn

section BackRelay

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

omit h16 in
include hvalid hmactag in
/-- **A relay does not reply under the header of a hop in the middle of a path**, whatever the
payload cipher of the reply it would build. -/
theorem replyOf_relayFront_default (hops : Array PathHop) (d : RSOR.Draw geom)
    (payload : ByteArray) (j : ℕ) (c U fwd : ByteArray) (km : Vector UInt8 32)
    (x y : Block geom) (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hc : c.size =
        kem.ciphertextSize)
    (hfwd : layerPast kem default macS kdfS streamS geom hops d payload j U (j + 1) = .ok fwd)
    (hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength)
    (hcmd : (hops[j]!).commands = []) (m : RSOR.Msg geom) :
    RSOR.replyOf cipher geom m (procKeysD kem macS geom km U (ofVector x)
        (RSOR.join (Util.Bytes.toVecN geom.headerLength
          (relayFront kem default macS kdfS streamS geom hops d payload j c U
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops d payload j c U))), y)))
      = none := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hs := relayFront_size geom kem kdfS streamS default macS hvalid hmactag hops d payload j c
    U fwd hj hlen hc hfwd hcmd
  unfold RSOR.join
  dsimp only
  rw [Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hs, Util.Bytes.size_ofVector, hmactag, hhdr, had]),
    procKeysD_relayFront geom kem kdfS streamS default macS hvalid hmactag hops d payload j c U
      fwd km (ofVector x) (ofVector y) hj hlen hU hc hfwd hs
      (by rw [Util.Bytes.size_ofVector]; exact hx)
      (by rw [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector])
      (by rw [hcmd]; simp) (by rw [hcmd]; simp)]
  rfl

/-- **A relay that answers one header hands on one fresh block.** When its patched reply
under that header does not depend on the decrypted block, the relay whose payload under the
header decrypts as the ideal cipher does after one encryption is the relay whose payload
decrypts to one uniform block. -/
theorem headerRelays_fresh (ρ : Role) (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext)
    (km : Vector UInt8 32) (U : ByteArray) (Hv : Vector UInt8 geom.headerLength)
    (patch : Protocols.RSOR.Patch 𝒮)
    (hrep : ∀ (m : RSOR.Msg geom) (o : RSOR.Onion geom) (x : Block geom), o.1 = Hv →
      patch.reply ρ m o (RSOR.replyOf cipher geom m
          (procKeysD kem macS geom km U (ofVector x) (RSOR.join o)))
        = patch.reply ρ m o (RSOR.replyOf cipher geom m
          (procKeysD kem macS geom km U (ofVector (default : Block geom)) (RSOR.join o))))
    {α : Type} (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α) (log : Protocols.RSOR.Log 𝒮) :
    (do
      let u ← $ᵗ (Block geom)
      let w ← $ᵗ (Block geom)
      let v ← $ᵗ (Block geom)
      (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk ct km U
        Hv (fun y => if y = u then w else v) patch) oa).run' log)
      =ᵈ ($ᵗ (Block geom) >>= fun g =>
        (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk ct km U
          Hv (fun _ => g) patch) oa).run' log) := by
  have h := (withDec_fresh (S := 𝒮) ρ Hv (fun o => o.2)
    (fun o x => RSOR.stepOf geom (procKeysD kem macS geom km U (ofVector x) (RSOR.join o)))
    (fun msg o x => RSOR.replyOf cipher geom msg
      (procKeysD kem macS geom km U (ofVector x) (RSOR.join o)))
    (fun h o => if h = ρ then
        RSOR.stepOf geom
          (relayAns kem cipher macS kdfS streamS geom (sk ρ) ct (fun _ => none) (RSOR.join o))
      else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o)
    (fun h msg o => if h = ρ then
        RSOR.replyOf cipher geom msg
          (relayAns kem cipher macS kdfS streamS geom (sk ρ) ct (fun _ => none) (RSOR.join o))
      else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o)
    patch hrep oa log).map Prod.fst
  simp only [map_bind] at h
  exact h

set_option maxHeartbeats 2000000 in
/-- **On the backward path, world 1′'s patched relay is world 0's relay with one fresh block.**
World 0's relay has the header of a hop in the middle of the reply's path, and forwards the
next layer's header with the block `g`. The relay of the world where an onion is sent on has
the same header bytes, and whatever it would forward is patched to that onion. The two games
are the same when the onion is the next layer's header with `g`. -/
theorem headerRelays_back_eq {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.BackwardChallenge hon) (sk : Role → kem.PrivateKey)
    (ct : kem.Ciphertext) (km : Vector UInt8 32) (U₀ U₁ : ByteArray)
    (D₁ : Block geom → Block geom) (g : Block geom) (hops₀ hops₁ : Array PathHop)
    (d₀ d₁ : RSOR.Draw geom) (payload : ByteArray) (j : ℕ) (cc fwd₀ fwd₁ : ByteArray)
    (onion : RSOR.Onion geom) (refuse : Vector UInt8 geom.headerLength)
    (hj₀ : j + 1 < hops₀.size) (hlen₀ : hops₀.size ≤ geom.nrHops)
    (hj₁ : j + 1 < hops₁.size) (hlen₁ : hops₁.size ≤ geom.nrHops)
    (hU₀ : U₀.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hU₁ : U₁.size =
        (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hc : cc.size = kem.ciphertextSize)
    (hfwd₀ : layerPast kem default macS kdfS streamS geom hops₀ d₀ payload j U₀ (j + 1) = .ok fwd₀)
    (hfwd₁ : layerPast kem default macS kdfS streamS geom hops₁ d₁ payload j U₁ (j + 1) = .ok fwd₁)
    (hcmd₀ : (hops₀[j]!).commands = []) (hcmd₁ : (hops₁[j]!).commands = [])
    (hF : relayFront kem default macS kdfS streamS geom hops₁ d₁ payload j cc U₁
      = (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀))
    (hname : (hops₀[j + 1]!).id = c.req.back.hops[c.pos].name) :
    headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk ct km U₁
        (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)))) D₁
        (Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) c onion
          (some (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀))))) none
          (Util.Bytes.toVecN _ (fwd₀.extract 0 geom.headerLength), g) refuse).patch
      = headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk ct km U₀
        (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)))) (fun _ =>
                  g)
        ({ proc := fun (h : Role) (o : RSOR.Onion geom) out =>
            if h = .sender ∧ o.1 = refuse then pure none else pure out } :
          Protocols.RSOR.Patch 𝒮) := by
  obtain ⟨-, -, -, hhdr, hpacket, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hH : 2 + kem.ciphertextSize + geom.routingInfoLength + macLength = geom.headerLength := by
    rw [hhdr, had]
  have hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength := by omega
  have hs₀ := relayFront_size geom kem kdfS streamS default macS hvalid hmactag hops₀ d₀ payload
    j cc U₀ fwd₀ hj₀ hlen₀ hc hfwd₀ hcmd₀
  have hs₁ := relayFront_size geom kem kdfS streamS default macS hvalid hmactag hops₁ d₁ payload
    j cc U₁ fwd₁ hj₁ hlen₁ hc hfwd₁ hcmd₁
  have hfwd₀' := hfwd₀
  unfold layerPast at hfwd₀'
  have hfsz : fwd₀.size = geom.packetLength :=
    newKEMPacket_size kem default macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hfwd₀'
      (newKEMPacket_unfold kem default macS kdfS streamS geom _ _ _ _ _ hfwd₀').1
  have hst₀ := fun y : Block geom => stepOf_relayFront geom kem kdfS streamS default macS hvalid
    hmactag hops₀ d₀ payload j cc U₀ fwd₀ km g y hj₀ hlen₀ hU₀ hc hfwd₀ hs₀ hx hcmd₀
  have hst₁ := fun x y : Block geom => stepOf_relayFront geom kem kdfS streamS default macS
    hvalid hmactag hops₁ d₁ payload j cc U₁ fwd₁ km x y hj₁ hlen₁ hU₁ hc hfwd₁ hs₁ hx hcmd₁
  have hrp₀ := fun (m : RSOR.Msg geom) (y : Block geom) => replyOf_relayFront_default kem cipher
    macS kdfS streamS geom hvalid hmactag hops₀ d₀ payload j cc U₀ fwd₀ km g y hj₀ hlen₀ hU₀ hc
    hfwd₀ hx hcmd₀ m
  have hrp₁ := fun (m : RSOR.Msg geom) (x y : Block geom) => replyOf_relayFront_default kem
    cipher macS kdfS streamS geom hvalid hmactag hops₁ d₁ payload j cc U₁ fwd₁ km x y hj₁ hlen₁
    hU₁ hc hfwd₁ hx hcmd₁ m
  simp only [hF] at hst₁ hrp₁
  simp only [hH] at hst₀ hst₁
  rw [hname, split_append geom _ _ (by
    rw [ByteArray.size_extract]
    omega)] at hst₀
  refine Protocols.RSOR.oracle_patch_congr (S := 𝒮) _ _ _ _ _ _ (fun h o => ?_)
    (fun h m o => ?_)
  · obtain ⟨o1, o2⟩ := o
    by_cases hc' : h = Role.relay ∧ o1 = (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀))))
    · obtain ⟨rfl, rfl⟩ := hc'
      have h4 : Role.relay = Role.relay ∧ (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)))) =
                  (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)))) := ⟨rfl,
                  rfl⟩
      refine (congrArg ((Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) c onion _ none _
        refuse).patch.proc Role.relay _)
        ((ite_eq_left h4).trans (hst₁ _ o2))).trans ?_
      refine (world1With_proc_own (S := 𝒮) c onion none _ refuse _ _).trans ?_
      refine Eq.trans ?_ (congrArg (({ proc := fun (h : Role) (o : RSOR.Onion geom) out =>
            if h = .sender ∧ o.1 = refuse then pure none else pure out } :
          Protocols.RSOR.Patch 𝒮).proc Role.relay _)
        ((ite_eq_left h4).trans (hst₀ o2))).symm
      rfl
    · have hne : ¬ (h = Role.relay ∧ some (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)))) = some
                  o1) :=
        fun hx => hc' ⟨hx.1, (Option.some.inj hx.2).symm⟩
      refine (congrArg ((Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) c onion _ none _
        refuse).patch.proc h _) (ite_eq_right hc')).trans ?_
      refine (world1With_proc_other (S := 𝒮) c onion _ none _ refuse h _ _ hne).trans ?_
      exact (congrArg (({ proc := fun (h : Role) (o : RSOR.Onion geom) out =>
            if h = .sender ∧ o.1 = refuse then pure none else pure out } :
          Protocols.RSOR.Patch 𝒮).proc h _) (ite_eq_right hc')).symm
  · obtain ⟨o1, o2⟩ := o
    refine (world1With_reply (S := 𝒮) c onion _ _ refuse h m _ _).trans ?_
    by_cases hc' : h = Role.relay ∧ o1 = (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀))))
    · obtain ⟨rfl, rfl⟩ := hc'
      have h4 : Role.relay = Role.relay ∧ (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)))) =
                  (Util.Bytes.toVecN geom.headerLength
          ((relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)
            ++ ofVector (macS.mac (ofVector km)
              (relayFront kem default macS kdfS streamS geom hops₀ d₀ payload j cc U₀)))) := ⟨rfl,
                  rfl⟩
      exact ((ite_eq_left h4).trans (hrp₁ m _ o2)).trans
        ((ite_eq_left h4).trans (hrp₀ m o2)).symm
    · exact (ite_eq_right hc').trans (ite_eq_right hc').symm

omit h16 in
include hvalid hmactag in
set_option maxHeartbeats 2000000 in
/-- **The reply at the honest relay, at the relabelled draws.** With the joined draw and the
shifted keystream, the relay's layer of the reply has the bytes it has with the first draw: in
front of the tag, behind it, and in the layers around it. The next layer is the first layer
over the rest of the path with the second draw, and every later header is that draw's. -/
theorem backPieces (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (r r' : RSOR.Randomness geom) (payload : ByteArray) (j : ℕ) (cc U fwd' fwdS : ByteArray)
    (hj : j + 1 < R.hops.length) (hU : U.size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) (hc : cc.size = kem.ciphertextSize)
    (hfwd' : layerPast kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
        r.2.1 payload j U (j + 1) = .ok fwd')
    (hfwdS : RSOR.layer kem default macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
        [.surbReply r'.2.2.2]) r'.1 payload 0 = .ok fwdS) :
    (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j U fwdS fwd').size =
            (geom.routingInfoLength + geom.perHopRoutingInfoLength)
    ∧ relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r'.2.2.2])
        (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength))
        payload j cc
        (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j U fwdS fwd')
      = relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1
          payload j cc U
    ∧ relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1
        payload j cc U
      = relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1
          payload j cc U
    ∧ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r'.2.2.2])
        (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength))
        payload j
        (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j U fwdS fwd') id
      = relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1
          payload j U id
    ∧ (∀ L : ByteArray, wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply
        r'.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) *
        geom.perHopRoutingInfoLength)) 0 j L
      = wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1 0 j
          L)
    ∧ layerPast kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r'.2.2.2])
        (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength))
        payload j
        (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j U fwdS fwd') (j + 1) = .ok
            fwdS
    ∧ ∀ i, j + 1 + i ≤ R.hops.length →
      (match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem R [.surbReply r'.2.2.2])
          (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) *
          geom.perHopRoutingInfoLength)) payload j
          (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j U fwdS fwd') (j + 1 + i)
            with
        | .ok p => (RSOR.split geom p).1
        | .error _ => (default : RSOR.Onion geom).1)
      = (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
          [.surbReply r'.2.2.2]) r'.1 payload i with
        | .ok p => (RSOR.split geom p).1
        | .error _ => (default : RSOR.Onion geom).1) := by
  have hle := R.length_le
  have hsz : ∀ l : List RoutingCommand, (RSOR.path kem R l).size = R.hops.length :=
    fun l => RSOR.path_size kem R l
  obtain ⟨hs, hF, hL⟩ := backShift_spec kem geom kdfS streamS default macS hvalid hmactag R
    [.surbReply r'.2.2.2] [.surbReply r.2.2.2] r.2.1 r'.1 payload j ((geom.nrHops - R.hops.length)
        * geom.perHopRoutingInfoLength) cc U fwdS fwd'
    (by rw [hsz]) hj hU hc hfwd' hfwdS
  have hif : ∀ l : List RoutingCommand, j + 1 < (RSOR.path kem R l).size := fun l => by
    rw [hsz]
    exact hj
  have h0 := (hL 0 (by omega)).trans hfwdS
  refine ⟨hs, ?_, ?_, ?_, ?_, h0, fun i hi => ?_⟩
  · unfold relayFrontAt
    exact (ite_eq_left (hif _)).trans hF
  · unfold relayFrontAt
    exact ite_eq_left (hif _)
  · unfold relayBackAt
    refine (ite_eq_left (hif _)).trans (Eq.trans ?_ (ite_eq_left (hif _)).symm)
    rw [relayBack_default kem macS kdfS streamS geom hvalid hmactag _ _ payload j _ fwdS h0,
      relayBack_default kem macS kdfS streamS geom hvalid hmactag _ _ payload j _ fwd' hfwd']
  · intro L
    refine wrapUp_congr geom kem kdfS streamS default macS _ _ _ _ (by rw [hsz]; exact hle)
      (by rw [hsz]; exact hle) 0 j L fun k _ hk => ⟨by rw [hsz]; omega, by rw [hsz]; omega, ?_,
        ?_, ?_⟩
    · rw [RSOR.path_getElem! kem R _ k (by omega), RSOR.path_getElem! kem R _ k (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [RSOR.path_getElem! kem R _ (k + 1) (by omega),
        RSOR.path_getElem! kem R _ (k + 1) (by omega)]
    · rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)]
      simp [joinDraw, show k ≤ j by omega]
  · have e1 := newKEMPacket_header kem macS kdfS streamS geom hvalid hmactag cipher default
    have e2 := congrArg (fun e : Except String ByteArray => match e with
      | .ok p => (RSOR.split geom p).1
      | .error _ => (default : RSOR.Onion geom).1) (hL i hi)
    exact (e1 _ _ _ _).trans (e2.trans (newKEMPacket_header kem macS kdfS streamS geom hvalid
      hmactag default cipher _ _ _ _))


omit hvalid hmactag h16 in
/-- A header's bytes followed by anything split off as the header. -/
theorem split_fst_append (H B : ByteArray) (hH : H.size = geom.headerLength) :
    (RSOR.split geom (H ++ B)).1 = Util.Bytes.toVecN geom.headerLength H := by
  unfold RSOR.split
  dsimp only
  rw [Util.Bytes.extract_append_of_le _ _ (le_of_eq hH.symm), extract_all _ _ hH]
  rfl

/-- **The onion sent on, after backward position `j`**: the header of the first layer over the
rest of the backward path, built with any payload cipher, and the drawn block. -/
theorem replySwap_fst {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.BackwardChallenge hon)
    (x : RSOR.Randomness geom × Block geom) (j : ℕ) (hp : c.pos.val = j + 1)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (hR : c.req.back = R) (fwdS :
        ByteArray)
    (hfwdS : RSOR.layer kem default macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
        [.surbReply x.1.2.2.2]) x.1.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) 0
        = .ok fwdS) :
    ((replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16).of c x).1
      = (Util.Bytes.toVecN _ (fwdS.extract 0 geom.headerLength), x.2) := by
  obtain ⟨p, hpk, hph⟩ := newKEMPacket_ok_header kem cipher macS kdfS streamS geom hvalid hmactag
    _ _ _ _ _ hfwdS
  subst hR
  unfold replySwap
  dsimp only
  rw [hp]
  refine (congrArg (fun e : Except String ByteArray => match e with
    | .ok pkt => ((RSOR.split geom pkt).1, x.2)
    | .error _ => (default : RSOR.Onion geom)) hpk).trans ?_
  exact Prod.ext hph rfl

/-- **The header the sender refuses, after backward position `j`**: that of the last layer over
the rest of the backward path. -/
theorem replySwap_snd {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.BackwardChallenge hon)
    (x : RSOR.Randomness geom × Block geom) (j : ℕ) (hp : c.pos.val = j + 1)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (hR : c.req.back = R) :
    ((replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16).of c x).2
      = (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
          [.surbReply x.1.2.2.2]) x.1.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) := by
  subst hR
  unfold replySwap
  dsimp only
  rw [hp]
  rfl

section Canon

variable (names : Role → RSOR.Name)

/-- On the backward path the relay's header bytes are those of its layer of the reply. -/
theorem backMU_back (W : Protocols.RSOR.BackSwap 𝒮) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (U : ByteArray) (j : ℕ)
    (hp : ch.c.pos.val = j + 1)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (hR : ch.c.req.back = R) :
    backMU kem cipher macS kdfS streamS geom hvalid hmactag h16 W names ch r c U
      = (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
          r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext c)) U) := by
  subst hR
  unfold backMU
  rw [hp]

/-- On the backward path world 0 shows the adversary's onion with the reply's first header in
its payload, and its sender does not answer the reply's last layer. -/
theorem backViewU0_back (W : Protocols.RSOR.BackSwap 𝒮) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names pk)
    (ow : RSOR.Randomness geom × Block geom) (c : kem.Ciphertext) (km : Vector UInt8 32)
    (U : ByteArray) (e : Block geom) (j : ℕ) (hp : ch.c.pos.val = j + 1)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (hR : ch.c.req.back = R) :
    backViewU0 kem cipher macS kdfS streamS geom hvalid hmactag h16 W names ch ow c km U e
      = { onion := (backOnionX kem cipher macS kdfS streamS geom ch.c.req ow.1
        (Nat.zero_lt_of_lt ch.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply ow.1.2.2.2])
            ow.1.2.1 0 j
        ((relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply ow.1.2.2.2])
          ow.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext c)) U)
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem R [.surbReply ow.1.2.2.2])
          ow.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext c)) U))
          ++ (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply
              ow.1.2.2.2])
          ow.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j U id)))))
          patch :=
            { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
                if h = .sender ∧ o.1 = backHeaderU kem cipher macS kdfS streamS geom ch.c.req ow.1
                    j U (R.hops.length - 1) then pure none
                else pure out } } := by
  subst hR
  unfold backViewU0
  split
  · next h0 => omega
  · next k hk =>
    obtain rfl : k = j := by omega
    rfl

/-- On the backward path the world where an onion is sent on shows the same onion, and its
relay sends that onion on under the header of its layer of the reply. -/
theorem backViewU1_back (W : Protocols.RSOR.BackSwap 𝒮) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names pk)
    (o : RSOR.Randomness geom × W.X) (c : kem.Ciphertext) (km : Vector UInt8 32)
    (U : ByteArray) (e : Block geom) (j : ℕ) (hp : ch.c.pos.val = j + 1)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (hR : ch.c.req.back = R) :
    backViewU1 kem cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o c km U e
      = Protocols.RSOR.BackwardChallenge.world1With ch.c
        (backOnionX kem cipher macS kdfS streamS geom ch.c.req o.1
        (Nat.zero_lt_of_lt ch.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply o.1.2.2.2])
            o.1.2.1 0 j
        ((relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply o.1.2.2.2])
          o.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext c)) U)
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem R [.surbReply o.1.2.2.2])
          o.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext c)) U))
          ++ (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply
              o.1.2.2.2])
          o.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j U id)))))
        (if j < R.hops.length then
          some (RSOR.split geom
            ((relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply
                o.1.2.2.2])
          o.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext c)) U)
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem R [.surbReply o.1.2.2.2])
          o.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext c)) U))
          ++ (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply
              o.1.2.2.2])
          o.1.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j U id))).1
        else none)
        none (W.of ch.c o.2).1 (W.of ch.c o.2).2 := by
  subst hR
  unfold backViewU1
  split
  · next h0 => omega
  · next k hk =>
    obtain rfl : k = j := by omega
    rfl

end Canon

set_option maxHeartbeats 8000000 in
/-- **On the backward path, world 0 at the relabelled draws is the world where a reply layer
is sent on.** With the mixed randomness and the shifted keystream, and the block the ideal
cipher decrypts to drawn, world 0's game is the game of the world where the relay sends on the
first layer over the rest of the path with a drawn block. -/
theorem backRun_evalDistEq (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardWith (replySwap
    kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary)
    (km : Vector UInt8 32) (k : Key kem × kem.PrivateKey)
    (cs : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names k.1
      × (A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)))
    (s : Vector UInt8 32) (r r' : RSOR.Randomness geom) (U : Keystream geom) (j : ℕ)
    (hp : cs.1.c.pos.val = j + 1)
    (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem)) (hR : cs.1.c.req.back = R) (fwd'
        fwdS : ByteArray)
    (hfwd' : layerPast kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
        r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U) (j + 1) =
        .ok fwd')
    (hfwdS : RSOR.layer kem default macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
        [.surbReply r'.2.2.2]) r'.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) 0 =
        .ok fwdS) :
    (do
      let b ← $ᵗ (Block geom)
      let u ← $ᵗ (Block geom)
      let v ← $ᵗ (Block geom)
      (propRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names _
          (backDraw0 geom)
        (backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher macS
            kdfS streamS geom hvalid hmactag h16) names) A (backMU0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
            h16) names)
        (backBlockU0 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher
            macS kdfS streamS geom hvalid hmactag h16) names) (backViewU0 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid
            hmactag h16) names) km
        (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
        (⟨k, cs, s, (((r.1, (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)), r.2.2.1, r'.2.2.2) : RSOR.Randomness geom), b)⟩ :
            KeyedDraw (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem
            cipher macS kdfS streamS geom hvalid hmactag h16) names A)) u v))
      =ᵈ (do
        let g ← $ᵗ (Block geom)
        let u ← $ᵗ (Block geom)
        let v ← $ᵗ (Block geom)
        (propRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
            (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names _
            (swapDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher
            macS kdfS streamS geom hvalid hmactag h16))
        (backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher macS
            kdfS streamS geom hvalid hmactag h16) names) A (backMU1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
            h16) names)
        (backBlockU1 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher
            macS kdfS streamS geom hvalid hmactag h16) names) (backViewU1 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid
            hmactag h16) names) km
        (ofVector U)
        (⟨k, cs, s, (r, (r', g))⟩ : KeyedDraw (backAdv1 kem cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16) names A))
            u v)) := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hjL : j + 1 < R.hops.length := by
    have h := cs.1.c.pos.isLt
    rw [hp] at h
    rw [← hR]
    exact h
  have hle := R.length_le
  have hsz : ∀ l : List RoutingCommand, (RSOR.path kem R l).size = R.hops.length :=
    fun l => RSOR.path_size kem R l
  have hif : ∀ l : List RoutingCommand, j + 1 < (RSOR.path kem R l).size :=
    fun l => lt_of_lt_of_eq hjL (hsz l).symm
  have hlen : ∀ l : List RoutingCommand, (RSOR.path kem R l).size ≤ geom.nrHops :=
    fun l => le_of_eq_of_le (hsz l) hle
  have hcmd : ∀ l : List RoutingCommand, ((RSOR.path kem R l)[j]!).commands = [] :=
    fun l => by
    rw [RSOR.path_getElem! kem R l j (by omega), ite_eq_right (by omega)]
  have hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength := by omega
  obtain ⟨hs, hF, hF1, hB, hW, h0, hRef⟩ := backPieces kem cipher macS kdfS streamS geom hvalid
    hmactag R r r' (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
        (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) fwd' fwdS hjL
        (Util.Bytes.size_ofVector _)
    (Util.Bytes.size_ofVector _) hfwd' hfwdS
  have hF0 : relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r'.2.2.2])
      (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength))
      (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector (kem.encodeCiphertext
      (encapOf kem k.1.1 s).1))
      (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd') =
            (relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) := by
    have h := hF
    unfold relayFrontAt at h
    exact (ite_eq_left (hif _)).symm.trans h
  have hs1 := relayFront_size geom kem kdfS streamS default macS hvalid hmactag (RSOR.path kem R
      [.surbReply r.2.2.2]) r.2.1
    (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector (kem.encodeCiphertext
        (encapOf kem k.1.1 s).1)) (ofVector U) fwd' (hif _) (hlen _) (Util.Bytes.size_ofVector _)
        hfwd'
    (hcmd _)
  have hHVs : ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply
      r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
      (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac (ofVector
      km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
      r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
      (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)))).size = geom.headerLength := by
    rw [ByteArray.size_append, hs1, Util.Bytes.size_ofVector, hmactag, hhdr, had]
  have hREF0 : backHeaderU kem cipher macS kdfS streamS geom cs.1.c.req ((r.1, (joinDraw geom r.2.1
      r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)), r.2.2.1, r'.2.2.2) :
      RSOR.Randomness geom) j
      (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
            (R.hops.length - 1) = (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path
            kem (R.drop (j + 1)) [.surbReply r'.2.2.2]) r'.1 (⟨Array.replicate
            geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) := by
    have h := hRef (R.hops.length - (j + 1) - 1) (by omega)
    rw [show j + 1 + (R.hops.length - (j + 1) - 1) = R.hops.length - 1 by omega] at h
    have hl : (R.drop (j + 1)).hops.length - 1 = R.hops.length - (j + 1) - 1 := by
      simp [Protocols.RSOR.Route.drop]
    rw [← hl] at h
    unfold backHeaderU
    rw [hR]
    exact h
  have hV0 : ∀ b u : Block geom,
      backViewU0 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher macS
          kdfS streamS geom hvalid hmactag h16) names cs.1 (((r.1, (joinDraw geom r.2.1 r'.1 j
          ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)), r.2.2.1, r'.2.2.2) :
          RSOR.Randomness geom), b) (encapOf kem k.1.1 s).1 km
        (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd') u
      = { onion := (backOnionX kem cipher macS kdfS streamS geom cs.1.c.req r
        (Nat.zero_lt_of_lt cs.1.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 0 j
        ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac
            (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R
            [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
            j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))) ++
            (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U) id)))))
          patch := ({ proc := fun (h : Role) (o : RSOR.Onion geom) out =>
          if h = .sender ∧ o.1 = (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem
              (R.drop (j + 1)) [.surbReply r'.2.2.2]) r'.1 (⟨Array.replicate
              geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) then pure none else pure out } :
        Protocols.RSOR.Patch 𝒮) } := fun b u => by
    rw [backViewU0_back kem cipher macS kdfS streamS geom hvalid hmactag h16 names (replySwap kem
        cipher macS kdfS streamS geom hvalid hmactag h16) cs.1 _ (encapOf kem k.1.1 s).1 km _ u j
        hp R hR]
    dsimp only
    rw [hW, hF, hB, hREF0]
    rfl
  have hM0 : ∀ b : Block geom, backMU0 kem cipher macS kdfS streamS geom hvalid hmactag h16
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16) names cs.1 (((r.1, (joinDraw
      geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)), r.2.2.1,
      r'.2.2.2) : RSOR.Randomness geom), b) (encapOf kem k.1.1 s).1
      (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd') =
            (relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) := fun b => by
    unfold backMU0
    rw [backMU_back kem cipher macS kdfS streamS geom hvalid hmactag h16 names (replySwap kem
        cipher macS kdfS streamS geom hvalid hmactag h16) cs.1 _ (encapOf kem k.1.1 s).1 _ j hp R
        hR]
    exact hF
  have hpl0 : ∀ b : Block geom, backBlockU0 kem cipher macS kdfS streamS geom hvalid hmactag h16
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16) names cs.1 (((r.1, (joinDraw
      geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength)), r.2.2.1,
      r'.2.2.2) : RSOR.Randomness geom), b)
      (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd') =
            b := fun b => by
    unfold backBlockU0
    split
    · next h0 => omega
    · rfl
  have hM1 : ∀ g : Block geom, backMU1 kem cipher macS kdfS streamS geom hvalid hmactag h16
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16) names cs.1 (r, (r', g))
      (encapOf kem k.1.1 s).1
      (ofVector U) = (relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply
          r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
          (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) := fun g => by
    unfold backMU1
    rw [backMU_back kem cipher macS kdfS streamS geom hvalid hmactag h16 names (replySwap kem
        cipher macS kdfS streamS geom hvalid hmactag h16) cs.1 _ (encapOf kem k.1.1 s).1 _ j hp R
        hR]
    exact hF1
  have hV1 : ∀ g u : Block geom,
      backViewU1 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher macS
          kdfS streamS geom hvalid hmactag h16) names cs.1 (r, (r', g)) (encapOf kem k.1.1 s).1 km
          (ofVector U) u
      = Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) cs.1.c
        (backOnionX kem cipher macS kdfS streamS geom cs.1.c.req r
        (Nat.zero_lt_of_lt cs.1.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 0 j
        ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac
            (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R
            [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
            j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))) ++
            (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U) id)))))
        (some (Util.Bytes.toVecN geom.headerLength ((relayFront kem default macS kdfS streamS geom
            (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate
            geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector (kem.encodeCiphertext (encapOf
            kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac (ofVector km) (relayFront kem
            default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1
            (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)))))) none
        (Util.Bytes.toVecN _ (fwdS.extract 0 geom.headerLength), g)
        (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1))
            [.surbReply r'.2.2.2]) r'.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) := fun g u => by
    rw [backViewU1_back kem cipher macS kdfS streamS geom hvalid hmactag h16 names (replySwap kem
        cipher macS kdfS streamS geom hvalid hmactag h16) cs.1 _ (encapOf kem k.1.1 s).1 km _ u j
        hp R hR]
    dsimp only
    rw [replySwap_fst kem cipher macS kdfS streamS geom hvalid hmactag h16 cs.1.c (r', g) j hp R hR
        fwdS hfwdS,
      replySwap_snd kem cipher macS kdfS streamS geom hvalid hmactag h16 cs.1.c (r', g) j hp R hR,
          hF1,
      ite_eq_left (show j < R.hops.length from Nat.lt_of_succ_lt hjL),
      split_fst_append geom _ _ hHVs]
    rfl
  have hname : ((RSOR.path kem R [.surbReply r'.2.2.2])[j + 1]!).id =
      cs.1.c.req.back.hops[cs.1.c.pos].name := by
    subst hR
    rw [RSOR.path_getElem! kem _ _ (j + 1) hjL]
    simp only [Fin.getElem_fin, hp]
    rfl
  have hr := fun (m : RSOR.Msg geom) (x y : Block geom) => replyOf_relayFront_default kem cipher
    macS kdfS streamS geom hvalid hmactag (RSOR.path kem R [.surbReply r'.2.2.2]) (joinDraw geom
        r.2.1 r'.1 j ((geom.nrHops - R.hops.length) * geom.perHopRoutingInfoLength))
        (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
        (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
    (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
            fwdS km x y (hif _) (hlen _) hs (Util.Bytes.size_ofVector _) h0 hx (hcmd _) m
  simp only [hF0] at hr
  have hback := fun (g : Block geom) (D₁ : Block geom → Block geom) => headerRelays_back_eq
    kem cipher macS kdfS streamS geom hvalid hmactag h16 cs.1.c (fun h => if h = Role.relay then
        k.2 else cs.2.2.2 h) (encapOf kem k.1.1 s).1 km
    (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
            (ofVector U) D₁ g (RSOR.path kem R [.surbReply r'.2.2.2]) (RSOR.path kem R [.surbReply
            r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
            ByteArray) j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) fwdS fwd'
    (backOnionX kem cipher macS kdfS streamS geom cs.1.c.req r
        (Nat.zero_lt_of_lt cs.1.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 0 j
        ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac
            (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R
            [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
            j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))) ++
            (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U) id)))))
    (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop (j + 1)) [.surbReply
        r'.2.2.2]) r'.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) (hif _) (hlen _) (hif _) (hlen _) hs
            (Util.Bytes.size_ofVector _)
    (Util.Bytes.size_ofVector _) h0 hfwd' (hcmd _) (hcmd _) hF0.symm hname
  simp only [hF0] at hback
  have e0 : ∀ b u v : Block geom,
      (propRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names _
          (backDraw0 geom)
        (backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher macS
            kdfS streamS geom hvalid hmactag h16) names) A (backMU0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
            h16) names)
        (backBlockU0 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher
            macS kdfS streamS geom hvalid hmactag h16) names) (backViewU0 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid
            hmactag h16) names) km
        (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
        (⟨k, cs, s, (((r.1, (joinDraw geom r.2.1 r'.1 j ((geom.nrHops - R.hops.length) *
            geom.perHopRoutingInfoLength)), r.2.2.1, r'.2.2.2) : RSOR.Randomness geom), b)⟩ :
            KeyedDraw (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem
            cipher macS kdfS streamS geom hvalid hmactag h16) names A)) u v)
      = (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h
          => if h = Role.relay then k.2 else cs.2.2.2 h) (encapOf kem k.1.1 s).1 km
          (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
          (Util.Bytes.toVecN geom.headerLength ((relayFront kem default macS kdfS streamS geom
              (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate
              geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector (kem.encodeCiphertext (encapOf
              kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac (ofVector km) (relayFront kem
              default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1
              (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)))))
          (fun y => if y = u then b else v)
          ({ proc := fun (h : Role) (o : RSOR.Onion geom) out =>
          if h = .sender ∧ o.1 = (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem
              (R.drop (j + 1)) [.surbReply r'.2.2.2]) r'.1 (⟨Array.replicate
              geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) then pure none else pure out } :
        Protocols.RSOR.Patch 𝒮))
        (A.guess cs.2.1 (backOnionX kem cipher macS kdfS streamS geom cs.1.c.req r
        (Nat.zero_lt_of_lt cs.1.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 0 j
        ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac
            (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R
            [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
            j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))) ++
            (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U)
            id))))))).run' cs.2.2.1 := fun b u v => by
    unfold propRunU KeyedDraw.c
    dsimp only
    rw [hV0 b u, hM0 b, hpl0 b]
  have e1 : ∀ g u v : Block geom,
      (propRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names _
          (swapDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher macS
          kdfS streamS geom hvalid hmactag h16))
        (backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher macS
            kdfS streamS geom hvalid hmactag h16) names) A (backMU1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
            h16) names)
        (backBlockU1 kem cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap kem cipher
            macS kdfS streamS geom hvalid hmactag h16) names) (backViewU1 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid
            hmactag h16) names) km
        (ofVector U)
        (⟨k, cs, s, (r, (r', g))⟩ : KeyedDraw (backAdv1 kem cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16) names A))
            u v)
      = (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h
          => if h = Role.relay then k.2 else cs.2.2.2 h) (encapOf kem k.1.1 s).1 km
          (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
          (Util.Bytes.toVecN geom.headerLength ((relayFront kem default macS kdfS streamS geom
              (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate
              geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector (kem.encodeCiphertext (encapOf
              kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac (ofVector km) (relayFront kem
              default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1
              (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
              (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)))))
          (fun _ => g)
          ({ proc := fun (h : Role) (o : RSOR.Onion geom) out =>
          if h = .sender ∧ o.1 = (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem
              (R.drop (j + 1)) [.surbReply r'.2.2.2]) r'.1 (⟨Array.replicate
              geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) then pure none else pure out } :
        Protocols.RSOR.Patch 𝒮))
        (A.guess cs.2.1 (backOnionX kem cipher macS kdfS streamS geom cs.1.c.req r
        (Nat.zero_lt_of_lt cs.1.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 0 j
        ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac
            (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R
            [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
            j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))) ++
            (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U)
            id))))))).run' cs.2.2.1 := fun g u v => by
    unfold propRunU KeyedDraw.c
    dsimp only
    rw [hV1 g u, hM1 g]
    exact congrArg (fun impl => (simulateQ impl (A.guess cs.2.1
      (backOnionX kem cipher macS kdfS streamS geom cs.1.c.req r
        (Nat.zero_lt_of_lt cs.1.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 0 j
        ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac
            (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R
            [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
            j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))) ++
            (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U)
            id))))))).run' cs.2.2.1) (hback g _)
  simp only [e0, e1]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (headerRelays_fresh kem cipher macS kdfS streamS geom hvalid hmactag h16
      .relay (fun h => if h = Role.relay then k.2 else cs.2.2.2 h) (encapOf kem k.1.1 s).1 km
    (backShift kem geom kdfS streamS (RSOR.path kem R [.surbReply r'.2.2.2])
        (RSOR.path kem R [.surbReply r.2.2.2]) (joinDraw geom r.2.1 r'.1 j ((geom.nrHops -
            R.hops.length) * geom.perHopRoutingInfoLength)) r.2.1 r'.1 j (ofVector U) fwdS fwd')
    (Util.Bytes.toVecN geom.headerLength ((relayFront kem default macS kdfS streamS geom (RSOR.path
        kem R [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
        ByteArray) j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++
        ofVector (macS.mac (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path
        kem R [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
        ByteArray) j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)))))
    ({ proc := fun (h : Role) (o : RSOR.Onion geom) out =>
          if h = .sender ∧ o.1 = (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem
              (R.drop (j + 1)) [.surbReply r'.2.2.2]) r'.1 (⟨Array.replicate
              geom.forwardPayloadLength 0⟩ : ByteArray)
          ((R.drop (j + 1)).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1) then pure none else pure out } :
        Protocols.RSOR.Patch 𝒮)
    (fun m o x ho => by
      obtain ⟨o1, o2⟩ := o
      obtain rfl : o1 = (Util.Bytes.toVecN geom.headerLength ((relayFront kem default macS kdfS
          streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate
          geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector (kem.encodeCiphertext (encapOf kem
          k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac (ofVector km) (relayFront kem default
          macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate
          geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector (kem.encodeCiphertext (encapOf kem
          k.1.1 s).1)) (ofVector U))))) := ho
      exact (hr m x o2).trans (hr m default o2).symm)
    (A.guess cs.2.1 (backOnionX kem cipher macS kdfS streamS geom cs.1.c.req r
        (Nat.zero_lt_of_lt cs.1.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 0 j
        ((relayFront kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector
            (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) ++ ofVector (macS.mac
            (ofVector km) (relayFront kem default macS kdfS streamS geom (RSOR.path kem R
            [.surbReply r.2.2.2]) r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
            j (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))) ++
            (relayBackAt kem default macS kdfS streamS geom (RSOR.path kem R [.surbReply r.2.2.2])
            r.2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) j (ofVector U)
            id)))))) cs.2.2.1) ?_
  exact EvalDistEq.bind_right _ fun g => ((OracleComp.EvalDistEq.bind_const _ _).trans
    (OracleComp.EvalDistEq.bind_const _ _)).symm

end BackRelay

end Cryptlib.Protocols.Sphinx.KEMSphinx
