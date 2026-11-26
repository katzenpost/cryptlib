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

/-! ## World 1 as a keyed game around the original's own ciphertext -/

variable [SampleableType kem.Plaintext]

/-- What the challenger of world 1 draws besides the seed of the original's encapsulation to
the honest relay: the relay's header keystream and MAC key for the replacement, the seed of the
replacement's encapsulation, the challenger's randomness, and the two blocks of the ideal
payload cipher. -/
abbrev NextOth := Keystream geom × Vector UInt8 32 × Vector UInt8 32
  × (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
  × Block geom × Block geom

/-- The draw of `NextOth`. -/
def nextDraw : ProbComp (NextOth geom) := do
  let U ← $ᵗ (Keystream geom)
  let km ← $ᵗ (Vector UInt8 32)
  let s ← $ᵗ (Vector UInt8 32)
  let o ← shortDraw geom
  let u ← $ᵗ (Block geom)
  let v ← $ᵗ (Block geom)
  return (U, km, s, o, u, v)

/-- The honest relay's layer of the replacement, from those draws. -/
def nextLayer {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (x : NextOth geom) : ByteArray :=
  shortLayerU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
    (encapOf kem pk.1 x.2.2.1).1 x.2.1 (ofVector x.1) x.2.2.2.2.1

/-- World 1 from those draws and the header keystream `U'` of the original's layer at the
relay: the world shown, the replacement's ciphertext, and the relay's answers to it. -/
def nextViewU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (x : NextOth geom) (U' : ByteArray) :
    Protocols.RSOR.World 𝒮 × kem.Ciphertext × (ByteArray → ProcResult) :=
  ({ onion := RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom
        (RSOR.path kem (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1).fwd
          [.recipient (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1).receiver])
        x.2.2.2.1.2.2.2.1 0 ch.c.pos
        (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x)),
     patch := ch.c.patchWith
        (nextU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1.1
          (RSOR.split geom
            (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x))
          U')
        x.2.2.2.1.1
        (RSOR.split geom
          (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x)) },
    (encapOf kem pk.1 x.2.2.1).1,
    headerHand kem macS geom x.2.1 (ofVector x.1)
      (Util.Bytes.toVecN _
        (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
            (encapOf kem pk.1 x.2.2.1).1 (ofVector x.1)
          ++ ofVector (macS.mac (ofVector x.2.1)
            (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
              (encapOf kem pk.1 x.2.2.1).1 (ofVector x.1)))))
      (fun y => if y = x.2.2.2.2.1 then
          shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
            (ofVector x.1)
        else x.2.2.2.2.2))

/-- World 1 from those draws and the keys `t` of the original's layer at the relay, which it
uses through their keystream only. -/
def nextView {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (x : NextOth geom) (_c : kem.Ciphertext) (t : KeyTuple) :
    Protocols.RSOR.World 𝒮 × kem.Ciphertext × (ByteArray → ProcResult) :=
  nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x (ksOf streamS geom t)

/-- World 1 around the ciphertext of the original's layer at the honest relay. -/
def nextSetup : KeyedSetup kem
    (Protocols.RSOR.World 𝒮 × kem.Ciphertext × (ByteArray → ProcResult)) Bool where
  Ch := ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names
  Oth := NextOth geom
  drawOth _ := nextDraw geom
  view := nextView kem cipher macS kdfS streamS geom hvalid hmactag h16 names
  final _ _ _ _ out := out

/-- The adversary of that keyed game: it answers the replacement's ciphertext itself, and
passes every other packet to the relay. -/
def nextAdv (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    KeyedAdversary (nextSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names) where
  St := A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)
  pre := (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre
  post st w := simulateQ (relayFirst kem w.2.1 w.2.2)
    ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 st.2.2 w.1.patch)
      (A.guess st.1 w.1.onion)).run' st.2.1)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 1000000 in
/-- **The keyed game with the real keys is world 1 from a uniform keystream, after its
draws.** With the keys that the seed `s'` gives, the second phase of `nextAdv` is the run of
world 1 with `s'` as the seed of the original's layer at the honest relay. -/
theorem nextReal_run (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (s' : Vector UInt8 32) (x : NextOth geom) (ct ss : ByteArray)
    (hpk : k.1.1 = kem.derivePublicKey k.2) (hrel : kem.Reliable (kem.stateFromSeed s'))
    (henc : kemEncap kem (ofVector (kem.encodePublicKey k.1.1)) s' = .ok (ct, ss))
    (hsz : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
      (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    simulateQ (procImplK kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
        ((hopKeysPRG kem kdfS).gen (encapOf kem k.1.1 s').2))
      ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post st
        (nextView kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
          (encapOf kem k.1.1 s').1 ((hopKeysPRG kem kdfS).gen (encapOf kem k.1.1 s').2)))
    = forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ (shortDraw geom)
        (shortView kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A
        (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (shortViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
        x.2.1 (ofVector x.1)
        ⟨k, (ch, st), x.2.2.1, (setSeed geom x.2.2.2.1.1 ch.c.pos s', x.2.2.2.1.2)⟩
        x.2.2.2.2.1 x.2.2.2.2.2 := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  obtain ⟨U, km, s, o, u, v⟩ := x
  have hdec : decapOf kem k.2 (encapOf kem k.1.1 s').1 = some (encapOf kem k.1.1 s').2 := by
    have h := decapOf_encapOf kem k.2 s' hrel ct ss (by rw [← hpk]; exact henc)
    rwa [← hpk] at h
  obtain ⟨W, hW⟩ : ∃ W,
      W = nextView kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (U, km, s, o, u, v) (encapOf kem k.1.1 s').1
      ((hopKeysPRG kem kdfS).gen (encapOf kem k.1.1 s').2) := ⟨_, rfl⟩
  rw [procImplK_real kem cipher macS kdfS streamS geom k.2 _ _ hdec, ← hW]
  show simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
    (simulateQ (relayFirst kem W.2.1 W.2.2)
      ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 st.2.2 W.1.patch)
        (A.guess st.1 W.1.onion)).run' st.2.1)) = _
  have hcomp : procImpl kem cipher macS kdfS streamS geom k.2 ∘ₛ relayFirst kem W.2.1 W.2.2
      = relayImpl (relayAns kem cipher macS kdfS streamS geom k.2 W.2.1 W.2.2) :=
    relayImpl_comp_relayFirst kem _ W.2.1 W.2.2
  rw [← QueryImpl.simulateQ_compose, hcomp]
  obtain ⟨Hv, hHv⟩ : ∃ Hv : Vector UInt8 geom.headerLength, Hv = Util.Bytes.toVecN _
      (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)
        ++ ofVector (macS.mac (ofVector km)
          (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)))) := ⟨_, rfl⟩
  have hsize : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)
      ++ ofVector (macS.mac (ofVector km)
        (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)))).size = geom.headerLength := by
    rw [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector, hmactag, hhdr]
    rfl
  have hcar : ∀ pkt : ByteArray, pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
      → carries kem (encapOf kem k.1.1 s).1 pkt = true := by
    intro pkt hp
    refine carries_of_extract kem _ pkt ?_
    have h' := congrArg (fun x : ByteArray => x.extract 2 (2 + kem.ciphertextSize)) hp
    simp only [ByteArray.extract_extract] at h'
    rw [Nat.zero_add, Nat.zero_add, Nat.min_eq_left (by unfold payloadOffset; omega)] at h'
    rw [h', hHv, Cryptlib.Util.Bytes.ofVector_toVecN _ hsize,
      Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsz]; omega)]
    exact relayFrontAt_ct kem cipher macS kdfS streamS geom _ _ _ _ _ _
      (Cryptlib.Util.Bytes.size_ofVector _) hsz
  obtain ⟨skf, hskf⟩ : ∃ skf : Role → kem.PrivateKey,
      skf = fun h => if h = .relay then k.2 else st.2.2 h := ⟨_, rfl⟩
  have hrel' : skf .relay = k.2 := by rw [hskf]; simp
  have hsk : ∀ h, h ≠ Role.relay → st.2.2 h = skf h := fun h hr => by rw [hskf]; simp [hr]
  obtain ⟨Dd, hDd⟩ : ∃ Dd : Block geom → Block geom, Dd = (fun y => if y = u then
          shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o (ofVector U)
        else v) := ⟨_, rfl⟩
  have hW1 : W.2.1 = (encapOf kem k.1.1 s).1 := by rw [hW]; rfl
  have hW2 : W.2.2 = headerHand kem macS geom km (ofVector U) Hv Dd := by
    rw [hW, hHv, hDd]
    rfl
  rw [viaOracle_congr kem cipher macS kdfS streamS geom hvalid hmactag h16 st.2.2 skf hsk, hW1, hW2]
  simp only [StateT.run'_eq, simulateQ_map]
  have hf : ∀ o' : RSOR.Onion geom,
      relayAns kem cipher macS kdfS streamS geom (skf .relay) (encapOf kem k.1.1 s).1
          (headerHand kem macS geom km (ofVector U) Hv Dd) (RSOR.join o')
        = if o'.1 = Hv then procKeysD kem macS geom km (ofVector U)
            (ofVector (Dd o'.2)) (RSOR.join o')
          else relayAns kem cipher macS kdfS streamS geom (skf .relay)
            (encapOf kem k.1.1 s).1 (fun _ => none) (RSOR.join o') := fun o' => by
    rw [hrel']
    exact relayAns_headerHand kem cipher macS kdfS streamS geom hvalid k.2 _ km (ofVector U) Hv Dd
      hcar o'
  have hvo := viaOracle_header kem cipher macS kdfS streamS geom hvalid hmactag h16 skf
    (encapOf kem k.1.1 s).1 (headerHand kem macS geom km (ofVector U) Hv Dd) km (ofVector U)
    Hv Dd hf W.1.patch (A.guess st.1 W.1.onion) st.2.1
  rw [hrel'] at hvo
  rw [hvo]
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hkey : (ch.c.req.fwd.hops[(ch.c.pos : ℕ)]'hpos).key = k.1 := congrArg (·.key) ch.c.relay
  have henc' : kemEncap kem ((RSOR.path kem ch.c.req.fwd
      [.recipient ch.c.req.receiver])[(ch.c.pos : ℕ)]!).publicKey s' = .ok (ct, ss) := by
    rw [RSOR.path_getElem! kem _ _ _ hpos]
    exact (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) s')
      hkey).trans henc
  have hss := (kemEncap_encapOf kem k.1.1 s' ct ss henc).2
  have hon : W.1.onion = (shortViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
        (setSeed geom o.1 ch.c.pos s', o.2) (encapOf kem k.1.1 s).1 km (ofVector U) u).onion := by
    rw [hW]
    rfl
  have hpa : W.1.patch = (shortViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
        (setSeed geom o.1 ch.c.pos s', o.2) (encapOf kem k.1.1 s).1 km (ofVector U) u).patch := by
    rw [hW]
    show ch.c.patchWith (nextU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1
        (RSOR.split geom
          (shortLayerU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 km (ofVector U) u))
        (ksOf streamS geom ((hopKeysPRG kem kdfS).gen (encapOf kem k.1.1 s').2))) o.1
        (RSOR.split geom
          (shortLayerU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 km (ofVector U) u))
      = ch.c.patch (setSeed geom o.1 ch.c.pos s')
        (RSOR.split geom
          (shortLayerU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 km (ofVector U) u))
    unfold Protocols.RSOR.ForwardChallenge.patch
    rw [next_setSeed kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 _ s' ct ss
      henc', hss]
    rfl
  unfold forwardRunU
  rw [hon, hpa, hskf, hDd, hHv]
  rfl

/-- World 1 from a uniform keystream after its draws up to the challenger's randomness `r` for
the original onion. -/
def shortRunG (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (U : Keystream geom) (km : Vector UInt8 32) (k : Key kem × kem.PrivateKey)
    (cs : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1
      × (A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)))
    (s : Vector UInt8 32) (r : RSOR.Randomness geom) : ProbComp Bool := do
  let m ← $ᵗ (RSOR.Msg geom)
  let n ← $ᵗ RSOR.Name
  let r' ← $ᵗ (RSOR.Randomness geom)
  let u ← $ᵗ (Block geom)
  let v ← $ᵗ (Block geom)
  forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ (shortDraw geom)
    (shortView kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A
    (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (shortViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    km (ofVector U) ⟨k, cs, s, (r, m, n, r')⟩ u v

omit [SampleableType kem.Plaintext] in
/-- **World 1 from a uniform keystream, with the seed of the original's layer at the honest
relay drawn apart**, and the draws in the order of the keyed game around that layer's
ciphertext. -/
theorem shortIdeal_evalDistEq (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    PRGScheme.prgIdealExperiment
        (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      =ᵈ ((keygen kem) >>= fun k =>
      (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
      ((shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre
        k.1)) >>= fun cs =>
      ($ᵗ (Vector UInt8 32)) >>= fun s' =>
      ($ᵗ (Keystream geom)) >>= fun U =>
      ($ᵗ (Vector UInt8 32)) >>= fun km =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      shortRunG kem cipher macS kdfS streamS geom hvalid hmactag h16 names A U km k cs s
        (setSeed geom r cs.1.c.pos s')) := by
  let G := shortRunG kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h0 : PRGScheme.prgIdealExperiment
        (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      = (($ᵗ (Keystream geom)) >>= fun U =>
      ($ᵗ (Vector UInt8 32)) >>= fun km =>
      (keygen kem) >>= fun k =>
      (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
      ((shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre
        k.1)) >>= fun cs =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s r) := by
    unfold PRGScheme.prgIdealExperiment shortStreamAdv forwardStreamAdv keyedDraw
    simp only [G, shortRunG, shortDraw, forwardSetupOf, bind_assoc, pure_bind]
    rfl
  rw [h0]
  refine EvalDistEq.trans
    (EvalDistEq.bind_right _ fun U =>
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (Vector UInt8 32)) (keygen kem) fun km k =>
      (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
      ((shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre
        k.1)) >>= fun cs =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s r)) ?_
  refine EvalDistEq.trans
    (EvalDistEq.bind_right _ fun U =>
    (EvalDistEq.bind_right _ fun k =>
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (Vector UInt8 32))
      (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
      ((shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre
        k.1)) fun km cs =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s r))) ?_
  refine EvalDistEq.trans
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (Keystream geom)) (keygen kem) fun U k =>
      (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
      ((shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre
        k.1)) >>= fun cs =>
      ($ᵗ (Vector UInt8 32)) >>= fun km =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s r) ?_
  refine EvalDistEq.trans
    (EvalDistEq.bind_right _ fun k =>
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (Keystream geom))
      (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
      ((shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)) fun U cs =>
      ($ᵗ (Vector UInt8 32)) >>= fun km =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s r)) ?_
  refine EvalDistEq.trans
    (EvalDistEq.bind_right _ fun k =>
    (EvalDistEq.bind_right _ fun cs =>
    (EvalDistEq.bind_right _ fun U =>
    (EvalDistEq.bind_right _ fun km =>
    (EvalDistEq.bind_right _ fun s =>
      ((evalDistEq_setSeed geom cs.1.c.pos
        (lt_of_lt_of_le cs.1.c.pos.isLt cs.1.c.req.fwd.length_le)
      (fun r => G U km k cs s r)).symm)))))) ?_
  refine EvalDistEq.trans
    (EvalDistEq.bind_right _ fun k =>
    (EvalDistEq.bind_right _ fun cs =>
    (EvalDistEq.bind_right _ fun U =>
    (EvalDistEq.bind_right _ fun km =>
    (EvalDistEq.bind_right _ fun s =>
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (RSOR.Randomness geom))
      ($ᵗ (Vector UInt8 32)) fun r s' =>
      G U km k cs s (setSeed geom r cs.1.c.pos s'))))))) ?_
  refine EvalDistEq.trans
    (EvalDistEq.bind_right _ fun k =>
    (EvalDistEq.bind_right _ fun cs =>
    (EvalDistEq.bind_right _ fun U =>
    (EvalDistEq.bind_right _ fun km =>
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (Vector UInt8 32))
      ($ᵗ (Vector UInt8 32)) fun s s' =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s (setSeed geom r cs.1.c.pos s')))))) ?_
  refine EvalDistEq.trans
    (EvalDistEq.bind_right _ fun k =>
    (EvalDistEq.bind_right _ fun cs =>
    (EvalDistEq.bind_right _ fun U =>
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (Vector UInt8 32))
      ($ᵗ (Vector UInt8 32)) fun km s' =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s (setSeed geom r cs.1.c.pos s'))))) ?_
  exact
    (EvalDistEq.bind_right _ fun k =>
    (EvalDistEq.bind_right _ fun cs =>
    (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (Keystream geom))
      ($ᵗ (Vector UInt8 32)) fun U s' =>
      ($ᵗ (Vector UInt8 32)) >>= fun km =>
      ($ᵗ (Vector UInt8 32)) >>= fun s =>
      ($ᵗ (RSOR.Randomness geom)) >>= fun r =>
      G U km k cs s (setSeed geom r cs.1.c.pos s'))))

/-- The draws of the keyed game around the original's ciphertext on which it is world 1: the
honest relay's public key is the one its private key gives, the seed of the original's layer
at the relay does not make the KEM fail, and the replacement's header bytes have a header's
length. -/
def nextGood {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (d : KeyedDraw (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) : Prop :=
  d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    (∃ ct ss, kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss)) ∧
    (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.o.2.2.2.1
      (encapOf kem d.k.1.1 d.o.2.2.1).1 (ofVector d.o.1)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength

/-- **World 1 from a uniform keystream is the keyed game around the original's ciphertext with
the real keys**, up to the chance of a draw that is not good. -/
theorem shortIdeal_sub_nextReal_le
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (PRGScheme.prgIdealExperiment
          (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
    ≤ (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[¬ nextGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            d]).toReal := by
  let F : KeyedDraw (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      → ProbComp Bool := fun d =>
    forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ (shortDraw geom)
      (shortView kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A
      (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (shortViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      d.o.2.1 (ofVector d.o.1)
      ⟨d.k, d.cs, d.o.2.2.1,
        (setSeed geom d.o.2.2.2.1.1 d.cs.1.c.pos d.s, d.o.2.2.2.1.2)⟩
      d.o.2.2.2.2.1 d.o.2.2.2.2.2
  let Gr : KeyedDraw (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      → ProbComp Bool := fun d =>
    simulateQ (procImplK kem cipher macS kdfS streamS geom d.k.2 (encapOf kem d.k.1.1 d.s).1
        ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2))
      ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post d.cs.2
        (nextView kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.o
          (encapOf kem d.k.1.1 d.s).1 ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2)))
  have hL : Pr{let x ← (PRGScheme.prgIdealExperiment
        (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true]
      = Pr{let x ← (keyedDraw cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A) >>= F)}[x = true] := by
    rw [(shortIdeal_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq
      (fun x => x = true)]
    unfold keyedDraw
    simp only [F, nextDraw, shortDraw, shortRunG, nextSetup, bind_assoc, pure_bind]
    rfl
  have hR : Pr{let x ← (keyedReal cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]
      = Pr{let x ← (keyedDraw cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A) >>= Gr)}[x = true] := by
    refine EvalDistEq.prEvent_eq ?_ _
    unfold keyedReal keyedGame keyedDraw
    simp only [Gr, nextSetup, bind_assoc, pure_bind, bind_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)
  rw [hL, hR]
  refine abs_prEvent_bind_sub_le_bad _ F Gr
    (fun d => ¬ nextGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names d)
    fun d hd => ?_
  obtain ⟨hpk, hrel, ⟨ct, ss, henc⟩, hsz⟩ := not_not.mp hd
  exact (nextReal_run kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d.k d.cs.1
    d.cs.2 d.s d.o
    ct ss hpk hrel henc hsz).symm

/-! ## The relay rejects the original's ciphertext -/

/-- Bytes of a header's length without its tag that no accepted packet starts with: their
version is not the packet version. -/
def nextM0 : ByteArray :=
  ⟨#[1, 1]⟩ ++ ⟨Array.replicate (kem.ciphertextSize + geom.routingInfoLength) 0⟩

omit [SampleableType kem.Plaintext] in
/-- A relay that answers under the header of `nextM0` only answers nothing. -/
theorem onlyHeader_nextM0 {pk : Key kem}
    (ch : (nextSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names).Ch pk)
    (o : (nextSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth)
    (c : kem.Ciphertext) (u : KeyTuple) (pkt : ByteArray) :
    onlyHeader cipher macS streamS geom
        (tagged (S := (nextSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names)) macS
          (fun _ _ _ _ => nextM0 kem geom)) ch o c u pkt = none := by
  unfold onlyHeader
  split_ifs with h
  · refine procKeys_version kem cipher macS streamS geom u pkt ?_
    have h2 := congrArg (fun x : ByteArray => x.extract 0 2) h
    simp only [ByteArray.extract_extract] at h2
    rw [Nat.zero_add, Nat.zero_add, Nat.min_eq_left (by unfold payloadOffset; omega)] at h2
    have h3 : (tagged (S := (nextSetup kem cipher macS kdfS streamS geom hvalid hmactag h16
      names)) macS
        (fun _ _ _ _ => nextM0 kem geom) ch o c u).extract 0 2 = ⟨#[1, 1]⟩ := by
      unfold tagged nextM0
      rw [Cryptlib.Util.Bytes.extract_append_of_le _ _
        (by rw [ByteArray.size_append]; exact Nat.le_add_right 2 _)]
      exact Cryptlib.Util.Bytes.extract_append_left ⟨#[1, 1]⟩ _
    rw [h2, h3]
    decide
  · rfl

/-- **The MAC step for the original's ciphertext.** No tag under the keys of the original's
layer at the relay is shown, so with uniform keys the relay may reject every packet that carries
its ciphertext, at the cost of a forgery against the MAC. -/
theorem nextIdeal_sub_reject_le
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
          (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
      - (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
          (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (fun _ _ _ _ _ => none))}[x = true]).toReal|
    ≤ (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        (fun _ _ _ _ => nextM0 kem geom)
        (fun ch o c rest _ => nextView kem cipher macS kdfS streamS geom hvalid hmactag h16
          names ch o c
          (withMAC rest default))))}[x = true]).toReal := by
  have h := keyedIdeal_sub_tagged_le cipher macS kdfS streamS geom
    (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A) hmactag
    (fun _ _ _ _ => nextM0 kem geom)
    (fun ch o c rest _ => nextView kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c
      (withMAC rest default))
    (fun _ => True)
    (fun _ _ _ => by
      unfold nextM0
      rw [ByteArray.size_append]
      show 2 + (Array.replicate _ (0 : UInt8)).size = _
      rw [Array.size_replicate, Nat.add_assoc])
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  have e : (fun {pk : Key kem} => onlyHeader cipher macS streamS geom
        (tagged (S := (nextSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names)) macS
          (fun _ _ _ _ => nextM0 kem geom)) (pk := pk))
      = fun {pk : Key kem} _ _ _ _ _ => none := by
    funext pk ch o c u pkt
    exact onlyHeader_nextM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c u pkt
  rw [e] at h
  simpa using h

/-! ## The keystream of the original's layer at the relay -/

/-- The adversary against the keystream generator that plays world 1 from the header keystream
of the original's layer at the relay, with the relay rejecting that layer's ciphertext. -/
def nextStreamAdv (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    PRGScheme.PRGAdversary (Keystream geom) := fun U' => do
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
    ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)
  let s' ← $ᵗ (Vector UInt8 32)
  let x ← nextDraw geom
  simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
      (fun _ => none))
    ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post cs.2
      (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names cs.1 x (ofVector U')))

omit [SampleableType kem.Plaintext] in
/-- **The stream cipher step for the original's layer.** Once the relay rejects that layer's
ciphertext, the game with uniform keys is the real experiment of the keystream generator for
`nextStreamAdv`. -/
theorem nextReject_eq_prg (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        (fun _ _ _ _ _ => none))}[x = true]
      = Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true] := by
  refine EvalDistEq.prEvent_eq ?_ _
  have hb : ∀ {α β : Type},
      Function.Bijective (Function.uncurry fun (a : α) (b : β) => (a, b)) :=
    fun {_ _} => Function.bijective_id
  let K : Vector UInt8 16 → Vector UInt8 32 → ProbComp Bool := fun iv ke =>
    nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
      ((keystreamPRG streamS geom).gen (ke, iv))
  have h0 : keyedGameH cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        (fun _ _ _ _ _ => none)
      = $ᵗ KeyTuple >>= fun u => K u.2.1 u.2.2.2 := by
    unfold keyedGameH
    simp only [K, nextStreamAdv, nextSetup, nextView, ksOf, keystreamPRG, id_map',
      Cryptlib.Util.Bytes.ofVector_toVecN _ (streamS.keystream_size _ _ _)]
  have hR : PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      = $ᵗ (Vector UInt8 32 × Vector UInt8 16) >>= fun s => K s.2 s.1 := rfl
  rw [h0, hR]
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (kp : Vector UInt8 48)
      (t : Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32) => (kp, t)) hb
    (fun u => K u.2.1 u.2.2.2)).symm ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 48))
    ($ᵗ (Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32) >>= fun t => K t.1 t.2.2)) ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (iv : Vector UInt8 16) (r : Vector UInt8 32 × Vector UInt8 32) => (iv, r)) hb
    (fun t => K t.1 t.2.2)).symm ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun iv =>
    (evalDistEq_pair_of_bijective
      (g := fun (km ke : Vector UInt8 32) => (km, ke)) hb (fun r => K iv r.2)).symm) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun iv =>
    OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32))
      ($ᵗ (Vector UInt8 32) >>= fun ke => K iv ke)) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ fun iv ke => K iv ke) ?_
  exact evalDistEq_pair_of_bijective
    (g := fun (ke : Vector UInt8 32) (iv : Vector UInt8 16) => (ke, iv)) hb
    (fun s => K s.2 s.1)

/-! ## World 1 with both keystreams uniform -/

/-- **The original's next layer from a uniform keystream.** World 1 from a uniform keystream
differs from world 1 with the keystream of the original's layer at the relay uniform too, and
that layer's ciphertext rejected, by at most: the chance of a draw that is not good; the cost
of replacing that layer's keys; a forgery against the MAC; and the keystream generator's
advantage. -/
theorem short_next_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (PRGScheme.prgIdealExperiment
          (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
    ≤ (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[¬ nextGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            d]).toReal
      + keyedCost cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
        (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        (fun _ _ _ _ => nextM0 kem geom)
        (fun ch o c rest _ => nextView kem cipher macS kdfS streamS geom hvalid hmactag h16
          names ch o c
          (withMAC rest default))))}[x = true]).toReal
      + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
            (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment
            (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal| := by
  have h1 := shortIdeal_sub_nextReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h2 := keyedChain_le cipher macS kdfS streamS geom
    (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
  have h3 := nextIdeal_sub_reject_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  rw [congrArg ENNReal.toReal
    (nextReject_eq_prg kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)] at h3
  have t1 := abs_sub_le
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
      (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
  have t2 := abs_sub_le
    (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
      (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
  have t3 := abs_sub_le
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
      (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
  linarith

/-! ## The bound so far -/

/-- **TLU→ for KEM Sphinx, down to two games with every keystream uniform.** As
`forwardUnlinkable_le_uniform`, with the keys of the original's layer at the honest relay
replaced in world 1 too: the cost of replacing them, a forgery against the MAC, the keystream
generator's advantage and the bad draws are added, and the distance left is between world 0
from a uniform keystream and world 1 with both keystreams uniform. -/
theorem forwardUnlinkable_le_next
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ((Protocols.RSOR.forwardUnlinkable (S := 𝒮)).advantage names A).toReal
      ≤ (Pr{let d ← (forwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A)}[forwardBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (forwardDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names _
          (shortDraw geom)
          A)}[shortBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + keyedCost cipher macS kdfS streamS geom
          (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + keyedCost cipher macS kdfS streamS geom
          (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
            (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
            (forwardM kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (forwardViewT kem cipher macS kdfS streamS geom hvalid hmactag h16
              names)))}[x = true]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ forwardGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
            (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
            (shortM kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (shortViewT kem cipher macS kdfS streamS geom hvalid hmactag h16
              names)))}[x = true]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ shortGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            true)}[x = true]).toReal
          - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            false)}[x = true]).toReal|
        + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (shortGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            true)}[x = true]).toReal
          - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (shortGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            false)}[x = true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
            (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
            (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
            (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
            (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal|
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ forwardGoodP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ shortGoodP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ nextGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                d]).toReal
        + keyedCost cipher macS kdfS streamS geom
          (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
          (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (fun _ _ _ _ => nextM0 kem geom)
          (fun ch o c rest _ => nextView kem cipher macS kdfS streamS geom hvalid hmactag h16
            names ch o c
            (withMAC rest default))))}[x = true]).toReal
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
              (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
              (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                A))}[x = true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgIdealExperiment
              (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
              (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                A))}[x = true]).toReal| := by
  have h := forwardUnlinkable_le_uniform kem cipher macS kdfS streamS geom hvalid hmactag h16
    names A
  have s1 := short_next_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have t1 := abs_sub_le
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
  linarith

end ForwardNext

end Cryptlib.Protocols.Sphinx.KEMSphinx
