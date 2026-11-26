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

/-- World 1 from those draws and the keys `t` of the original's layer at the relay: the world
shown, the replacement's ciphertext, and the relay's answers to it. The world uses `t` through
its keystream in the original's next layer only. -/
def nextView {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (x : NextOth geom) (_c : kem.Ciphertext) (t : KeyTuple) :
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
          (ksOf streamS geom t))
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
  obtain ⟨W, hW⟩ : ∃ W, W = nextView kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      ch
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

end ForwardNext

end Cryptlib.Protocols.Sphinx.KEMSphinx
