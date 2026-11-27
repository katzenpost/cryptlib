/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxProp

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.KEMSphinx (keysKs keysTag keysEnc evalDistEq_pair_of_bijective
  prEvent_bind_toReal_sub_le_of_bad)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # TLU→ for NIKE Sphinx: the worlds as views of the hops' keys -/

section Onion

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- The first layer of `q`'s onion, from the forward path's first group element and its hops'
keys. Of the randomness it reads the filler and the backward path's draws. -/
def onionOfKeys (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
      (RSOR.path nike q.fwd [.recipient q.receiver])
      (RSOR.body nike macS kdfS streamS geom q r) with
  | some pkt => split geom pkt
  | none => default

variable {nike geom} in
/-- The randomness with the forward path's secret replaced. -/
def setKey (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) :
    RSOR.Randomness nike geom :=
  ((d, r.1.2), r.2)

/-- **On the sender's own keys it is the sender's onion**, when that onion builds. -/
theorem onionOfKeys_real (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (d : Vector UInt8 nike.privateKeySize) (pkt : ByteArray)
    (h : RSOR.layer nike cipher macS kdfS streamS geom
      (RSOR.path nike q.fwd [.recipient q.receiver]) (setKey r d).1
      (RSOR.body nike macS kdfS streamS geom q (setKey r d)) 0 = .ok pkt) :
    onionOfKeys nike cipher macS kdfS streamS geom q r
        (groupElem nike ((nike.decodePrivateKey d).getD default)
          (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
            (RSOR.path nike q.fwd [.recipient q.receiver])
            (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray 0)
        (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
          (RSOR.path nike q.fwd [.recipient q.receiver])
          (RSOR.path nike q.fwd [.recipient q.receiver]).size)
      = RSOR.form nike cipher macS kdfS streamS geom q (setKey r d) q.first := by
  have hf : RSOR.form nike cipher macS kdfS streamS geom q (setKey r d) q.first
      = split geom pkt := by
    unfold RSOR.form
    rw [show ((q.first : Fin q.fwd.hops.length) : ℕ) = 0 from rfl, h]
  have hp := layer_zero_pktFn nike cipher macS kdfS streamS geom _ _ _ pkt h
    (RSOR.path_keys nike q.fwd [.recipient q.receiver])
  rw [hf]
  unfold onionOfKeys
  rw [show blindElem nike (groupElem nike ((nike.decodePrivateKey d).getD default)
      (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
        (RSOR.path nike q.fwd [.recipient q.receiver])
        (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray 0) _
      = groupElem nike ((nike.decodePrivateKey d).getD default) _ from
    funext fun i => (groupElem_eq_blindElem nike _ _ i).symm]
  dsimp only [setKey, RSOR.clientKey, RSOR.filler, RSOR.body, RSOR.surb] at hp ⊢
  rw [hp]

omit cipher macS kdfS streamS in
/-- Drawing the challenger's randomness and a secret, and putting the secret on the forward
path, is drawing the randomness. -/
theorem evalDistEq_setKey {δ : Type} (K : RSOR.Randomness nike geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness nike geom)
      let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
      K (setKey r d)) =ᵈ ($ᵗ (RSOR.Randomness nike geom) >>= K) := by
  have hg : Function.Bijective (Function.uncurry
      fun (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) =>
        (setKey r d, r.1.1)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun p => (setKey p.1 p.2, p.1.1.1), ?_, ?_⟩ <;>
    · rintro ⟨r, d⟩
      rfl
  have hp := evalDistEq_pair_of_bijective
    (g := fun (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) => (r, d))
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => h, fun p => ⟨p, rfl⟩⟩ (fun p => K p.1)
  exact ((evalDistEq_pair_of_bijective hg
    (fun p : RSOR.Randomness nike geom × Vector UInt8 nike.privateKeySize => K p.1)).trans
      hp.symm).trans
    (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 nike.privateKeySize)) (K r))

/-- The first layer of `q`'s onion, with the tag of hop `j` given. -/
def onionOfTag (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) (j : ℕ) (tag : ByteArray) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray)
      (Function.update (keysTag macS ks.toArray) j fun _ => tag)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
          q.fwd [.recipient q.receiver])
      (RSOR.body nike macS kdfS streamS geom q r) with
  | some pkt => split geom pkt
  | none => default

/-- The bytes of `q`'s onion that hop `j`'s tag covers. -/
def onionMsg (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) (j : ℕ) : ByteArray :=
  hdrMsg geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
    (blindElem nike a ks.toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j

omit cipher macS kdfS streamS geom in
theorem toArray_getElem!_congr {α : Type} [Inhabited α] (l l' : List α) (i : ℕ)
    (h : l[i]? = l'[i]?) : l.toArray[i]! = l'.toArray[i]! := by
  simp [getElem!_def, h]

/-- **The onion uses the replaced hop's MAC key for one tag only.** With the hop's keys replaced,
the onion is the onion built from the replacement without its MAC key and the tag of
`onionMsg` under that key. -/
theorem onionOfKeys_tag (q : RSOR.Request nike geom) (rnd : RSOR.Randomness nike geom)
    (a : ByteArray) (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (r : Rest)
    (km : Vector UInt8 32) (n : ℕ) (hj : j < n) (hjp : j < (RSOR.path nike q.fwd [.recipient
        q.receiver]).size) :
    onionOfKeys nike cipher macS kdfS streamS geom q rnd a
        (hopKeysWith nike kdfS c hops j (restKeys r km) n)
      = onionOfTag nike cipher macS kdfS streamS geom q rnd a
        (hopKeysWith nike kdfS c hops j (restKeys r default) n) j
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (onionMsg nike macS streamS geom q rnd a
            (hopKeysWith nike kdfS c hops j (restKeys r default) n) j))) := by
  have hne : ∀ i, i ≠ j → (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray[i]!
      = (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray[i]! := fun i hi =>
    toArray_getElem!_congr _ _ i ((hopKeysWith_congr nike kdfS c hops j (restKeys r km)
      (restKeys r default) rfl n).2 i hi)
  have hj1 : (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray[j]! = restKeys r km :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j _ n hj)
  have hj0 : (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray[j]!
      = restKeys r default :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j _ n hj)
  have hks : keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray := by
    funext i
    unfold keysKs
    by_cases hi : i = j
    · rw [hi, hj1, hj0]; rfl
    · rw [hne i hi]
  have henc : keysEnc cipher (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = keysEnc cipher (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray := by
    funext i
    unfold keysEnc
    by_cases hi : i = j
    · rw [hi, hj1, hj0]; rfl
    · rw [hne i hi]
  have hge : blindElem nike a (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = blindElem nike a (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray := by
    funext i
    refine blindElem_congr nike a _ _ (fun m => ?_) i
    by_cases hm : m = j
    · rw [hm, hj1, hj0]; rfl
    · rw [hne m hm]
  have htag : keysTag macS (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = Function.update
        (keysTag macS (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray) j
        (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) m)) := by
    funext i
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      unfold keysTag
      rw [hj1]
      rfl
    · rw [Function.update_of_ne hi]
      unfold keysTag
      rw [hne i hi]
  unfold onionOfKeys onionOfTag onionMsg
  rw [hks, henc, hge, htag, nikePktFn_tagAt geom _ _ _ _ _ _ _ j hjp
    (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) m))]

end Onion

section Forward

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- Setting a hop's public key to the one it has changes nothing. -/
theorem modify_publicKey_self (hops : Array PathHop) (j : ℕ) (x : ByteArray) (hj : j < hops.size)
    (hx : hops[j]!.publicKey = x) :
    hops.modify j (fun h => { h with publicKey := x }) = hops := by
  refine Array.ext (by simp) fun i h1 h2 => ?_
  rw [Array.getElem_modify]
  split
  · next hji =>
    subst hji
    rw [getElem!_pos hops j hj] at hx
    subst hx
    rfl
  · rfl

/-- What the adversary's first phase of TLU→ leaves the challenger, with the forward relay
behind the oracle. -/
abbrev ForwardCh (names : Role → Name) (pk : RSOR.Key nike) :=
  PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
      := 𝒮)) .relay names pk

/-- The path of the game: the forward path of the adversary's request, the honest relay at its
place. -/
def forwardPlace (names : Role → Name) {pk : RSOR.Key nike} (ch : ForwardCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 names pk) :
    Array PathHop × ℕ :=
  (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver], ch.c.pos)

/-- World 0: the first layer of the adversary's own onion, from the hops' keys. -/
def forwardView (names : Role → Name) {pk : RSOR.Key nike} (ch : ForwardCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness nike geom) (a : ByteArray) (ks : List HopKeys) :
    Protocols.RSOR.World 𝒮 :=
  { onion := onionOfKeys nike cipher macS kdfS streamS geom ch.c.req r a ks }

/-- The adversary on the key game for world 0. -/
abbrev forwardAdv (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    : KeyAdversary nike :=
  propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
      (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (RSOR.Randomness nike geom)
    ($ᵗ RSOR.Randomness nike geom) (forwardView nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names) A

/-- The draws of world 0. -/
abbrev forwardDraw (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    ProbComp (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness nike geom) A) :=
  propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ ($ᵗ RSOR.Randomness nike geom) A

/-- World 0 of TLU→ as its draws, then the adversary's guess on the first layer of its own
onion, built with the forward path's secret drawn apart. -/
theorem play_false_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    Protocols.RSOR.Property.play names A false
      =ᵈ forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= fun D =>
        (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag
            h16 .relay names D.k.1 D.keys)
            (fun h => if h = .relay then D.k.2 else (D.keys h).2) {})
          (A.guess D.st (RSOR.form nike cipher macS kdfS streamS geom D.c.req
            (setKey D.o D.d) D.c.req.first))).run' D.log := by
  refine (play_evalDistEq_honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names A false).trans ?_
  unfold Protocols.RSOR.Property.playFrom forwardDraw propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun kb =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun out => ?_
  have h := evalDistEq_setKey nike geom fun r =>
    (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
        .relay names k.1 (keysOf nike .relay kb ks))
        (fun h => if h = .relay then k.2 else (keysOf nike .relay kb ks h).2) {})
      (A.guess out.1.2 (RSOR.form nike cipher macS kdfS streamS geom out.1.1.req r
        out.1.1.req.first))).run' out.2
  have hw : Protocols.RSOR.forwardUnlinkable.world out.1.1 false = (do
      let r ← $ᵗ (RSOR.Randomness nike geom)
      return { onion := (RSOR.form nike cipher macS kdfS streamS geom out.1.1.req r
        out.1.1.req.first) }) := by
    simp [Protocols.RSOR.forwardUnlinkable]
    rfl
  refine EvalDistEq.trans ?_ h.symm
  rw [hw]
  simp only [bind_assoc, pure_bind]
  exact EvalDistEq.rfl

/-- The draws that the exact step does not cover: the adversary's onion cannot be built. -/
def forwardBad {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness nike geom) A) :
        Prop :=
  ¬ ∃ pkt, RSOR.layer nike cipher macS kdfS streamS geom
    (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) (setKey D.o D.d).1
    (RSOR.body nike macS kdfS streamS geom D.c.req (setKey D.o D.d)) 0 = .ok pkt

/-- **World 0 of TLU→ is the key game's real world, off the bad draws.** -/
theorem play_false_sub_keyGame_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyGame cipher macS kdfS streamS geom
          (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          true)}[x = true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        A)}[forwardBad nike cipher macS kdfS streamS geom hvalid hmactag h16 D]).toReal := by
  rw [(play_false_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyGame_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ _ _ _ A).prEvent_eq (fun x => x
        = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _ (forwardBad nike cipher macS kdfS streamS geom
      hvalid hmactag h16) (fun D hD => ?_)
    (fun x => x = true)
  obtain ⟨pkt, hpkt⟩ := Classical.not_not.mp hD
  have hpos : (D.c.pos : ℕ) < D.c.req.fwd.hops.length := D.c.pos.isLt
  have hsz := RSOR.path_size nike D.c.req.fwd [.recipient D.c.req.receiver]
  have hkey : (D.c.req.fwd.hops[(D.c.pos : ℕ)]'hpos).key = D.k.1 := congrArg (·.key) D.c.relay
  have hmod := modify_publicKey_self
    (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
    (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1)) (by rw [hsz]; exact hpos) (by
      rw [RSOR.path_getElem! nike _ _ _ hpos]
      exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1))
        hkey)
  unfold propRealOf
  dsimp only [forwardPlace]
  rw [hmod]
  refine Eq.trans ?_ (ite_eq_left (show (D.c.pos : ℕ)
    < (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size by
      rw [hsz]; exact hpos)).symm
  dsimp only [forwardView]
  rw [onionOfKeys_real nike cipher macS kdfS streamS geom D.c.req D.o D.d pkt hpkt]
  rfl

/-- **World 0 of TLU→ with the honest relay's keys replaced.** Playing world 0 with the relay's
keys for the adversary's onion uniform, the hops after it derived from them, and the relay
answering that onion's element with them, changes the adversary's guess by at most the chance
that the onion cannot be built and the advantage of `forwardAdv` in the key game. -/
theorem play_false_sub_ideal_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (($ᵗ (KEMSphinx.KeyTuple × Vector UInt8 32)) >>= fun u =>
          forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= propIdealOf
              nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) _
            (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A u)}[x =
                true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        A)}[forwardBad nike cipher macS kdfS streamS geom hvalid hmactag h16 D]).toReal
      + keyAdvantage cipher macS kdfS streamS geom (forwardAdv nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names A) := by
  have h1 := play_false_sub_keyGame_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
  rw [← (keyGame_false_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) _ _
    (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).prEvent_eq (fun x
        => x = true)]
  unfold keyAdvantage
  exact (abs_sub_le _ _ _).trans (add_le_add h1 le_rfl)

/-- The hops' keys of a draw of world 0, the honest relay's without a MAC key. -/
def forwardKeys0 (names : Role → Name) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness nike geom) A) : List
    HopKeys :=
  drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
      (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) x default

/-- The bytes of the adversary's onion that the honest relay's tag covers. -/
def forwardMsg (names : Role → Name) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x
    : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness nike geom) A) :
    ByteArray :=
  onionMsg nike macS streamS geom x.2.c.req x.2.o
    (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2) (forwardKeys0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names x).toArray 0)
    (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names x) x.2.c.pos

/-- World 0 from the honest relay's tag. -/
def forwardViewT (names : Role → Name) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness nike geom) A)
    (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  { onion := onionOfTag nike cipher macS kdfS streamS geom x.2.c.req x.2.o
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2) (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names x).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names x) x.2.c.pos
          (Util.Bytes.ofVector tag) }

/-- **The MAC step for world 0 of TLU→.** With the honest relay's keys replaced, the relay may
answer the element of the adversary's onion under that onion's header only, at the cost of a
forgery against the MAC and the chance that the bytes its tag covers do not have a header's
length. -/
theorem forward_ideal_sub_only_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let b ← (keyGame cipher macS kdfS streamS geom
          (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) false)}[b =
              true]).toReal
      - (Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) _
          ($ᵗ RSOR.Randomness nike geom) (forwardView nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names) A
          (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names))}[b =
              true]).toReal|
    ≤ (Pr{let b ← (Primitives.MAC.forgeExp macS
          (macForge nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) _ ($ᵗ RSOR.Randomness nike geom) A
            (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (forwardViewT
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[b = true]).toReal
      + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ ($ᵗ RSOR.Randomness nike geom)
          A)}[¬ (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names x).size =
              (2 + nike.publicKeySize + geom.routingInfoLength)]).toReal := by
  refine keyGame_false_sub_gameOnly_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) _ _
    (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A (forwardMsg nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (forwardViewT nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names)
    (fun x => (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names x).size = (2
        + nike.publicKeySize + geom.routingInfoLength)) (fun x hg => hg) (fun x km _ => ?_)
  have hpos : (x.2.c.pos : ℕ) < x.2.c.req.fwd.hops.length := x.2.c.pos.isLt
  have hsz := RSOR.path_size nike x.2.c.req.fwd [.recipient x.2.c.req.receiver]
  unfold drawView forwardView forwardViewT forwardMsg forwardKeys0
  refine congrArg (fun o => ({ onion := o } : Protocols.RSOR.World 𝒮)) ?_
  exact onionOfKeys_tag nike cipher macS kdfS streamS geom x.2.c.req x.2.o _ _ _ _ x.1 km _
    (by
      show (x.2.c.pos : ℕ) < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) x.2).size
      unfold drawHops forwardPlace
      rw [Array.size_modify, hsz]
      exact hpos)
    (by rw [hsz]; exact hpos)

end Forward

end Cryptlib.Protocols.Sphinx.NIKESphinx
