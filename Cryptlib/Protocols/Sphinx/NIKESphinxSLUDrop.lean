/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUTail

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Common (commandsToBytes zeroPadTo toVec32 xorBytes)
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult relayImpl keysKs keysTag keysEnc)
open Cryptlib.Protocols.Sphinx.Common (v0AD)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # SLU← for NIKE Sphinx: a fresh start after the honest relay

On the backward path the reply's next layer starts from the sender's element, blinded by the
hops up to the honest relay; the relay's blinding factor is uniform. A fresh onion over the
rest of the path starts from a fresh element. In a group of prime order the two are the same.
The NIKE type does not say so, so it is a game (`dropGame`): its advantage is a term of the
bound. -/

section Drop

variable (nike : NIKE) (kdfS : KDF)

/-- What a fresh start over the rest of a path gives the hops after hop `j`: the element of a
fresh secret, and those hops' keys from it. -/
def freshTail (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) : ByteArray × List HopKeys :=
  (groupElem nike c (RSOR.hopKeys nike kdfS c (hops.extract (j + 1) hops.size)
      (hops.size - (j + 1))).toArray 0,
    RSOR.hopKeys nike kdfS c (hops.extract (j + 1) hops.size) (hops.size - (j + 1)))

variable {nike} in
/-- **The game of a fresh start after a hop.** What lies after the hop comes from the
adversary's secret through the hop's uniform blinding factor, or from a fresh secret over the
rest of the path. -/
def dropGame (B : BlindAdversary nike) (b : Bool) : ProbComp Bool := do
  let x ← B.pre
  let seed ← $ᵗ (Vector UInt8 32)
  let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
  B.post x.2 (if b then
      freshTail nike kdfS ((nike.decodePrivateKey d).getD default) x.1.2.1 x.1.2.2
    else tailOf nike kdfS x.1.1 x.1.2.1 x.1.2.2 seed)

variable {nike} in
/-- The adversary's advantage in that game. -/
noncomputable def dropAdvantage (B : BlindAdversary nike) : ℝ :=
  |(Pr{let x ← dropGame kdfS B true}[x = true]).toReal
    - (Pr{let x ← dropGame kdfS B false}[x = true]).toReal|

end Drop

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- **The adversary on `dropGame` that world 0 gives.** It draws what world 0 draws besides
the relay's blinding seed, names the sender's secret, the path and the relay's place, and plays
`backPost0` on what it is given. -/
def backDropAdv (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid
    hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) : BlindAdversary nike where
  St := KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
      (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
      (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength))
  pre := do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    return (((drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D), (drawHops nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) D), (drawPos nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)), (U, km, D, u, v))
  post := backPost0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W E

theorem backPost0_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid
    hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (s : KEMSphinx.Keystream geom × Vector UInt8 32 ×
    PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)))
    (tail : ByteArray × List HopKeys) (hp : s.2.2.1.c.pos.val = 0) :
    backPost0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W E s tail = E s := by
  unfold backPost0
  exact ite_eq_left hp

/-- `backPost0_real`, on a draw. -/
theorem backPost0_draw {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid
    hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (D : PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
    (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)
    (U : KEMSphinx.Keystream geom) (km seed : Vector UInt8 32) (u v : Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) (k : ℕ)
    (hk : D.c.pos.val = k + 1) (hT : pathBuilds geom (RSOR.path nike D.c.req.back [.surbReply
        D.o.1.2.2.2]) ((RSOR.path nike D.c.req.back [.surbReply D.o.1.2.2.2]).size - (drawPos nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D))) :
    backPost0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W E (U, km, D, u, v) (tailOf
        nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D) (drawHops nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) D) (drawPos nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) seed)
      = propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) A (backMS0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
          (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (km, seed, D) U u v
          :=
  (backPost0_real nike cipher macS kdfS streamS geom hvalid hmactag h16 W E (km, seed, D) U u v k
      hk hT).symm

/-- **World 0 played from a uniform keystream, over its draws, with `E` at the exit**: the
game's draws, the relay's keystream and MAC key, the two blocks, and the relay's blinding seed
last. -/
def back0E (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid
    hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) : ProbComp Bool :=
  (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names _ (backDraw0 nike geom) A) >>= fun D => do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let seed ← $ᵗ (Vector UInt8 32)
    (if D.c.pos.val = 0 then E (U, km, D, u, v)
      else propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) A (backMS0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
          (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (km, seed, D) U u v)

/-- The draws of world 0 on which the relay is on the backward path and the reply's header
does not build from the relay's layer on. -/
def backBadT {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (D : PropDraw
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) : Prop :=
  ¬ D.c.pos.val = 0 ∧ ¬ pathBuilds geom (RSOR.path nike D.c.req.back [.surbReply D.o.1.2.2.2])
      ((RSOR.path nike D.c.req.back [.surbReply D.o.1.2.2.2]).size - (drawPos nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) D))

set_option maxHeartbeats 2000000 in
/-- **The game's side with the sender's own secret is world 0**, off the draws on which the
reply's header does not build. -/
theorem dropGame_false_sub_le (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary)
    (E : KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
    (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    |(Pr{let b ← (dropGame kdfS (backDropAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
        W names A E) false)}[b = true]).toReal
      - (Pr{let b ← (back0E nike cipher macS kdfS streamS geom hvalid hmactag h16 W names A E)}[b =
          true]).toReal|
    ≤ (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[backBadT nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W D]).toReal := by
  have hB : dropGame kdfS (backDropAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 W
      names A E) false
      =ᵈ ((propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A) >>= fun D => do
        let U ← $ᵗ (KEMSphinx.Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let seed ← $ᵗ (Vector UInt8 32)
        backPost0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W E (U, km, D, u, v)
            (tailOf nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names D) (drawHops nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) (drawPos nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) seed)) :=
            by
    unfold dropGame backDropAdv
    simp only [bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    exact EvalDistEq.bind_right _ fun D => EvalDistEq.bind_right _ fun U =>
      EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun u =>
      EvalDistEq.bind_right _ fun v => EvalDistEq.bind_right _ fun seed =>
      OracleComp.EvalDistEq.bind_const _ _
  rw [hB (fun b => b = true)]
  unfold back0E
  exact KEMSphinx.abs_prEvent_bind_sub_le_bad _ _ _ (fun D => backBadT nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W D) fun D hD => by
    by_cases hp : D.c.pos.val = 0
    · have hx := fun (U : KEMSphinx.Keystream geom) (km : Vector UInt8 32) (u v : Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))
          (tail : ByteArray × List HopKeys) =>
        backPost0_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W (E := E) (U, km, D,
            u, v) tail hp
      simp only [hx, hp, ↓reduceIte]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp
      have hT : pathBuilds geom (RSOR.path nike D.c.req.back [.surbReply D.o.1.2.2.2]) ((RSOR.path
          nike D.c.req.back [.surbReply D.o.1.2.2.2]).size - (drawPos nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)) := not_not.mp
        fun h => hD ⟨hp, h⟩
      have hx := fun (U : KEMSphinx.Keystream geom) (km seed : Vector UInt8 32) (u v : Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength)) =>
        backPost0_draw nike cipher macS kdfS streamS geom hvalid hmactag h16 W (E := E) D U km seed
            u v k hk hT
      simp only [hx, hp, ↓reduceIte]

/-- **World 0 with a fresh start after the relay**: the draws of `back0E` but the relay's blinding
    seed, then a
secret `d0`, and `backPost0` on the fresh start over the rest of the path from `d0`. -/
def back0F (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid
    hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) : ProbComp Bool :=
  (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names _ (backDraw0 nike geom) A) >>= fun D => do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let d0 ← $ᵗ (Vector UInt8 nike.privateKeySize)
    backPost0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W E (U, km, D, u, v)
      (freshTail nike kdfS ((nike.decodePrivateKey d0).getD default) (drawHops nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) (drawPos
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D))

/-- The game's side with a fresh secret is `back0F`. -/
theorem dropGame_true_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS
    streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness
    nike geom × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) → ProbComp Bool) :
    dropGame kdfS (backDropAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 W names A E)
        true =ᵈ back0F nike cipher macS kdfS streamS geom hvalid hmactag h16 W names A E := by
  unfold dropGame backDropAdv back0F
  simp only [bind_assoc, pure_bind, ↓reduceIte]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact EvalDistEq.bind_right _ fun D => EvalDistEq.bind_right _ fun U =>
    EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun u =>
    EvalDistEq.bind_right _ fun v => OracleComp.EvalDistEq.bind_const _ _

/-- **A fresh start after the relay** costs the advantage of `backDropAdv` in `dropGame` and
the chance of a draw on which the reply's header does not build. -/
theorem back0E_sub_back0F_le (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary)
    (E : KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
    (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    |(Pr{let b ← (back0E nike cipher macS kdfS streamS geom hvalid hmactag h16 W names A E)}[b =
        true]).toReal
      - (Pr{let b ← (back0F nike cipher macS kdfS streamS geom hvalid hmactag h16 W names A E)}[b =
          true]).toReal|
    ≤ (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[backBadT nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W D]).toReal
      + dropAdvantage kdfS (backDropAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 W
          names A E) := by
  have h1 := dropGame_false_sub_le nike cipher macS kdfS streamS geom hvalid hmactag h16 W names A E
  rw [abs_sub_comm] at h1
  rw [← (dropGame_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 W names A
      E) (fun b => b = true)]
  refine (abs_sub_le _ (Pr{let b ← (dropGame kdfS (backDropAdv nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names A E) false)}[b = true]).toReal _).trans
    (add_le_add h1 (le_of_eq ?_))
  exact abs_sub_comm _ _

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
