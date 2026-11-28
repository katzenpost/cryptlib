/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUFn

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

/-! # SLU← for NIKE Sphinx: world 0 on the backward path, from what lies after the relay

World 0 played from a uniform keystream at the honest relay reads the hops after the relay
through the element that reaches the next hop and those hops' keys (`tailOf`). -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

omit cipher macS kdfS streamS geom hvalid hmactag h16 in
/-- The sender's first element does not read the hops' keys. -/
theorem groupElem_zero (c : nike.PrivateKey) (K K' : Array HopKeys) :
    groupElem nike c K 0 = groupElem nike c K' 0 :=
  rfl

omit cipher hvalid hmactag h16 in
/-- **The hops' functions, split at a hop.** With hop `j`'s blinding factor from `seed`, the
keystreams, tagging functions and elements of a path are those of the hops up to `j`, whatever
hop `j`'s other keys, spliced with those of what lies after hop `j` (`tailOf`). -/
theorem tail_splice (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (seed : Vector UInt8 32)
    (t t0 : HopKeys) (ht : t.blindingFactor = blindingFactorPrivKey seed) (hj : j < hops.size)
    (U : ByteArray) (f : ByteArray → ByteArray) (a : ByteArray)
    (ha : a = groupElem nike c (hopKeysWith nike kdfS c hops j t hops.size).toArray 0) :
    spliceAt j (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c hops j t0
        hops.size).toArray) j U)
        (keysKs geom streamS (tailOf nike kdfS c hops j seed).2.toArray)
      = Function.update (keysKs geom streamS (hopKeysWith nike kdfS c hops j t hops.size).toArray)
          j U
    ∧ spliceAt j (Function.update (keysTag macS (hopKeysWith nike kdfS c hops j t0
        hops.size).toArray) j f)
        (keysTag macS (tailOf nike kdfS c hops j seed).2.toArray)
      = Function.update (keysTag macS (hopKeysWith nike kdfS c hops j t hops.size).toArray) j f
    ∧ spliceAt j (blindElem nike a (hopKeysWith nike kdfS c hops j t0 hops.size).toArray)
        (blindElem nike (tailOf nike kdfS c hops j seed).1
          (tailOf nike kdfS c hops j seed).2.toArray)
      = blindElem nike a (hopKeysWith nike kdfS c hops j t hops.size).toArray := by
  have hfront : ∀ i, i < j → (hopKeysWith nike kdfS c hops j t0 hops.size).toArray[i]! =
      (hopKeysWith nike kdfS c hops j t hops.size).toArray[i]! := fun i hi =>
    hopKeysWith_getElem!_lt nike kdfS c hops j t0 t hops.size i hi (le_of_lt hj)
  rw [tailOf_hopKeysWith nike kdfS c hops j seed t hj ht]
  refine ⟨?_, ?_, ?_⟩
  · rw [spliceAt_congr_le j _ (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c hops j
      t hops.size).toArray) j U) _
      (fun i hi => by
        by_cases hi' : i = j
        · rw [hi', Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hi', Function.update_of_ne hi']
          unfold keysKs
          rw [hfront i (by omega)])]
    exact spliceAt_drop (keysKs geom streamS) (fun K K' i i' h => by
      unfold keysKs
      rw [h]) (hopKeysWith nike kdfS c hops j t hops.size) j _ (fun i hi => Function.update_of_ne
          (by omega) _ _)
  · rw [spliceAt_congr_le j _ (Function.update (keysTag macS (hopKeysWith nike kdfS c hops j t
      hops.size).toArray) j f) _
      (fun i hi => by
        by_cases hi' : i = j
        · rw [hi', Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hi', Function.update_of_ne hi']
          unfold keysTag
          rw [hfront i (by omega)])]
    exact spliceAt_drop (keysTag macS) (fun K K' i i' h => by
      unfold keysTag
      rw [h]) (hopKeysWith nike kdfS c hops j t hops.size) j _ (fun i hi => Function.update_of_ne
          (by omega) _ _)
  · rw [spliceAt_congr_le j _ (blindElem nike a (hopKeysWith nike kdfS c hops j t
      hops.size).toArray) _ (fun i hi =>
        blindElem_congr_lt nike a _ _ i (fun n hn => by rw [hfront n (by omega)])), ha,
      groupElem_eq_blindElem nike c (hopKeysWith nike kdfS c hops j t hops.size).toArray (j + 1)]
    exact spliceAt_blindElem nike _ (hopKeysWith nike kdfS c hops j t hops.size) j

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- **What world 0 does with the hops after the relay.** On the draws of world 0 besides the
relay's blinding seed (its keystream and MAC key, the game's draws, the two blocks) and on what
lies after the relay, `tail`: on the backward path, when the reply's header builds from the
relay's layer on, the game on the hops' functions, those after the relay from `tail`; at the
exit, `E`. -/
def backPost0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid
    hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool)
    (s : KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom
        × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength))) (tail : ByteArray × List HopKeys) : ProbComp Bool :=
  if s.2.2.1.c.pos.val = 0 then E s
  else if pathBuilds geom (RSOR.path nike s.2.2.1.c.req.back [.surbReply s.2.2.1.o.1.2.2.2])
      ((RSOR.path nike s.2.2.1.c.req.back [.surbReply s.2.2.1.o.1.2.2.2]).size - (drawPos nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1)) then
    backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((s.2.1, default, s.2.2.1) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) (fun y => if y = s.2.2.2.1 then s.2.2.1.o.2 else s.2.2.2.2)
      (spliceAt (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) s.2.2.1) (Function.update (keysKs geom streamS
          (hopKeysWith nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names s.2.2.1) (drawHops nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1) (drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1)
          (restKeys ((default, default, default), default) default) (drawHops nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1).size).toArray)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) s.2.2.1)
        (Util.Bytes.ofVector s.1)) (keysKs geom streamS tail.2.toArray))
      (spliceAt (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) s.2.2.1) (Function.update (keysTag macS (hopKeysWith
          nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names s.2.2.1) (drawHops nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1) (drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1)
          (restKeys ((default, default, default), default) default) (drawHops nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1).size).toArray)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) s.2.2.1) (fun m => Util.Bytes.ofVector (macS.mac
          (Util.Bytes.ofVector s.2.1) m)))
        (keysTag macS tail.2.toArray))
      (spliceAt (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) s.2.2.1) (blindElem nike (groupElem nike (drawKey nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names s.2.2.1) (hopKeysWith nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names s.2.2.1) (drawHops nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) s.2.2.1) (restKeys ((default, default, default),
          default) default) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) s.2.2.1).size).toArray 0) (hopKeysWith nike kdfS
          (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names s.2.2.1) (drawHops nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1) (drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1)
          (restKeys ((default, default, default), default) default) (drawHops nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) s.2.2.1).size).toArray)
        (blindElem nike tail.1 tail.2.toArray))
  else pure false

set_option maxHeartbeats 4000000 in
/-- **Handed the path's own tail, that is world 0** on the backward path, when the reply's
header builds from the relay's layer on. -/
theorem backPost0_real {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary}
    (E : KEMSphinx.Keystream geom × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom
        × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength)) → ProbComp Bool) (x : PropStrX nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike
        geom × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) (U :
        KEMSphinx.Keystream geom) (u v : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))
    (k : ℕ) (hk : x.2.2.c.pos.val = k + 1)
    (hT : pathBuilds geom (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])
        ((RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]).size - (drawPos nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2))) :
    propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A
        (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backPlainS0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W) (backViewS0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) x U u v
      = backPost0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W E (U, x.1, x.2.2, u, v)
        (tailOf nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawHops nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) (drawPos nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)
            x.2.1) := by
  have hlt : x.2.2.c.pos.val < x.2.2.c.req.back.hops.length := x.2.2.c.pos.isLt
  have hn : k + 1 < x.2.2.c.req.back.hops.length := by omega
  have hpos := backPos_lt nike cipher macS kdfS streamS geom hvalid hmactag h16 W x.2.2
  have hne : ¬ x.2.2.c.pos.val = 0 := by omega
  have hsp := tail_splice nike macS kdfS streamS geom (drawKey nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawHops nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) (drawPos
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) x.2.1
      (restKeys ((default, default, default), x.2.1) default) (restKeys ((default, default,
      default), default) default) rfl
    hpos (Util.Bytes.ofVector U) (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1)
        m)) (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.2) (hopKeysWith nike kdfS (drawKey nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names x.2.2) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) (drawPos nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) x.2.2) (restKeys ((default, default, default),
        default) default) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2).size).toArray 0)
    (groupElem_zero nike _ _ _)
  have hA : groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.2) (hopKeysWith nike kdfS (drawKey nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x.2.2) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
      geom hvalid hmactag h16 W names) x.2.2) (restKeys ((default, default, default), x.2.1)
      default) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2).size).toArray 0 = groupElem nike (drawKey nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2)
      (hopKeysWith nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawHops nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) (drawPos nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) (restKeys ((default,
      default, default), default) default) (drawHops nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2.2).size).toArray 0 :=
    groupElem_zero nike _ _ _
  have hx : ∀ (dec : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Vector
      UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) (ks : ℕ → ByteArray) (tag : ℕ →
      ByteArray → ByteArray)
      (ge : ℕ → ByteArray),
      backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x dec ks tag ge =
          backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((x.1, default, x.2.2)
          : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) dec ks tag ge :=
    fun _ _ _ _ => rfl
  rw [backRun0_fnMac nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U u v k hk hn hT]
  unfold backPost0
  refine Eq.trans ?_ (ite_eq_right hne).symm
  refine Eq.trans ?_ (ite_eq_left hT).symm
  rw [hx]
  unfold drawKeys propPayRest propStrPay
  dsimp only
  rw [hA, ← hsp.1, ← hsp.2.1, ← hsp.2.2]

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
