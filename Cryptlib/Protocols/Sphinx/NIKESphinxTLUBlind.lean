/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLURelay

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

/-! # The last comparison of TLU→ for NIKE Sphinx: the blinding adversary

The adversary on the blinding game that world 0 gives, its two sides as games over world 0's
draws, and the element that reaches the relay in the two worlds. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-! ## The blinding adversary of world 0 -/

/-- **What world 0 does with the hops after the relay.** On the draws of world 0 besides the
relay's blinding seed (the relay's keystream and MAC key, the game's draws, the two blocks) and
on what lies after the relay, `tail`: before the end of a path whose header builds, the game
from the hops' functions, those after the relay from `tail`; at the end of the path, `E`. -/
def blindPost (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength)) → ProbComp Bool) (s : KEMSphinx.Keystream geom × Vector UInt8
        32 × (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) (tail : ByteArray × List HopKeys) : ProbComp Bool :=
  if (s.2.2.1.c.pos : ℕ) + 1 < s.2.2.1.c.req.fwd.hops.length then
    if pathBuilds geom (RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver])
        ((RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]).size -
        s.2.2.1.c.pos) then
      fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A ((forwardPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A
          := A) (s.2.1, default, s.2.2.1)))
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (A := A) (s.2.1, default, s.2.2.1)))
        s.2.2.1.st s.2.2.1.log s.2.2.1.c.req s.2.2.1.o s.2.2.1.c.pos s.2.1 s.2.2.2.1 s.2.2.2.2
        (spliceAt s.2.2.1.c.pos (Function.update (keysKs geom streamS (hopKeysWith nike kdfS
            ((nike.decodePrivateKey s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd
            [.recipient s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default,
            default), default) default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray)
          s.2.2.1.c.pos (Util.Bytes.ofVector s.1)) (keysKs geom streamS tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray) (keysTag macS tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (keysEnc cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray) (keysEnc cipher tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey s.2.2.1.d).getD
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver])
            s.2.2.1.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
            s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]).size).toArray 0) (hopKeysWith
            nike kdfS ((nike.decodePrivateKey s.2.2.1.d).getD default) (RSOR.path nike
            s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys
            ((default, default, default), default) default) (RSOR.path nike s.2.2.1.c.req.fwd
            [.recipient s.2.2.1.c.req.receiver]).size).toArray)
          (blindElem nike tail.1 tail.2.toArray))
    else pure false
  else E s

/-- **The adversary on the blinding game that world 0 gives.** It draws what world 0 draws
besides the relay's blinding seed, names the sender's secret, the path and the relay's place,
and plays `blindPost` on what it is given. -/
def blindAdv (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength)) → ProbComp Bool) : BlindAdversary nike where
  St := KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
      (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength))
  pre := do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let D ← forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) A
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    return (((nike.decodePrivateKey D.d).getD default,
      RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver], D.c.pos), (U, km, D, u, v))
  post := blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E

/-- The hops' keys of world 0 after its steps: the sender's, the honest relay's replaced by
its blinding seed alone. -/
theorem fwd0_keys (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A) :
    forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) x) default)
      = hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
        (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) x.2.2.c.pos
        (restKeys ((default, default, default), x.2.1) default)
        (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]).size := by
  have hpos : (x.2.2.c.pos : ℕ) < x.2.2.c.req.fwd.hops.length := x.2.2.c.pos.isLt
  have hsz := RSOR.path_size nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]
  have hkey : (x.2.2.c.req.fwd.hops[(x.2.2.c.pos : ℕ)]'hpos).key = x.2.2.k.1 :=
    congrArg (·.key) x.2.2.c.relay
  have hpk : ((RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver])[
        (x.2.2.c.pos : ℕ)]!).publicKey
      = Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey
  have hmod := modify_publicKey_self
    (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) x.2.2.c.pos
    (Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1)) (by rw [hsz]; exact hpos) hpk
  show hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
    ((RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]).modify x.2.2.c.pos
      fun h => { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) })
    x.2.2.c.pos (restKeys ((default, default, default), x.2.1) default) _ = _
  rw [hmod]
  exact congrArg (hopKeysWith nike kdfS _ _ _ _) (congrArg Array.size hmod)

/-- The hops' keys of world 1 after its first steps: the sender's for the replacement's path,
which is the original's cut after the honest relay, the relay's replaced likewise. -/
theorem fwd1_keys (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A) :
    forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) x) default)
      = hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
        (RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []) x.2.2.c.pos
        (restKeys ((default, default, default), x.2.1) default)
        (RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []).size := by
  have hpos : (x.2.2.c.pos : ℕ) < x.2.2.c.req.fwd.hops.length := x.2.2.c.pos.isLt
  have hpos1 : (x.2.2.c.pos : ℕ) < (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)).hops.length := by
    show (x.2.2.c.pos : ℕ) < (List.take ((x.2.2.c.pos : ℕ) + 1) x.2.2.c.req.fwd.hops).length
    rw [List.length_take]
    exact lt_min (Nat.lt_succ_self _) hpos
  have hsz := RSOR.path_size nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []
  have hkey : ((x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)).hops[(x.2.2.c.pos : ℕ)]'hpos1).key
      = x.2.2.k.1 := by
    show ((List.take ((x.2.2.c.pos : ℕ) + 1) x.2.2.c.req.fwd.hops)[(x.2.2.c.pos : ℕ)]'hpos1).key
      = _
    have h0 : (x.2.2.c.req.fwd.hops[(x.2.2.c.pos : ℕ)]'hpos).key = x.2.2.k.1 :=
      congrArg (·.key) x.2.2.c.relay
    have h1 : (List.take ((x.2.2.c.pos : ℕ) + 1) x.2.2.c.req.fwd.hops)[(x.2.2.c.pos : ℕ)]'hpos1
        = x.2.2.c.req.fwd.hops[(x.2.2.c.pos : ℕ)]'hpos := List.getElem_take
    exact (congrArg Protocols.RSOR.Hop.key h1).trans h0
  have hpk : ((RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) [])[
        (x.2.2.c.pos : ℕ)]!).publicKey
      = Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos1]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey
  have hmod := modify_publicKey_self
    (RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []) x.2.2.c.pos
    (Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1)) (by rw [hsz]; exact hpos1) hpk
  show hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
    ((RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []).modify x.2.2.c.pos
      fun h => { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) })
    x.2.2.c.pos (restKeys ((default, default, default), x.2.1) default) _ = _
  rw [hmod]
  exact congrArg (hopKeysWith nike kdfS _ _ _ _) (congrArg Array.size hmod)

set_option maxHeartbeats 4000000 in
/-- **Handed the path's own tail, the blinding adversary plays world 0**, on a draw before the
end of a path whose header builds. -/
theorem blindPost_real (names : Role → Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (E : KEMSphinx.Keystream geom ×
        Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) → ProbComp Bool)
    (U : KEMSphinx.Keystream geom) (km seed : Vector UInt8 32) (D : PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) (u v : Vector
        UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) ((RSOR.path
        nike D.c.req.fwd [.recipient D.c.req.receiver]).size - D.c.pos)) :
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, D, u, v)
        (tailOf nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd
        [.recipient D.c.req.receiver]) D.c.pos seed)
      = strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (km, seed, D) U u v := by
  have hpos : (D.c.pos : ℕ) < (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size :=
    lt_of_lt_of_eq D.c.pos.isLt (RSOR.path_size nike D.c.req.fwd _).symm
  have hlt : ∀ i, i < (D.c.pos : ℕ) → (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD
      default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys
      ((default, default, default), seed) default) (RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]).size).toArray[i]! = (hopKeysWith nike kdfS ((nike.decodePrivateKey
      D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
      (restKeys ((default, default, default), default) default) (RSOR.path nike D.c.req.fwd
      [.recipient D.c.req.receiver]).size).toArray[i]! := fun i hi =>
    hopKeysWith_getElem!_lt nike kdfS _ _ _ _ _ _ i hi hpos.le
  have hat : ∀ s : HopKeys, (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD default)
      (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos s (RSOR.path nike
      D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray[
      (D.c.pos : ℕ)]! = s := fun s =>
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hpos)
  have e1 : ∀ i, i ≤ (D.c.pos : ℕ) →
      Function.update (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD
          default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys
          ((default, default, default), seed) default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]).size).toArray) D.c.pos (Util.Bytes.ofVector U) i
        = Function.update (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
            D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
            (restKeys ((default, default, default), default) default) (RSOR.path nike D.c.req.fwd
            [.recipient D.c.req.receiver]).size).toArray) D.c.pos (Util.Bytes.ofVector U) i :=
    fun i hi => by
      by_cases he : i = (D.c.pos : ℕ)
      · rw [he, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne he, Function.update_of_ne he]
        unfold keysKs
        rw [hlt i (by omega)]
  have e2 : ∀ i, i ≤ (D.c.pos : ℕ) → keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
      D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
      (restKeys ((default, default, default), seed) default) (RSOR.path nike D.c.req.fwd
      [.recipient D.c.req.receiver]).size).toArray i = keysTag macS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray i :=
    fun i hi => by
      funext m
      unfold keysTag
      by_cases he : i = (D.c.pos : ℕ)
      · rw [he, hat, hat]
        rfl
      · rw [hlt i (by omega)]
  have e3 : ∀ i, i ≤ (D.c.pos : ℕ) →
      keysEnc cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path
          nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default,
          default), seed) default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]).size).toArray i = keysEnc cipher (hopKeysWith nike kdfS
          ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), default) default)
          (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray i := fun i hi =>
          by
    funext m
    unfold keysEnc
    by_cases he : i = (D.c.pos : ℕ)
    · rw [he, hat, hat]
      rfl
    · rw [hlt i (by omega)]
  have e4 : ∀ i, i ≤ (D.c.pos : ℕ) →
      blindElem nike (groupElem nike ((nike.decodePrivateKey D.d).getD default) (hopKeysWith nike
          kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), seed) default)
          (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray 0) (hopKeysWith
          nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd
          [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), seed)
          default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray i
        = blindElem nike (groupElem nike ((nike.decodePrivateKey D.d).getD default) (hopKeysWith
            nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd
            [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray 0)
            (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default,
            default), default) default) (RSOR.path nike D.c.req.fwd [.recipient
            D.c.req.receiver]).size).toArray i := fun i hi =>
    blindElem_congr_lt nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey
      ((nike.decodePrivateKey D.d).getD default)))) _ _ i fun n hn =>
      congrArg HopKeys.blindingFactor (hlt n (by omega))
  have hrun := strRun_fwd0_fn nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (km,
      seed, D) U u v hj hT
  rw [fwd0_keys nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (km, seed, D)] at hrun
  have htail := fnRun_tailOf nike cipher macS kdfS streamS geom hvalid hmactag h16 A
    ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (A := A) (km, seed, D)))
    ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (A := A) (km, seed, D)))
    D.st D.log D.c.req D.o D.c.pos km u v ((nike.decodePrivateKey D.d).getD default) (RSOR.path
        nike D.c.req.fwd [.recipient D.c.req.receiver]) seed (restKeys ((default, default,
        default), seed) default) (Util.Bytes.ofVector U)
    hpos rfl
  rw [spliceAt_congr_le _ _ _ _ e1, spliceAt_congr_le _ _ _ _ e2, spliceAt_congr_le _ _ _ _ e3,
    spliceAt_congr_le _ _ _ _ e4] at htail
  unfold blindPost
  rw [ite_eq_left hj, ite_eq_left hT]
  exact (hrun.trans htail).symm

/-- At the end of the path the blinding adversary plays `E`. -/
theorem blindPost_exit (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (s : KEMSphinx.Keystream geom × Vector UInt8 32 ×
    (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS streamS
    geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)))
    (tail : ByteArray × List HopKeys)
    (hj : ¬ (s.2.2.1.c.pos : ℕ) + 1 < s.2.2.1.c.req.fwd.hops.length) :
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E s tail = E s := by
  unfold blindPost
  exact ite_eq_right hj

/-- **World 0 over its draws, with `E` at the end of the path**: the game's draws, the relay's
keystream and MAC key, the two blocks, and the relay's blinding seed last. -/
def world0E (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
    macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength
    + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) : ProbComp Bool :=
  forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) A >>= fun D => do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let seed ← $ᵗ (Vector UInt8 32)
    if (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length then
      strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (km, seed, D) U u v
    else E (U, km, D, u, v)

/-- The draws of world 0 on which the relay is before the end of a path whose header does not
build. -/
def fwdBad0 {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A) : Prop :=
  (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length ∧ ¬ pathBuilds geom (RSOR.path nike D.c.req.fwd
      [.recipient D.c.req.receiver]) ((RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]).size - D.c.pos)

set_option maxHeartbeats 2000000 in
/-- **The blinding game's side with the sender's own secret is world 0**, off the draws on
which the path's header does not build. -/
theorem blindGame_false_sub_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    |(Pr{let b ← (blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A E) false)}[b = true]).toReal
      - (Pr{let b ← (world0E nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)}[b =
          true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[fwdBad0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 D]).toReal := by
  have hB : blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
      E) false
      =ᵈ (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A >>= fun D => do
        let U ← $ᵗ (KEMSphinx.Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let seed ← $ᵗ (Vector UInt8 32)
        blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, D, u, v)
            (tailOf nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos seed)) := by
    unfold blindGame blindAdv
    simp only [bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    exact EvalDistEq.bind_right _ fun D => EvalDistEq.bind_right _ fun U =>
      EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun u =>
      EvalDistEq.bind_right _ fun v => EvalDistEq.bind_right _ fun seed =>
      OracleComp.EvalDistEq.bind_const _ _
  rw [hB (fun b => b = true)]
  unfold world0E
  exact KEMSphinx.abs_prEvent_bind_sub_le_bad _ _ _ (fun D => fwdBad0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 D) fun D hD => by
    by_cases hj : (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length
    · have hT : pathBuilds geom (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver])
        ((RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size - D.c.pos) := not_not.mp
        fun h => hD ⟨hj, h⟩
      simp only [blindPost_real nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E _ _
          _ D _ _ hj hT, hj, ↓reduceIte]
    · have hx := fun (U : KEMSphinx.Keystream geom) (km : Vector UInt8 32)
          (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
          (tail : ByteArray × List HopKeys) =>
        blindPost_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E
          (U, km, D, u, v) tail hj
      simp only [hx, hj, ↓reduceIte]

/-- **World 0 with the hops after the relay from an independent secret**: the draws of
`world0E`, then a secret `d0`, and the blinding adversary's game on the tail of the path from
`d0`. -/
def world0B (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
    macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength
    + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) : ProbComp Bool :=
  forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) A >>= fun D => do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let seed ← $ᵗ (Vector UInt8 32)
    let d0 ← $ᵗ (Vector UInt8 nike.privateKeySize)
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, D, u, v)
      (tailOf nike kdfS ((nike.decodePrivateKey d0).getD default) (RSOR.path nike D.c.req.fwd
          [.recipient D.c.req.receiver]) D.c.pos seed)

/-- The blinding game's side with an independent secret is `world0B`. -/
theorem blindGame_true_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E) true
        =ᵈ world0B nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E := by
  unfold blindGame blindAdv world0B
  simp only [bind_assoc, pure_bind, ↓reduceIte]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- **Replacing the secret behind the hops after the relay** costs the blinding advantage of
`blindAdv` and the chance of a draw on which the path's header does not build. -/
theorem world0E_sub_world0B_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    |(Pr{let b ← (world0E nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)}[b =
        true]).toReal
      - (Pr{let b ← (world0B nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)}[b =
          true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[fwdBad0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 D]).toReal
      + blindAdvantage kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
          E) := by
  have h1 := blindGame_false_sub_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E
  rw [abs_sub_comm] at h1
  rw [← (blindGame_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)
      (fun b => b = true)]
  refine (abs_sub_le _ (Pr{let b ← (blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names A E)
    false)}[b = true]).toReal _).trans (add_le_add h1 (le_of_eq ?_))
  exact abs_sub_comm _ _

/-- A draw of world 1 as a draw of world 0: the same game draws, the original's randomness. -/
def toDraw0 {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A) : PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A :=
  ⟨D.k, D.keys, D.c, D.st, D.log, D.o.1, D.d⟩

/-- **The element that reaches the relay is the same in the two worlds**: the replacement's
path is the original's up to the relay, and the sender's secret is the same. -/
theorem drawElem_fwd1 (names : Role → Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (D : PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) :
    drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names)) D
      = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names)) (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          D) := by
  have hpos : (D.c.pos : ℕ) < D.c.req.fwd.hops.length := D.c.pos.isLt
  have hpos1 : (D.c.pos : ℕ) < (D.c.req.fwd.take (D.c.pos + 1)).hops.length := by
    show (D.c.pos : ℕ) < (List.take ((D.c.pos : ℕ) + 1) D.c.req.fwd.hops).length
    rw [List.length_take]
    exact lt_min (Nat.lt_succ_self _) hpos
  have hkey : (D.c.req.fwd.hops[(D.c.pos : ℕ)]'hpos).key = D.k.1 := congrArg (·.key) D.c.relay
  have hkey1 : ((D.c.req.fwd.take (D.c.pos + 1)).hops[(D.c.pos : ℕ)]'hpos1).key = D.k.1 := by
    show ((List.take ((D.c.pos : ℕ) + 1) D.c.req.fwd.hops)[(D.c.pos : ℕ)]'hpos1).key = _
    have h1 : (List.take ((D.c.pos : ℕ) + 1) D.c.req.fwd.hops)[(D.c.pos : ℕ)]'hpos1
        = D.c.req.fwd.hops[(D.c.pos : ℕ)]'hpos := List.getElem_take
    exact (congrArg Protocols.RSOR.Hop.key h1).trans hkey
  have hpk : ((RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver])[(D.c.pos : ℕ)]!).publicKey
      = (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1)) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey
  have hpk1 : ((RSOR.path nike (D.c.req.fwd.take (D.c.pos + 1)) [])[(D.c.pos : ℕ)]!).publicKey =
      (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1)) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos1]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey1
  have hmod := modify_publicKey_self (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver])
      D.c.pos (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1))
    (lt_of_lt_of_eq hpos (RSOR.path_size nike _ _).symm) hpk
  have hmod1 := modify_publicKey_self (RSOR.path nike (D.c.req.fwd.take (D.c.pos + 1)) []) D.c.pos
      (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1))
    (lt_of_lt_of_eq hpos1 (RSOR.path_size nike _ _).symm) hpk1
  have hpub : ∀ i < (D.c.pos : ℕ), (RSOR.path nike (D.c.req.fwd.take (D.c.pos + 1))
      [])[i]!.publicKey = (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver])[i]!.publicKey
      := fun i hi => by
    rw [RSOR.path_getElem! nike _ _ i (lt_trans hi hpos1),
      RSOR.path_getElem! nike _ _ i (lt_trans hi hpos)]
    exact congrArg (fun h : Protocols.RSOR.Hop Name (RSOR.Key nike) =>
      Util.Bytes.ofVector (nike.encodePublicKey h.key.1)) List.getElem_take
  show groupElem nike ((nike.decodePrivateKey D.d).getD default)
      (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default)
        ((RSOR.path nike (D.c.req.fwd.take (D.c.pos + 1)) []).modify D.c.pos fun h => { h with
            publicKey := (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1)) }) D.c.pos).toArray
            D.c.pos
    = groupElem nike ((nike.decodePrivateKey D.d).getD default)
      (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default)
        ((RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).modify D.c.pos fun h => { h
            with publicKey := (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1)) })
            D.c.pos).toArray D.c.pos
  rw [hmod, hmod1, hopKeys_congr_pub nike kdfS _ _ _ _ hpub]

/-- The draws of world 1's last game on which the relay would not reply to a packet under
the replacement's header. -/
def finNoReply {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : Prop :=
  ∀ (m : Msg geom) (o : Onion geom), o.1 = (finMine nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x).1 →
    replyOf cipher geom m (procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)
        x.2.U))
      (constStream (Util.Bytes.ofVector x.2.U)) geom (fun _ => .ok (restKeys (payRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default).1 default))
      (fun _ _ => (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2)) else x.2.v) o.2) (join o)) = none

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
