/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTLUPayload

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # The stream cipher step for TLU→

After the payload cipher step, a world of TLU→ uses the honest relay's header encryption key
and IV for one keystream only. So the world is the real experiment of the keystream generator
`keystreamPRG` for an adversary that plays it from the keystream, and the keystream can be
replaced by uniform bytes at the cost of that generator's advantage. -/

section ForwardStream

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

variable [SampleableType kem.Plaintext]

variable (names : Role → RSOR.Name) (Oth : Type) (drawO : ProbComp Oth)
  (view : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → KeyTuple
    → Protocols.RSOR.World (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
  (A : (Protocols.RSOR.forwardUnlinkable
    (S := sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary)
  (M : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → RestKeys → ByteArray)
  (pl : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32
    → Block geom)
  (viewE : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32
    → Block geom
    → Protocols.RSOR.World (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))

local notation "𝒜" =>
  forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO view A

local notation "𝒯" =>
  forwardSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO view

variable
  (MU : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → ByteArray → ByteArray)
  (plU : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → ByteArray → Block geom)
  (viewU : {pk : Key kem} →
      ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
    → Oth → kem.Ciphertext → Vector UInt8 32 → ByteArray → Block geom
    → Protocols.RSOR.World (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))

/-- The ideal payload game of a world after its draws, from the relay's MAC key and its header
keystream `U`: `MU` are the header bytes, `plU` the sender's block and `viewU` the world, as
functions of the keystream. -/
def forwardRunU (km : Vector UInt8 32) (U : ByteArray) (d : KeyedDraw 𝒜) (u v : Block geom) :
    ProbComp Bool :=
  (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay
      (fun h => if h = .relay then d.k.2 else d.cs.2.2.2 h) d.c km U
      (Util.Bytes.toVecN _ (MU d.cs.1 d.o d.c U
        ++ ofVector (macS.mac (ofVector km) (MU d.cs.1 d.o d.c U))))
      (fun y => if y = u then plU d.cs.1 d.o U else v)
      (viewU d.cs.1 d.o d.c km U u).patch)
    (A.guess d.cs.2.1 (viewU d.cs.1 d.o d.c km U u).onion)).run' d.cs.2.2.1

/-- The adversary against the keystream generator that plays the ideal payload game of a world
from the keystream. -/
def forwardStreamAdv : PRGScheme.PRGAdversary (Keystream geom) := fun U => do
  let km ← $ᵗ (Vector UInt8 32)
  let d ← keyedDraw cipher macS kdfS streamS geom 𝒜
  let u ← $ᵗ (Block geom)
  let v ← $ᵗ (Block geom)
  forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO view A
    MU plU viewU km (ofVector U) d u v

omit [SampleableType kem.Plaintext] in
/-- **The stream cipher step, for a world of TLU→.** When the header bytes, the sender's block
and the world are functions of the relay's header keystream, the ideal payload game is the real
experiment of the keystream generator for `forwardStreamAdv`. -/
theorem forwardPayload_exp_false_eq_prg
    (hM : ∀ {pk : Key kem}
      (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
      (o : Oth) (c : kem.Ciphertext) (kp : Vector UInt8 48) (iv : Vector UInt8 16)
      (ke : Vector UInt8 32), M ch o c (kp, iv, ke)
        = MU ch o c (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)))
    (hpl : ∀ {pk : Key kem}
      (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
      (o : Oth) (c : kem.Ciphertext) (iv : Vector UInt8 16) (km ke : Vector UInt8 32),
      pl ch o c (iv, km, ke)
        = plU ch o (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)))
    (hviewE : ∀ {pk : Key kem}
      (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
      (o : Oth) (c : kem.Ciphertext) (iv : Vector UInt8 16) (km ke : Vector UInt8 32)
      (e : Block geom), viewE ch o c (iv, km, ke) e
        = viewU ch o c km (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)) e) :
    Pr{let x ← ((forwardPayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16
        names Oth drawO view A M pl viewE).exp false)}[x = true]
      = Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (forwardStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO
          view A MU plU viewU))}[x = true] := by
  refine EvalDistEq.prEvent_eq ?_ _
  have hb : ∀ {α β : Type},
      Function.Bijective (Function.uncurry fun (a : α) (b : β) => (a, b)) :=
    fun {_ _} => Function.bijective_id
  let K : Vector UInt8 16 → Vector UInt8 32 → Vector UInt8 32 → ProbComp Bool :=
    fun iv km ke => do
      let d ← keyedDraw cipher macS kdfS streamS geom 𝒜
      let u ← $ᵗ (Block geom)
      let v ← $ᵗ (Block geom)
      forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO view A
        MU plU viewU km (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)) d u v
  have hbody : ∀ (iv : Vector UInt8 16) (km ke : Vector UInt8 32) (d : KeyedDraw 𝒜)
      (u v : Block geom),
      (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay
          (fun h => if h = .relay then d.k.2 else d.cs.2.2.2 h) d.c km
          (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))
          (Util.Bytes.toVecN _ (tagged (S := 𝒯) macS M d.cs.1 d.o d.c (default, iv, km, ke)))
          (fun y => if y = u then pl d.cs.1 d.o d.c (iv, km, ke) else v)
          (viewE d.cs.1 d.o d.c (iv, km, ke) u).patch)
        (A.guess d.cs.2.1 (viewE d.cs.1 d.o d.c (iv, km, ke) u).onion)).run' d.cs.2.2.1
      = forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO view A
        MU plU viewU km (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)) d u v := by
    intro iv km ke d u v
    have hT : tagged (S := 𝒯) macS M d.cs.1 d.o d.c (default, iv, km, ke)
        = MU d.cs.1 d.o d.c (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))
          ++ ofVector (macS.mac (ofVector km) (MU d.cs.1 d.o d.c
            (streamS.keystream (ofVector ke) (ofVector iv)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)))) := by
      unfold tagged restOf
      dsimp only
      rw [hM d.cs.1 d.o d.c default iv ke]
    unfold forwardRunU
    rw [hT, hpl d.cs.1 d.o d.c iv km ke, hviewE d.cs.1 d.o d.c iv km ke u]
  have h0 : (forwardPayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16
        names Oth drawO view A M pl viewE).exp false
      = (do
        let _ ← $ᵗ (Vector UInt8 48)
        let iv ← $ᵗ (Vector UInt8 16)
        let r ← $ᵗ (Vector UInt8 32 × Vector UInt8 32)
        K iv r.1 r.2) := by
    unfold PayloadGame.exp
    simp only [forwardPayloadGame, bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte, K]
    refine bind_congr fun kp => bind_congr fun iv => bind_congr fun r => bind_congr fun d =>
      bind_congr fun u => bind_congr fun v => ?_
    exact hbody iv r.1 r.2 d u v
  have hR : PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (forwardStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth drawO
          view A MU plU viewU)
      = (do
        let s ← $ᵗ (Vector UInt8 32 × Vector UInt8 16)
        let km ← $ᵗ (Vector UInt8 32)
        K s.2 km s.1) := by
    unfold PRGScheme.prgRealExperiment forwardStreamAdv keystreamPRG
    simp only [K, Cryptlib.Util.Bytes.ofVector_toVecN _ (streamS.keystream_size _ _ _)]
  rw [h0, hR]
  refine (OracleComp.EvalDistEq.bind_const _ _).trans ?_
  refine EvalDistEq.trans ?_ (evalDistEq_pair_of_bijective
    (g := fun (ke : Vector UInt8 32) (iv : Vector UInt8 16) => (ke, iv)) hb
    (fun s => $ᵗ (Vector UInt8 32) >>= fun km => K s.2 km s.1))
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun iv =>
    (evalDistEq_pair_of_bijective
      (g := fun (km ke : Vector UInt8 32) => (km, ke)) hb (fun r => K iv r.1 r.2)).symm) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun iv =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ fun km ke => K iv km ke) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ fun iv ke =>
    $ᵗ (Vector UInt8 32) >>= fun km => K iv km ke

/-! ## World 0 -/

/-- World 0's header bytes at the honest relay, from its header keystream. -/
def forwardMU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (U : ByteArray) : ByteArray :=
  relayFrontAt kem cipher macS kdfS streamS geom
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
    (ofVector (kem.encodeCiphertext c)) U

/-- World 0's block at the honest relay, from its header keystream. -/
def forwardBlockU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (U : ByteArray) : Block geom :=
  Util.Bytes.toVecN _ (relayBackAt kem cipher macS kdfS streamS geom
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos U id)

/-- World 0 from the honest relay's MAC key, its header keystream and the encrypted block. -/
def forwardViewU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (km : Vector UInt8 32) (U : ByteArray)
    (e : Block geom) : Protocols.RSOR.World 𝒮 where
  onion := RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 0 ch.c.pos
    (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c U
      ++ ofVector (macS.mac (ofVector km)
        (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c U))
      ++ ofVector e))

/-- The adversary against the keystream generator that plays world 0. -/
def forwardStreamAdv0 (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    PRGScheme.PRGAdversary (Keystream geom) :=
  forwardStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom)
    (fun ch r c t =>
      { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }) A
    (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)

omit [SampleableType kem.Plaintext] in
/-- **The stream cipher step for world 0 of TLU→.** With uniform keys at the honest relay and
the challenge header only, world 0 is the ideal experiment of the keystream generator for
`forwardStreamAdv0`, up to the one-block cipher advantage, the generator's advantage and the
chance of a draw that is not good. -/
theorem forward_stream_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
          (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (forwardM kem cipher macS kdfS streamS geom hvalid hmactag h16
              names))))}[x = true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
    ≤ |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (forwardGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
          true)}[x = true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (forwardGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
          false)}[x = true]).toReal|
      + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16
          names A))}[¬ forwardGoodP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            d]).toReal := by
  have h := forward_payload_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have e : Pr{let x ← ((forwardGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A).exp false)}[x = true]
      = Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true] :=
    forwardPayload_exp_false_eq_prg kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom)
    (fun ch r c t =>
      { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }) A _ _ _ _ _ _
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
  rw [e] at h
  have t := abs_sub_le
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
      (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (forwardM kem cipher macS kdfS streamS geom hvalid hmactag h16
          names))))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
      (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
  linarith

/-! ## World 1 -/

/-- World 1's header bytes at the honest relay, from its header keystream. -/
def shortMU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (c : kem.Ciphertext) (U : ByteArray) : ByteArray :=
  relayFrontAt kem cipher macS kdfS streamS geom
    (RSOR.path kem (ch.c.short o.2.1 o.2.2.1).fwd
      [.recipient (ch.c.short o.2.1 o.2.2.1).receiver])
    o.2.2.2.1
    (RSOR.body kem macS kdfS streamS geom (ch.c.short o.2.1 o.2.2.1) o.2.2.2) ch.c.pos
    (ofVector (kem.encodeCiphertext c)) U

/-- World 1's block at the honest relay, from its header keystream. -/
def shortBlockU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (U : ByteArray) : Block geom :=
  Util.Bytes.toVecN _ (relayBackAt kem cipher macS kdfS streamS geom
    (RSOR.path kem (ch.c.short o.2.1 o.2.2.1).fwd
      [.recipient (ch.c.short o.2.1 o.2.2.1).receiver])
    o.2.2.2.1
    (RSOR.body kem macS kdfS streamS geom (ch.c.short o.2.1 o.2.2.1) o.2.2.2) ch.c.pos U id)

/-- The honest relay's layer of the replacement, from its MAC key, its header keystream and
the encrypted block. -/
def shortLayerU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (c : kem.Ciphertext) (km : Vector UInt8 32) (U : ByteArray) (e : Block geom) : ByteArray :=
  shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c U
    ++ ofVector (macS.mac (ofVector km)
      (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c U))
    ++ ofVector e

/-- World 1 from the honest relay's MAC key, its header keystream and the encrypted block. -/
def shortViewU {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (c : kem.Ciphertext) (km : Vector UInt8 32) (U : ByteArray)
    (e : Block geom) : Protocols.RSOR.World 𝒮 where
  onion := RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom
    (RSOR.path kem (ch.c.short o.2.1 o.2.2.1).fwd
      [.recipient (ch.c.short o.2.1 o.2.2.1).receiver])
    o.2.2.2.1 0 ch.c.pos
    (shortLayerU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c km U e))
  patch := ch.c.patch o.1
    (RSOR.split geom
      (shortLayerU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c km U e))

/-- The adversary against the keystream generator that plays world 1. -/
def shortStreamAdv (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    PRGScheme.PRGAdversary (Keystream geom) :=
  forwardStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    _ (shortDraw geom) (shortView kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A
    (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (shortViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)

omit [SampleableType kem.Plaintext] in
/-- **The stream cipher step for world 1 of TLU→.** With uniform keys at the honest relay and
the challenge header only, world 1 is the ideal experiment of the keystream generator for
`shortStreamAdv`, up to the one-block cipher advantage, the generator's advantage and the
chance of a draw that is not good. -/
theorem short_stream_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
          (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (shortM kem cipher macS kdfS streamS geom hvalid hmactag h16
              names))))}[x = true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
    ≤ |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (shortGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
          true)}[x = true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (shortGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
          false)}[x = true]).toReal|
      + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16
          names A))}[¬ shortGoodP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            d]).toReal := by
  have h := short_payload_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have e : Pr{let x ← ((shortGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A).exp false)}[x = true]
      = Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true] :=
    forwardPayload_exp_false_eq_prg kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      _ (shortDraw geom) (shortView kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      A _ _ _ _ _ _
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
  rw [e] at h
  have t := abs_sub_le
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
      (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (shortM kem cipher macS kdfS streamS geom hvalid hmactag h16
          names))))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
      (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
  linarith

/-! ## The bound so far -/

/-- **TLU→ for KEM Sphinx, down to two games played from a uniform keystream.** The advantage is
at most: the chance of a bad draw in either world; the cost of replacing the honest relay's
keys in either world; a forgery against the MAC in either world; the one-block advantage
against the payload cipher in either world; the advantage against the keystream generator in
either world; and the distance between the two worlds played from a uniform keystream, a
uniform encrypted block and the relay's MAC key. -/
theorem forwardUnlinkable_le_uniform
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
        + |(Pr{let x ← (PRGScheme.prgIdealExperiment
          (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal| := by
  have h := forwardUnlinkable_le_tagged kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have s0 := forward_stream_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have s1 := short_stream_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have t1 := abs_sub_le
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
      (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (shortM kem cipher macS kdfS streamS geom hvalid hmactag h16
          names))))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
      (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (forwardM kem cipher macS kdfS streamS geom hvalid hmactag h16
          names))))}[x = true]).toReal
  have t2 := abs_sub_le
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
      (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (forwardM kem cipher macS kdfS streamS geom hvalid hmactag h16
          names))))}[x = true]).toReal
  rw [abs_sub_comm
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A))}[x = true]).toReal
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom
      (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (forwardM kem cipher macS kdfS streamS geom hvalid hmactag h16
          names))))}[x = true]).toReal] at t2
  linarith

end ForwardStream

end Cryptlib.Protocols.Sphinx.KEMSphinx
