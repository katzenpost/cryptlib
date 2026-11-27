/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLURelay

namespace Cryptlib.Protocols.RSOR

open OracleComp OracleSpec

variable {S : Scheme}

/-- STI↔ from its world 0 to a world in the middle. -/
def tailTo (mid : {hon : Honest S} → TailChallenge hon → ProbComp (World S)) : Property S where
  Challenge := TailChallenge
  world c b := match b with
    | false => (tailIndistinguishable (S := S)).world c false
    | true => mid c

/-- STI↔ from a world in the middle to its world 1. -/
def tailFrom (mid : {hon : Honest S} → TailChallenge hon → ProbComp (World S)) : Property S where
  Challenge := TailChallenge
  world c b := match b with
    | false => mid c
    | true => (tailIndistinguishable (S := S)).world c true

/-- An adversary of STI↔, against the game up to the world in the middle. -/
def tailTo.cast (mid : {hon : Honest S} → TailChallenge hon → ProbComp (World S))
    (A : (tailIndistinguishable (S := S)).Adversary) : (tailTo mid).Adversary :=
  ⟨A.State, A.choose, A.guess⟩

/-- An adversary of STI↔, against the game from the world in the middle. -/
def tailFrom.cast (mid : {hon : Honest S} → TailChallenge hon → ProbComp (World S))
    (A : (tailIndistinguishable (S := S)).Adversary) : (tailFrom mid).Adversary :=
  ⟨A.State, A.choose, A.guess⟩

/-- **STI↔ through a world in the middle.** -/
theorem tailIndistinguishable_advantage_le
    (mid : {hon : Honest S} → TailChallenge hon → ProbComp (World S)) (names : Role → S.Name)
    (A : (tailIndistinguishable (S := S)).Adversary) :
    ((tailIndistinguishable (S := S)).advantage names A).toReal
      ≤ ((tailFrom mid).advantage names (tailFrom.cast mid A)).toReal
        + ((tailTo mid).advantage names (tailTo.cast mid A)).toReal := by
  rw [Property.advantage_toReal, Property.advantage_toReal, Property.advantage_toReal]
  have e1 : Property.play names (tailFrom.cast mid A) true = Property.play names A true := rfl
  have e2 : Property.play names (tailFrom.cast mid A) false
      = Property.play names (tailTo.cast mid A) true := rfl
  have e3 : Property.play names (tailTo.cast mid A) false = Property.play names A false := rfl
  rw [e1, e2, e3]
  exact abs_sub_le _ _ _

end Cryptlib.Protocols.RSOR

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

/-! # STI↔ for KEM Sphinx

World 0 of STI↔ shows a layer of the adversary's onion from a forward position on; world 1
shows the first layer of an onion over the rest of the forward path. A layer from a position on
is a layer over the rest of the path, with the filler there as the rest's padding.

The two worlds are compared through a world in the middle (`tailTo`, `tailFrom`). -/

section RestOfForward

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

omit cipher macS in
/-- The fillers from position `j` on are the fillers built on the rest of the path from the
filler at `j`. -/
theorem fillerAt_drop (hops : Array PathHop) (seeds : Array (Vector UInt8 32))
    (filler : ByteArray) (j i : ℕ) :
    RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i)
      = RSOR.fillerAt kem kdfS streamS geom (hops.extract j hops.size)
        (seeds.extract j seeds.size) (RSOR.fillerAt kem kdfS streamS geom hops seeds filler j)
        i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i + 1) = _
    simp only [RSOR.fillerAt]
    rw [ih, extract_tail_tail hops j i, extract_tail_tail seeds j i]

/-- **A layer from a position on is a layer over the rest of the path**, when the seeds from
there on are the rest's seeds and the filler there is the rest's padding. -/
theorem layer_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (d d' : RSOR.Draw geom) (payload : ByteArray) (j i : ℕ)
    (hj : j ≤ R.hops.length)
    (hseeds : (d.1.toArray.extract 0 (RSOR.path kem R last).size).extract j
        (d.1.toArray.extract 0 (RSOR.path kem R last).size).size
      = d'.1.toArray.extract 0 (RSOR.path kem (R.drop j) last).size)
    (hfill : RSOR.fillerAt kem kdfS streamS geom (RSOR.path kem R last)
        (d.1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector d.2).extract 0
          ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j
      = (ofVector d'.2).extract 0
        ((geom.nrHops - (RSOR.path kem (R.drop j) last).size)
          * geom.perHopRoutingInfoLength)) :
    RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload (j + i)
      = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop j) last) d' payload
        i := by
  unfold RSOR.layer
  dsimp only
  rw [fillerAt_drop, hfill,
    extract_tail_tail (d.1.toArray.extract 0 (RSOR.path kem R last).size) j i,
    extract_tail_tail (RSOR.path kem R last) j i, hseeds,
    path_extract_drop kem geom R last j hj]

end RestOfForward

section TailGame

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- The first layer of an onion over the rest of the forward path, with the forward draw `d`,
around the payload of the adversary's onion. The honest backward relay answers nothing to the
reply's layer, as in world 0. -/
def tailMidWorld {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (d : RSOR.Draw geom) : Protocols.RSOR.World 𝒮 where
  onion :=
    (match RSOR.layer kem cipher macS kdfS streamS geom
        (RSOR.path kem (c.req.fwd.drop c.pos) [.recipient c.req.receiver]) d
        (RSOR.body kem macS kdfS streamS geom c.req r) 0 with
    | .ok pkt => RSOR.split geom pkt
    | .error _ => (default : RSOR.Onion geom))
  patch := (Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back).patch

/-- **The world in the middle of STI↔**: `tailMidWorld` with its draws. The payload still
carries the SURB over the whole backward path. -/
def tailMid {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    ProbComp (Protocols.RSOR.World 𝒮) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let d ← $ᵗ (RSOR.Draw geom)
  return tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d

/-- The challenger's randomness with the seed `s` at the forward hop before position `pos`. -/
def tailSeed (pos : ℕ) (r : RSOR.Randomness geom) (s : Vector UInt8 32) : RSOR.Randomness geom :=
  match pos with
  | 0 => r
  | k + 1 => setSeed geom r k s

omit kem cipher macS kdfS streamS hvalid hmactag h16 in
/-- Drawing the challenger's randomness and a seed, and putting the seed at the hop before the
shown layer, is drawing the randomness. -/
theorem evalDistEq_tailSeed {δ : Type} (pos : ℕ) (hpos : pos ≤ geom.nrHops)
    (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (tailSeed geom pos r s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  cases pos with
  | zero =>
    exact EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r)
  | succ k => exact evalDistEq_setSeed geom k (by omega) K

end TailGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
