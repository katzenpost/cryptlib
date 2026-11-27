/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUNext

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Common (commandsToBytes zeroPadTo toVec32)
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult relayImpl keysKs keysTag keysEnc)
open Cryptlib.Protocols.Sphinx.Common (v0AD)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # The last comparison of the two worlds of TLU→, for NIKE Sphinx

After the steps of `NIKESphinxTLU.lean` and `NIKESphinxTLUNext.lean` each world is played from
uniform keystreams. Here the two are compared. -/

section NextFn

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- The layer after hop `j` of `q`'s onion, from each hop's keystream, tag, encryption and
element: the header of layer `j + 1` and the block the hops after it left. -/
def nextOfFn (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (ks : ℕ → ByteArray)
    (tag enc : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (j : ℕ) : Onion geom :=
  if (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength then
    match nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
        [.recipient q.receiver]).size with
    | some _ => split geom (layerHdr geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd
        [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (j + 1)
      ++ encTrace enc (RSOR.path nike q.fwd [.recipient q.receiver]).size ((⟨Array.replicate
          geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS geom q r))
          ((RSOR.path nike q.fwd [.recipient q.receiver]).size - (j + 1)))
    | none => default
  else default

omit nike in
/-- Whether a hop's fragment builds does not depend on the tag it names. -/
theorem nikeFragment_isOk (path : Array PathHop) (mac mac' : ByteArray) (i : ℕ) :
    (nikeFragment geom path mac i).isOk = (nikeFragment geom path mac' i).isOk := by
  unfold nikeFragment
  generalize commandsToBytes _ _ = e
  cases e <;> simp only [bind, Except.bind, pure, Except.pure, Except.isOk, Except.toBool]

omit nike in
/-- Whether a header builds depends on the path alone. -/
theorem nikeHdrTrace_isSome (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path : Array PathHop) (t : ℕ) :
    (nikeHdrTrace geom ks tag ge filler path t).isSome
      = (nikeHdrTrace geom ks' tag' ge' filler' path t).isSome := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [nikeHdrTrace, nikeHdrTrace]
    cases h : nikeHdrTrace geom ks tag ge filler path t with
    | none =>
      rw [h] at ih
      cases h' : nikeHdrTrace geom ks' tag' ge' filler' path t with
      | none => rfl
      | some s' => rw [h'] at ih; cases ih
    | some s =>
      rw [h] at ih
      cases h' : nikeHdrTrace geom ks' tag' ge' filler' path t with
      | none => rw [h'] at ih; cases ih
      | some s' =>
        dsimp only
        have hf := nikeFragment_isOk geom path s.2 s'.2 (path.size - 1 - t)
        cases hf1 : nikeFragment geom path s.2 (path.size - 1 - t) with
        | error e =>
          rw [hf1] at hf
          cases hf2 : nikeFragment geom path s'.2 (path.size - 1 - t) with
          | error e' => rfl
          | ok F' => rw [hf2] at hf; cases hf
        | ok F =>
          rw [hf1] at hf
          cases hf2 : nikeFragment geom path s'.2 (path.size - 1 - t) with
          | error e' => rw [hf2] at hf; cases hf
          | ok F' => rfl

/-- **The layer after hop `j` reads the hops up to `j` through the padding after hop `j`
only.** -/
theorem nextOfFn_congr (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (ks ks' : ℕ → ByteArray) (tag tag' enc enc' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (j : ℕ) (hj : j + 1 < (RSOR.path nike q.fwd [.recipient
        q.receiver]).size)
    (h : ∀ i, j < i → ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i ∧ enc i = enc' i)
    (hp : KEMSphinx.padAt geom ks j = KEMSphinx.padAt geom ks' j) :
    nextOfFn nike macS kdfS streamS geom q r ks tag enc ge j
      = nextOfFn nike macS kdfS streamS geom q r ks' tag' enc' ge' j := by
  have hL := layerHdr_congr_tail geom ks ks' tag tag' ge ge' (RSOR.filler nike geom (RSOR.path nike
      q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j hj
    (fun i hi => ⟨(h i hi).1, (h i hi).2.1, (h i hi).2.2.1⟩) hp
  have hE := encTrace_congr enc enc' (RSOR.path nike q.fwd [.recipient q.receiver]).size
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS
      geom q r)) ((RSOR.path nike q.fwd [.recipient q.receiver]).size - (j + 1)) (by omega)
    fun i hi _ => (h i (by omega)).2.2.2
  have hS := nikeHdrTrace_isSome geom ks ks' tag tag' ge ge' (RSOR.filler nike geom (RSOR.path nike
      q.fwd [.recipient q.receiver]) r.1) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
      q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
      [.recipient q.receiver]).size
  unfold nextOfFn
  rw [hL, hE]
  cases h1 : nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
      q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
      [.recipient q.receiver]).size with
  | none =>
    rw [h1] at hS
    cases h2 : nikeHdrTrace geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike q.fwd
        [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path
        nike q.fwd [.recipient q.receiver]).size with
    | none => rfl
    | some s' => rw [h2] at hS; cases hS
  | some s =>
    rw [h1] at hS
    cases h2 : nikeHdrTrace geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike q.fwd
        [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path
        nike q.fwd [.recipient q.receiver]).size with
    | none => rw [h2] at hS; cases hS
    | some s' => rfl

/-- The layer after hop `j` from the hops' keys and hop `j`'s keystream is `nextOfFn` on their
keystreams, tags, encryptions and elements. -/
theorem nextOfStream_eq_nextOfFn (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (a : ByteArray) (K : List HopKeys) (j : ℕ) (U : ByteArray)
    (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (hj : j + 1 < (RSOR.path nike q.fwd [.recipient q.receiver]).size) (hjk : j < K.length) (hU :
        U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (ha : a.size = nike.publicKeySize) :
    nextOfStream nike cipher macS kdfS streamS geom q r a K j U
      = nextOfFn nike macS kdfS streamS geom q r
        (Function.update (keysKs geom streamS K.toArray) j U) (keysTag macS K.toArray)
        (keysEnc cipher K.toArray) (blindElem nike a K.toArray) j :=
  nextOfStream_layerHdr nike cipher macS kdfS streamS geom q r a K j U hvalid hmactag hj hjk hU ha

end NextFn

/-! ## The blinding game

The hops after the honest relay get their keys from the sender's secret and the relay's
blinding factor, and the element that reaches them is the sender's, blinded. When the relay's
blinding factor is uniform, a prime-order group makes all of this independent of the sender's
secret. The NIKE type does not say so, and with clamped scalars it need not hold exactly, so
it is a game: its advantage is a term of the bound. -/

section Blind

variable (nike : NIKE) (kdfS : KDF)

/-- What lies after hop `j` of a path: the element that reaches hop `j + 1` and the keys of the
hops after `j`, from the sender's secret `c` and the seed of hop `j`'s blinding factor. -/
def tailOf (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (seed : Vector UInt8 32) :
    ByteArray × List HopKeys :=
  (groupElem nike c
      (hopKeysWith nike kdfS c hops j (keysOfDraw (default, seed)) hops.size).toArray (j + 1),
    (hopKeysWith nike kdfS c hops j (keysOfDraw (default, seed)) hops.size).drop (j + 1))

/-- **The tail of a path with a hop's keys replaced is `tailOf`**, whatever the other keys of
the replacement. -/
theorem tailOf_hopKeysWith (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ)
    (seed : Vector UInt8 32) (t : HopKeys) (hj : j < hops.size)
    (ht : t.blindingFactor = blindingFactorPrivKey seed) :
    tailOf nike kdfS c hops j seed
      = (groupElem nike c (hopKeysWith nike kdfS c hops j t hops.size).toArray (j + 1),
        (hopKeysWith nike kdfS c hops j t hops.size).drop (j + 1)) := by
  have hf : RSOR.factor nike (keysOfDraw (default, seed)) = RSOR.factor nike t := by
    unfold RSOR.factor
    rw [ht]
    rfl
  have hk : ∀ t' : HopKeys, (hopKeysWith nike kdfS c hops j t' hops.size).toArray[j]! = t' :=
    fun t' => toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j t' _ hj)
  have hg : ∀ t' : HopKeys, groupElem nike c (hopKeysWith nike kdfS c hops j t'
      hops.size).toArray (j + 1)
      = nikeBlind nike (groupElem nike c (RSOR.hopKeys nike kdfS c hops j).toArray j)
        t'.blindingFactor := fun t' => by
    show nikeBlind nike _ _ = _
    rw [groupElem_hopKeysWith nike kdfS c hops j t' hops.size (le_of_lt hj), hk]
  unfold tailOf
  rw [hg, hg, ht]
  refine congrArg (Prod.mk _) (List.ext_getElem? fun m => ?_)
  rw [List.getElem?_drop, List.getElem?_drop]
  exact (hopKeysWith_congr nike kdfS c hops j _ _ hf hops.size).2 (j + 1 + m) (by omega)

/-- An adversary on the blinding game: it names a secret, a path and a hop, and is given what
lies after the hop. -/
structure BlindAdversary where
  St : Type
  pre : ProbComp ((nike.PrivateKey × Array PathHop × ℕ) × St)
  post : St → ByteArray × List HopKeys → ProbComp Bool

variable {nike} in
/-- **The blinding game.** What lies after the hop comes from the adversary's secret, or from
an independent uniform one. The hop's blinding factor is uniform. -/
def blindGame (B : BlindAdversary nike) (b : Bool) : ProbComp Bool := do
  let x ← B.pre
  let seed ← $ᵗ (Vector UInt8 32)
  let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
  B.post x.2 (tailOf nike kdfS (if b then (nike.decodePrivateKey d).getD default else x.1.1)
    x.1.2.1 x.1.2.2 seed)

variable {nike} in
/-- The adversary's advantage in the blinding game. -/
noncomputable def blindAdvantage (B : BlindAdversary nike) : ℝ :=
  |(Pr{let x ← blindGame kdfS B true}[x = true]).toReal
    - (Pr{let x ← blindGame kdfS B false}[x = true]).toReal|

end Blind

end Cryptlib.Protocols.Sphinx.NIKESphinx
