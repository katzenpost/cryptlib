/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUShift

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

/-! # SLU← for NIKE Sphinx: the two worlds on the backward path, joined

The fresh-start world of `NIKESphinxSLUDrop.lean` and world 1 with the onion built like a
reply layer, compared through one game. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- **A forwarding relay hands on one fresh block.** The relay answers its header once. So
when the block it hands on is, with `u`, `w` and `v` uniform, `w` for the block `u` and `v`
for any other, it is one uniform block. -/
theorem fwdRelay_fresh (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (Hv : Protocols.RSOR.Scheme.Header 𝒮) (name : Name) (Lh : ByteArray) {α : Type}
    (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α) (log : Protocols.RSOR.Log 𝒮) :
    (do
      let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
      let w ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
      let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
      (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO Hv
          name Lh (fun y => if y = u then w else v))
        oa).run' log)
      =ᵈ ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
        (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO Hv
            name Lh (fun _ => g)) oa).run' log) := by
  have h := (KEMSphinx.withDec_fresh (S := 𝒮) Role.relay Hv (fun o => o.2)
    (fun (o : Onion geom) (y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) =>
      some (.forward name (split geom (Lh ++ Util.Bytes.ofVector y))))
    (fun _ _ _ => none) procO replyO {} (fun _ _ _ _ => rfl) oa log).map Prod.fst
  simp only [map_bind] at h
  exact h

omit cipher macS kdfS streamS hvalid hmactag h16 in
/-- **Two headers are the same up to hop `j` when what hop `j`'s keystream head masks comes out
the same**, the hops in front are the same, and hop `j` has the same element and tagging
function. What lies after hop `j` may differ. -/
theorem layerHdr_join (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path path' : Array PathHop)
    (j : ℕ) (hj : j + 1 < path.size) (hj' : j + 1 < path'.size)
    (h : ∀ i < j, ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i
      ∧ path[i]!.commands = path'[i]!.commands ∧ path[i + 1]!.id = path'[i + 1]!.id)
    (hgj : ge j = ge' j) (htj : tag j = tag' j)
    (hX : xorBytes (hopContent nike geom ks tag ge filler path j)
        ((ks j).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
            geom.perHopRoutingInfoLength))
      = xorBytes (hopContent nike geom ks' tag' ge' filler' path' j)
        ((ks' j).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
            geom.perHopRoutingInfoLength)))
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - j)).isSome)
    (hT' : (nikeHdrTrace geom ks' tag' ge' filler' path' (path'.size - j)).isSome)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops) (hn' : path'.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hfill' : filler'.size = (geom.nrHops - path'.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hks' : ∀ k,
        (ks' k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ i m, (tag i m).size = macLength) (htag' : ∀ i m, (tag' i m).size = macLength)
    (hcmd : path[j]!.commands = []) (hcmd' : path'[j]!.commands = [])
    (hgej : (ge j).size = nike.publicKeySize)
    (hge1 : (ge (j + 1)).size = nike.publicKeySize)
    (hge1' : (ge' (j + 1)).size = nike.publicKeySize) :
    nikeHdrTrace geom ks tag ge filler path path.size
        = nikeHdrTrace geom ks' tag' ge' filler' path' path'.size
      ∧ ∀ i, i ≤ j → layerHdr geom ks tag ge filler path i
        = layerHdr geom ks' tag' ge' filler' path' i := by
  have hpad : (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty)
      = (if j > 0 then KEMSphinx.padAt geom ks' (j - 1) else ByteArray.empty) := by
    by_cases h0 : j > 0
    · rw [ite_eq_left h0, ite_eq_left h0]
      exact KEMSphinx.padAt_congr geom ks ks' (j - 1) fun m hm => (h m (by omega)).1
    · rw [ite_eq_right h0, ite_eq_right h0]
  have hM : hdrMsg geom ks tag ge filler path j = hdrMsg geom ks' tag' ge' filler' path' j := by
    rw [(hdrMsg_content nike geom ks tag ge filler path j hj hnnh hle hrouting hn hfill hks htag
        hcmd hT hge1).1,
      (hdrMsg_content nike geom ks' tag' ge' filler' path' j hj' hnnh hle hrouting hn' hfill'
        hks' htag' hcmd' hT' hge1').1, hX, hpad, hgj]
  exact layerHdr_front nike geom ks ks' tag tag' ge ge' filler filler' path path' j (by omega)
    (by omega) h hM htj hT hT' hnnh hle hn hn' hfill hfill' htag htag' hgej (hgj ▸ hgej)

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
/-- **A header whose hops' functions are spliced at hop `j`**: its layers after hop `j` are
the layers of a header over the rest of the path, built from the spliced-in functions, with the
long filler followed by the front of the padding as its filler. -/
theorem layerHdr_spliceAt_drop (kf kg : ℕ → ByteArray) (tf tg : ℕ → ByteArray → ByteArray)
    (gf gg : ℕ → ByteArray) (fil : ByteArray) (path path' : Array PathHop) (j : ℕ)
    (hsz : path'.size + (j + 1) = path.size) (hn : path.size ≤ geom.nrHops)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hkf : ∀ k, (kf k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hkg : ∀ k,
        (kg k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htf : ∀ i m, (tf i m).size = macLength) (htg : ∀ i m, (tg i m).size = macLength)
    (hc : ∀ m, m < path'.size → path'[m]!.commands = path[j + m + 1]!.commands)
    (hid : ∀ m, m + 1 < path'.size → path'[m + 1]!.id = path[j + m + 1 + 1]!.id)
    (r : ℕ) (hr : r < path'.size) :
    layerHdr geom kg tg gg (fil ++ frontPad geom (spliceAt j kf kg) j (path.size - 1)) path' r
      = layerHdr geom (spliceAt j kf kg) (spliceAt j tf tg) (spliceAt j gf gg) fil path
        (j + r + 1) := by
  have e : ∀ {α : Type} (f g : ℕ → α), (fun m => spliceAt j f g (j + m + 1)) = g :=
    fun f g => funext fun m => by
      rw [spliceAt_gt j f g (j + m + 1) (by omega)]
      congr 1
      omega
  have hks : ∀ k, (spliceAt j kf kg k).size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k ≤ j
    · rw [spliceAt_le j _ _ k hk]
      exact hkf k
    · rw [spliceAt_gt j _ _ k (by omega)]
      exact hkg _
  have htag : ∀ i m, (spliceAt j tf tg i m).size = macLength := fun i m => by
    by_cases hk : i ≤ j
    · rw [spliceAt_le j _ _ i hk]
      exact htf i m
    · rw [spliceAt_gt j _ _ i (by omega)]
      exact htg _ m
  have h := layerHdr_drop geom (spliceAt j kf kg) (spliceAt j tf tg) (spliceAt j gf gg) fil path
    path' j hsz hn hnnh hle hrouting hfill hks htag hc hid r hr
  rw [e kf kg, e tf tg, e gf gg] at h
  exact h

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
/-- The mask between the tail of hop `j`'s keystream and the front of the padding `t` hops
later: the padding in front of hop `j`, then the stretches of the later hops' keystreams that
fall on it. It does not read hop `j`'s keystream. -/
def frontMask (ks : ℕ → ByteArray) (j : ℕ) : ℕ → ByteArray
  | 0 => (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty) ++
      KEMSphinx.zeroBytes geom.perHopRoutingInfoLength
  | t + 1 => xorBytes ((ks (j + t + 1)).extract ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + t + 1 + 1) * geom.perHopRoutingInfoLength)
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + t + 1 + 1) *
          geom.perHopRoutingInfoLength + (j + 1) * geom.perHopRoutingInfoLength)) (frontMask ks j t)

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
theorem frontMask_size (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (j t : ℕ)
    (hb : (j + t + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) : (frontMask geom ks j t).size = (j + 1) *
        geom.perHopRoutingInfoLength := by
  have e1 : (j + 1) * geom.perHopRoutingInfoLength = j * geom.perHopRoutingInfoLength +
      geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  induction t with
  | zero =>
    have hb0 : (j + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := hb
    have hprev : (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty).size = j *
        geom.perHopRoutingInfoLength := by
      cases j with
      | zero => simp
      | succ i =>
        rw [ite_eq_left (Nat.succ_pos i), Nat.add_sub_cancel]
        exact padAt_size geom ks hks i
          (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) hb0)
    rw [frontMask, ByteArray.size_append, hprev, KEMSphinx.zeroBytes_size, e1]
  | succ t ih =>
    have e2 : (j + (t + 1) + 1) * geom.perHopRoutingInfoLength = (j + t + 1) *
        geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have e3 : (j + 1) * geom.perHopRoutingInfoLength ≤ (j + t + 1) * geom.perHopRoutingInfoLength
        := Nat.mul_le_mul_right _ (by omega)
    have e4 : (j + t + 1 + 1) * geom.perHopRoutingInfoLength = (j + t + 1) *
        geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have hb' : (j + t + 1 + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := hb
    rw [frontMask, Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract, hks]
    omega

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
/-- The mask reads the keystreams of the hops other than `j` only. -/
theorem frontMask_congr (ks ks' : ℕ → ByteArray) (j t : ℕ) (h : ∀ m, m ≠ j → ks m = ks' m) :
    frontMask geom ks j t = frontMask geom ks' j t := by
  induction t with
  | zero =>
    rw [frontMask, frontMask]
    by_cases h0 : j > 0
    · rw [ite_eq_left h0, ite_eq_left h0,
        KEMSphinx.padAt_congr geom ks ks' (j - 1) fun m hm => h m (by omega)]
    · rw [ite_eq_right h0, ite_eq_right h0]
  | succ t ih => rw [frontMask, frontMask, ih, h (j + t + 1) (by omega)]

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
/-- **The front of the padding `t` hops after hop `j` is the tail of hop `j`'s keystream under
that mask.** -/
theorem frontPad_mask (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (j t : ℕ)
    (hb : (j + t + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) :
    frontPad geom ks j (j + t)
      = xorBytes ((ks j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1)
          * geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength))
          (frontMask geom ks j t) := by
  have e1 : (j + 1) * geom.perHopRoutingInfoLength = j * geom.perHopRoutingInfoLength +
      geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  induction t with
  | zero =>
    have hb0 : (j + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := hb
    have hs : (KEMSphinx.padAt geom ks j).size = (j + 1) * geom.perHopRoutingInfoLength :=
      padAt_size geom ks hks j hb0
    have hprev : (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty).size = j *
        geom.perHopRoutingInfoLength := by
      cases j with
      | zero => simp
      | succ i =>
        rw [ite_eq_left (Nat.succ_pos i), Nat.add_sub_cancel]
        exact padAt_size geom ks hks i
          (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) hb0)
    have hp := padAt_step geom ks hks j
    rw [hks j] at hp
    have hT : ((ks j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
        = (j + 1) * geom.perHopRoutingInfoLength := by
      rw [ByteArray.size_extract, hks]
      omega
    show (KEMSphinx.padAt geom ks j).extract 0 ((j + 1) * geom.perHopRoutingInfoLength) = _
    have h1 : (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty).size ≤ ((ks
        j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
        := by
      rw [hprev, hT]
      omega
    have h2 : ((ks j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
        - (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty).size
        ≤ geom.perHopRoutingInfoLength := by
      rw [hprev, hT]
      omega
    rw [KEMSphinx.extract_all _ _ hs, hp, frontMask, xorBytes_pad _ _ geom.perHopRoutingInfoLength
        h1 h2]
  | succ t ih =>
    have e2 : (j + (t + 1) + 1) * geom.perHopRoutingInfoLength = (j + t + 1) *
        geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have e3 : (j + 1) * geom.perHopRoutingInfoLength ≤ (j + t + 1) * geom.perHopRoutingInfoLength
        := Nat.mul_le_mul_right _ (by omega)
    have hT : ((ks j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
        = (j + 1) * geom.perHopRoutingInfoLength := by
      rw [ByteArray.size_extract, hks]
      omega
    have e4 : (j + t + 1 + 1) * geom.perHopRoutingInfoLength = (j + t + 1) *
        geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
    have hb' : (j + t + 1 + 1) * geom.perHopRoutingInfoLength ≤ (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := hb
    have hK : ((ks (j + t + 1)).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
        (j + t + 1 + 1) * geom.perHopRoutingInfoLength)
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + t + 1 + 1) *
            geom.perHopRoutingInfoLength + (j + 1) * geom.perHopRoutingInfoLength)).size = (j + 1)
            * geom.perHopRoutingInfoLength := by
      rw [ByteArray.size_extract, hks]
      omega
    show frontPad geom ks j (j + t + 1) = _
    rw [frontPad_succ geom ks hks j (j + t) (Nat.le_add_right j t) (by omega), ih (by omega),
      frontMask, KEMSphinx.xorBytes_left_comm _ _ _ (hK.trans hT.symm)
        (hT.trans (frontMask_size geom ks hks j t (by omega)).symm)]

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- **World 0's relay on the backward path hands on one fresh block.** -/
theorem backFnRun0_fresh {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A)
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) :
    (do
      let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
      let w ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
      let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
      backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x (fun y => if y = u then
          w else v) ks tag ge)
      =ᵈ ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
          backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x (fun _ => g) ks tag
          ge) :=
  fwdRelay_fresh nike cipher macS kdfS streamS geom hvalid hmactag h16 _ _ _ _ _ _ _

/-- **World 1 on the backward path, from the hops' functions.** The adversary's onion carries
the header of the reply's first layer; under the header of the layer at the honest relay the
relay forwards the onion sent on; and the sender refuses the header that goes with it. -/
def backFnRun1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A)
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) :
    ProbComp Bool :=
  (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (fun (h : Role) (o : Onion geom) =>
        if h = Role.sender ∧ o.1 = backRefuse nike cipher macS kdfS streamS geom hvalid hmactag h16
            W x then none
        else (fun h o => if h = Role.relay then
          stepOf geom (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.proc nike cipher macS kdfS streamS geom (x.2.2.keys h).2 o) h o)
      (fun h msg o => if h = Role.relay then
          replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.reply nike cipher macS kdfS streamS geom (x.2.2.keys h).2 msg o)
      (Util.Bytes.toVecN geom.headerLength (layerHdr geom ks tag ge (RSOR.filler nike geom
          (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path
          nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)))
      (x.2.2.c.req.back.hops[x.2.2.c.pos].name)
      (Util.Bytes.ofVector (backSentOn nike cipher macS kdfS streamS geom hvalid hmactag h16 W
          x).1) (fun _ => (backSentOn nike cipher macS kdfS streamS geom hvalid hmactag h16 W x).2))
    (A.guess x.2.2.st (backOnionOfHdr nike cipher macS kdfS streamS geom x.2.2.c.req x.2.2.o.1
      (Nat.zero_lt_of_lt x.2.2.c.pos.isLt)
      (backHdrBytes nike geom x.2.2.c.req x.2.2.o.1 ks tag ge)))).run' x.2.2.log

/-- **World 1 before the end of the backward path is that game** on the hops' keystreams, the
honest relay's replaced by the uniform one; their tags, the relay's its MAC; and their
elements. This holds when the reply's header builds. -/
theorem backRun1_fnMac {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A)
    (U : KEMSphinx.Keystream geom) (u v : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) (k : ℕ) (hk : x.2.2.c.pos.val = k + 1)
    (hT : pathBuilds geom (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) (RSOR.path
        nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]).size) :
    propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A
        (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backPlainS1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W) (backViewS1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) x U u v
      = backFnRun1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x (Function.update
          (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (Function.update
          (keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (fun m => Util.Bytes.ofVector (macS.mac
          (Util.Bytes.ofVector x.1) m))) (blindElem nike (groupElem nike (drawKey nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2)
          (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) := by
  have hlt : x.2.2.c.pos.val < x.2.2.c.req.back.hops.length := x.2.2.c.pos.isLt
  have hn : k + 1 < x.2.2.c.req.back.hops.length := by omega
  have hJ : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) = k := backPos_back nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W x.2.2 k hk
  have hsz := RSOR.path_size nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]
  have hJs : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) < (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]).size := by
    rw [hsz, hJ]
    exact lt_trans (Nat.lt_succ_self k) hn
  have hMS : (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U) = hdrMsg geom
      (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (blindElem nike
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
      default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) :=
    backMS1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U k hk
  have hL : layerHdr geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x) default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (Function.update (keysTag macS
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray)
      (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      x.2.2) fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) (backMS1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W x U))) (blindElem nike (groupElem nike (drawKey
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names x.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2)
      = (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U) ++
          Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) (backMS1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 W x U)) := by
    unfold layerHdr
    rw [hdrMsg_update_tag geom _ _ _ _ _ (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names) x.2.2) hJs, Function.update_self, ← hMS]
  rw [backRun1_fwd nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U u v k hk hn hT]
  unfold backFnRun1
  rw [backHdrBytes_tagAt nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray)
      (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      x.2.2) (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
      kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) hJs (fun m
      => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) m)),
    layerHdr_tagAt geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)
        (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
        default) default).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2)
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) hJs (fun m => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.1) m)) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names) x.2.2), ← hMS, hL]

/-- **The game the two worlds share on the backward path**, from what they differ in: the
header `H0` of the reply's first layer, which the adversary's onion carries; the header `Hv`
the honest relay answers, by forwarding to `name` the header `Lh` with the block `g`; and the
header the sender refuses. -/
def backJoinRun {Oth : Type} {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names Oth A) (r : RSOR.Randomness nike geom)
    (H0 : ByteArray) (Hv refuse : Vector UInt8 geom.headerLength) (name : Name) (Lh : ByteArray)
    (g : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) : ProbComp Bool :=
  (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (fun (h : Role) (o : Onion geom) =>
        if h = Role.sender ∧ o.1 = refuse then none
        else (fun h o => if h = Role.relay then
          stepOf geom (noneAns nike cipher macS kdfS streamS geom D.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) D) (join o))
        else RSOR.proc nike cipher macS kdfS streamS geom (D.keys h).2 o) h o)
      (fun h msg o => if h = Role.relay then
          replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom D.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) D) (join o))
        else RSOR.reply nike cipher macS kdfS streamS geom (D.keys h).2 msg o)
      Hv name Lh (fun _ => g))
    (A.guess D.st (backOnionOfHdr nike cipher macS kdfS streamS geom D.c.req r
      (Nat.zero_lt_of_lt D.c.pos.isLt) H0))).run' D.log

/-- World 0 with one block handed on is that game: the relay forwards the header of the
reply's next layer, and the sender refuses the header of its last. -/
theorem backFnRun0_join {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A)
    (g : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) :
    backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x (fun _ => g) ks tag ge
      = backJoinRun nike cipher macS kdfS streamS geom hvalid hmactag h16 W x.2.2 x.2.2.o.1
        (backHdrBytes nike geom x.2.2.c.req x.2.2.o.1 ks tag ge)
        (Util.Bytes.toVecN geom.headerLength (layerHdr geom ks tag ge (RSOR.filler nike geom
          (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path
          nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)))
        (backHdrFn nike geom x.2.2.c.req x.2.2.o.1 ks tag ge (x.2.2.c.req.back.hops.length - 1))
        (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])[(drawPos nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) + 1]!.id
        (layerHdr geom ks tag ge (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back
          [.surbReply x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back
          [.surbReply x.2.2.o.1.2.2.2]) ((drawPos nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) + 1)) g :=
  rfl

/-- World 1 is that game: the relay forwards the onion sent on, and the sender refuses the
header that goes with it. -/
theorem backFnRun1_join {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A)
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) :
    backFnRun1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x ks tag ge
      = backJoinRun nike cipher macS kdfS streamS geom hvalid hmactag h16 W x.2.2 x.2.2.o.1
        (backHdrBytes nike geom x.2.2.c.req x.2.2.o.1 ks tag ge)
        (Util.Bytes.toVecN geom.headerLength (layerHdr geom ks tag ge (RSOR.filler nike geom
          (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path
          nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)))
        (backRefuse nike cipher macS kdfS streamS geom hvalid hmactag h16 W x)
        (x.2.2.c.req.back.hops[x.2.2.c.pos].name)
        (Util.Bytes.ofVector (backSentOn nike cipher macS kdfS streamS geom hvalid hmactag h16 W
          x).1)
        (backSentOn nike cipher macS kdfS streamS geom hvalid hmactag h16 W x).2 :=
  rfl

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
