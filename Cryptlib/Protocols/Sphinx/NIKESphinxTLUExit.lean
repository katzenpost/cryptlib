/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUDraws

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

/-! # The last comparison of TLU→ for NIKE Sphinx: the end of the path

The honest relay as the last hop of the original's path: the two relays in one closed form. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- What a relay hands over as the last hop for the recipient `rc`, its payload decrypted to
`y`: what follows the zero tag of `y`, when that tag is zero. -/
def lastRes (rc : Name) (y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) :
    ProcResult :=
  if ((Util.Bytes.ofVector y).extract 0 geom.payloadTagLength).data.all (· == 0) = true then
    some (some ((Util.Bytes.ofVector y).extract geom.payloadTagLength
        (geom.payloadTagLength + geom.forwardPayloadLength)),
      default, [RoutingCommand.recipient rc], none)
  else none

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
/-- A relay's step does not read the packet's replay tag. -/
theorem stepOf_tag (pl : ByteArray) (h1 h2 : Vector UInt8 32) (cmds : List RoutingCommand) :
    stepOf geom (some (some pl, h1, cmds, none)) = stepOf geom (some (some pl, h2, cmds, none)) :=
  rfl

omit nike macS kdfS streamS hvalid hmactag h16 in
/-- Nor does its reply. -/
theorem replyOf_tag (m : Msg geom) (pl : ByteArray) (h1 h2 : Vector UInt8 32)
    (cmds : List RoutingCommand) :
    replyOf cipher geom m (some (some pl, h1, cmds, none))
      = replyOf cipher geom m (some (some pl, h2, cmds, none)) :=
  rfl

/-- The honest relays, the relay answering the header `Hv` as the last hop for the recipient
`rc`, with its block decrypted by `D`. -/
def lastRelay (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (Hv : Protocols.RSOR.Scheme.Header 𝒮) (rc : Name) (D : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength) → Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) :
    QueryImpl (Protocols.RSOR.oracleSpec 𝒮) (StateT (Protocols.RSOR.Log 𝒮) ProbComp) :=
  Protocols.RSOR.oracle (S := 𝒮) (m := ProbComp)
    (fun h o => pure (if h = Role.relay ∧ o.1 = Hv then stepOf geom (lastRes geom rc (D o.2))
      else procO h o))
    (fun h m o => pure (if h = Role.relay ∧ o.1 = Hv then
        replyOf cipher geom m (lastRes geom rc (D o.2))
      else replyO h m o)) {}

set_option maxHeartbeats 2000000 in
/-- **A relay that answers the last layer of a path, in closed form.** From that layer's tag
and keystream it does what `lastRes` says: its blinding factor and its other keys are not
read. -/
theorem hdrRelay_eq_lastRelay
    (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom)) {n : ℕ}
    (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys) (Hv : Vector UInt8 geom.headerLength)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) (ks : ℕ → ByteArray) (tag : ℕ →
        ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ) (rc : Name)
    (hi : i + 1 = path.size) (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (F : ByteArray) (hF : nikeFragment geom path ByteArray.empty i = .ok F)
    (hcmd : path[i]!.commands = [RoutingCommand.recipient rc])
    (hksi : ks i = U) (htagi : tag i (hdrMsg geom ks tag ge filler path i) = Util.Bytes.ofVector T)
    (hHv : Util.Bytes.ofVector Hv = layerHdr geom ks tag ge filler path i) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U t Hv D {} =
        lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO Hv rc D := by
  obtain ⟨hnnh, hper, hrouting, -⟩ := id hvalid
  have hproc := fun (o : Onion geom) (ho : o.1 = Hv) =>
    procD_join_last nike geom T U t (D o.2) ks tag ge filler path i o hi hnnh (by omega) hrouting
      hn hfill hks htag hge F hF
      (by
        rw [hcmd]
        intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]
        intro hcon
        cases hcon)
      (by rw [hcmd]; rfl) (by rw [hcmd]; rfl) hksi htagi (by rw [ho]; exact hHv) (by omega)
  refine congrArg₂ (fun p r => Protocols.RSOR.oracle (S := 𝒮) (m := ProbComp) p r {})
    (funext fun h => funext fun o => congrArg pure ?_)
    (funext fun h => funext fun m => funext fun o => congrArg pure ?_)
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · refine Eq.trans (ite_eq_left hc) (Eq.trans ?_ (Eq.symm (ite_eq_left hc)))
      dsimp only
      rw [hproc o hc.2, hcmd]
      unfold lastRes
      split
      · exact stepOf_tag geom _ _ _ _
      · rfl
    · exact Eq.trans (ite_eq_right hc) (Eq.symm (ite_eq_right hc))
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · refine Eq.trans (ite_eq_left hc) (Eq.trans ?_ (Eq.symm (ite_eq_left hc)))
      dsimp only
      rw [hproc o hc.2, hcmd]
      unfold lastRes
      split
      · exact replyOf_tag cipher geom _ _ _ _ _
      · rfl
    · exact Eq.trans (ite_eq_right hc) (Eq.symm (ite_eq_right hc))

set_option maxHeartbeats 2000000 in
/-- **At the end of the path, world 1's patched relay is world 0's relay in closed form.**
World 1's relay answers the replacement's header as its last hop, for the replacement's
recipient `rc₁` and with its block decrypted by `D₁`; the patch turns a delivery into the
original's, and answers the unchanged onion with the original's reply. This is the last-hop
relay for the original's recipient with the block decrypted by `D₀`, when: for the unchanged
block both decryptions begin with the zero tag and `D₀`'s carries the original's message and
reply; for a changed block neither begins with the zero tag. -/
theorem hdrRelay_patchWith_last {pk : RSOR.Key nike}
    {keys : Role → RSOR.Key nike × nike.PrivateKey} (names : Role → Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮) (honAt nike cipher macS kdfS streamS geom hvalid
        hmactag h16 .relay names pk keys))
    (hx : ¬ c.pos + 1 < c.req.fwd.hops.length) (r : RSOR.Randomness nike geom)
    (mine next : Onion geom)
    (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom)) {n : ℕ}
    (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys) (D₁ D₀ : Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength) → Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) (rc₁ : Name)
    (hstep : ∀ o : Onion geom, o.1 = mine.1 →
      stepOf geom (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ => .ok t)
          (fun _ _ => D₁ o.2) (join o)) = stepOf geom (lastRes geom rc₁ (D₁ o.2)))
    (hrep : ∀ (m : Msg geom) (o : Onion geom), o.1 = mine.1 →
      replyOf cipher geom m (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ =>
          .ok t) (fun _ _ => D₁ o.2) (join o)) = replyOf cipher geom m (lastRes geom rc₁ (D₁ o.2)))
    (hu1 : ((Util.Bytes.ofVector (D₁ mine.2)).extract 0 geom.payloadTagLength).data.all (· == 0) =
        true) (hu0 : ((Util.Bytes.ofVector (D₀ mine.2)).extract 0 geom.payloadTagLength).data.all
        (· == 0) = true)
    (hmsg : KEMSphinx.RSOR.msgOf geom ((Util.Bytes.ofVector (D₀ mine.2)).extract
        geom.payloadTagLength (geom.payloadTagLength + geom.forwardPayloadLength)) = c.req.msg)
    (hne : ∀ y, y ≠ mine.2 → ¬ ((Util.Bytes.ofVector (D₁ y)).extract 0
        geom.payloadTagLength).data.all (· == 0) = true ∧ ¬ ((Util.Bytes.ofVector (D₀ y)).extract 0
        geom.payloadTagLength).data.all (· == 0) = true)
    (hreply : ∀ (m : Msg geom) (out : Option (Name × Onion geom)),
      (c.patchWith next r mine).reply Role.relay m mine out
        = replyOf cipher geom m (lastRes geom c.req.receiver (D₀ mine.2))) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U t mine.1 D₁
        (c.patchWith next r mine)
      = lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO mine.1
          c.req.receiver D₀ := by
  refine Protocols.RSOR.oracle_pure_patch (S := 𝒮) _ _ _ _ _ (fun h o => ?_) (fun h m o => ?_)
  · unfold Protocols.RSOR.ForwardChallenge.patchWith
    dsimp only
    by_cases hc : h = Role.relay ∧ o.1 = mine.1
    · refine Eq.trans (ite_eq_left hc) (Eq.trans (dite_eq_right hx) (congrArg pure ?_))
      refine Eq.trans (congrArg (Option.map _) (Eq.trans (ite_eq_left hc) (hstep o hc.2)))
        (Eq.symm (Eq.trans (ite_eq_left hc) ?_))
      unfold lastRes
      by_cases ho : o.2 = mine.2
      · rw [ho, ite_eq_left hu0, ite_eq_left hu1]
        show some (Protocols.RSOR.Step.deliver (KEMSphinx.RSOR.msgOf geom _) c.req.receiver)
          = some (Protocols.RSOR.Step.deliver c.req.msg c.req.receiver)
        rw [hmsg]
        rfl
      · rw [ite_eq_right (hne o.2 ho).2, ite_eq_right (hne o.2 ho).1]
        rfl
    · exact Eq.trans (ite_eq_right hc) (congrArg pure (Eq.trans (ite_eq_right hc)
        (Eq.symm (ite_eq_right hc))))
  · by_cases hc : h = Role.relay ∧ o.1 = mine.1
    · obtain ⟨rfl, ho1⟩ := hc
      refine Eq.symm (Eq.trans (ite_eq_left ⟨rfl, ho1⟩) ?_)
      by_cases ho : o.2 = mine.2
      · obtain rfl : o = mine := Prod.ext ho1 ho
        exact (hreply m _).symm
      · unfold Protocols.RSOR.ForwardChallenge.patchWith
        refine Eq.symm (Eq.trans (ite_eq_right fun hcon => ho (by rw [hcon.2.1])) ?_)
        refine Eq.trans (ite_eq_left ⟨rfl, ho1⟩) (Eq.trans (hrep m o ho1) ?_)
        unfold lastRes
        rw [ite_eq_right (hne o.2 ho).2, ite_eq_right (hne o.2 ho).1]
    · unfold Protocols.RSOR.ForwardChallenge.patchWith
      exact Eq.trans (ite_eq_right fun hcon => hc ⟨hcon.1, by rw [hcon.2.1]⟩)
        (Eq.trans (ite_eq_right hc) (Eq.symm (ite_eq_right hc)))

include hvalid hmactag h16 in
set_option maxHeartbeats 2000000 in
/-- **The exit relay's reply to the sender's payload is the first layer of the reply onion**,
when the request's two paths build. -/
theorem replyOf_body (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (m : Msg geom)
    (hr : RSOR.Reliable nike cipher macS kdfS streamS geom q r) (hb : 0 < q.back.hops.length)
    (hsh : Vector UInt8 32) (rc : Name) :
    replyOf cipher geom m (some (some (RSOR.body nike macS kdfS streamS geom q r), hsh,
        [RoutingCommand.recipient rc], none))
      = some ((q.back.hops[0]'hb).name,
        RSOR.formBack nike cipher macS kdfS streamS geom q r m ⟨0, hb⟩) := by
  obtain ⟨-, -, x0, sprp, hx0, -, -, hs1, hxs, -, hnp, hfirst⟩ :=
    RSOR.reply_spec nike cipher macS kdfS streamS geom hvalid hmactag h16 q r m hr hb
  have hss : (RSOR.surb nike macS kdfS streamS geom q r).1.size = geom.surbLength := by
    have := hnp
    unfold SURB.newPacketFromSURB at this
    by_contra hne
    simp [hne] at this
    cases this
  have hfl : (RSOR.body nike macS kdfS streamS geom q r).get! 0 = 1 := by
    have hne : ¬ q.back.hops.isEmpty := by
      rw [List.isEmpty_iff]
      exact List.ne_nil_of_length_pos hb
    have h2 : (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray).size = 2 := rfl
    unfold RSOR.body
    rw [KEMSphinx.get!_eq_getElem _ 0 (by
        rw [ByteArray.size_append, ByteArray.size_append, h2]
        omega),
      ByteArray.getElem_append_left (by rw [ByteArray.size_append, h2]; omega),
      ByteArray.getElem_append_left (by rw [h2]; omega)]
    simp only [hne]
    rfl
  have hsb : (RSOR.body nike macS kdfS streamS geom q r).extract 2 (2 + geom.surbLength) =
      (RSOR.surb nike macS kdfS streamS geom q r).1 := by
    unfold RSOR.body
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
      rw [ByteArray.size_append, hss]
      exact Nat.le_refl _)]
    exact KEMSphinx.extract_append_tail _ _ _ _ rfl (by rw [hss])
  unfold replyOf RSOR.formBack
  dsimp only
  rw [ite_eq_left ⟨rfl, hfl⟩, hsb, hnp, hx0]
  dsimp only
  rw [hfirst]
  rfl

/-- **Two headers that end at the same hop have the same bytes under that hop's tag**, when the
hops in front are the same and the head of the one's keystream is the other's, shifted by the
difference of what the two mask. -/
theorem hdrMsg_shift_last (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path path' : Array PathHop) (i : ℕ)
    (hi : i + 1 = path.size) (hi' : i + 1 = path'.size) (F F' : ByteArray)
    (hF : nikeFragment geom path ByteArray.empty i = .ok F)
    (hF' : nikeFragment geom path' ByteArray.empty i = .ok F')
    (hX : (F ++ (if geom.nrHops > path.size then filler else ByteArray.empty)).size =
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
        geom.perHopRoutingInfoLength)) (hX' : (F' ++ (if geom.nrHops > path'.size then filler' else
        ByteArray.empty)).size = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1)
        * geom.perHopRoutingInfoLength))
    (hks' : ∀ k, (ks' k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hge : ge
        i = ge' i) (hfront : ∀ m < i, ks m = ks' m)
    (hshift : (ks i).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
        geom.perHopRoutingInfoLength)
      = xorBytes ((ks' i).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i +
          1) * geom.perHopRoutingInfoLength)) (xorBytes (F' ++ (if geom.nrHops > path'.size then
          filler' else ByteArray.empty)) (F ++ (if geom.nrHops > path.size then filler else
          ByteArray.empty)))) :
    hdrMsg geom ks tag ge filler path i = hdrMsg geom ks' tag' ge' filler' path' i := by
  have hp : (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else ByteArray.empty)
      = (if i > 0 then KEMSphinx.padAt geom ks' (i - 1) else ByteArray.empty) := by
    by_cases hj : i > 0
    · rw [ite_eq_left hj, ite_eq_left hj]
      exact KEMSphinx.padAt_congr geom ks ks' (i - 1) fun m hm => hfront m (by omega)
    · rw [ite_eq_right hj, ite_eq_right hj]
  have hsz : ((ks' i).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1)
      * geom.perHopRoutingInfoLength)).size = ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength) := by
    rw [ByteArray.size_extract, hks']
    omega
  rw [hdrMsg_last geom ks tag ge filler path i hi F hF,
    hdrMsg_last geom ks' tag' ge' filler' path' i hi' F' hF', hshift,
    KEMSphinx.xorBytes_shift _ _ _ (hX.trans hX'.symm) (hsz.trans hX.symm), hge, hp]

/-- **The bytes under the tag of the last layer have their length.** -/
theorem hdrMsg_size_last (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ)
    (hi : i + 1 = path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (hge : (ge i).size = nike.publicKeySize)
    (F : ByteArray) (hF : nikeFragment geom path ByteArray.empty i = .ok F) :
    (hdrMsg geom ks tag ge filler path i).size = 2 + nike.publicKeySize + geom.routingInfoLength :=
        by
  obtain ⟨k, hk⟩ : ∃ k, geom.nrHops = i + 1 + k := ⟨geom.nrHops - (i + 1), by omega⟩
  have e1 : geom.routingInfoLength = (i + 1) * geom.perHopRoutingInfoLength
      + k * geom.perHopRoutingInfoLength := by
    rw [hrouting, hk, Nat.mul_comm, Nat.add_mul]
  have e2 : (i + 1) * geom.perHopRoutingInfoLength
      = i * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  have hjp : (i + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by omega
  have hFs : F.size = geom.perHopRoutingInfoLength :=
    nikeFragment_size geom path _ i hnnh hle F hF
  have hB : (if geom.nrHops > path.size then filler else ByteArray.empty).size = k *
      geom.perHopRoutingInfoLength := by
    by_cases hg : geom.nrHops > path.size
    · rw [ite_eq_left hg, hfill, show geom.nrHops - path.size = k by omega]
    · rw [ite_eq_right hg, show k = 0 by omega, Nat.zero_mul]
      rfl
  have hPd : (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else ByteArray.empty).size = i *
      geom.perHopRoutingInfoLength := padFront_size geom ks hks i hjp
  have hFB : F.size + (if geom.nrHops > path.size then filler else ByteArray.empty).size =
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength) := by
    rw [hFs, hB]
    omega
  have hR : ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength) + (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else
      ByteArray.empty).size = geom.routingInfoLength := by
    rw [hPd]
    omega
  have hU : (ks i).size = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength) + (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else
      ByteArray.empty).size + geom.perHopRoutingInfoLength := by
    rw [hks, hPd]
    omega
  have hm0 : (hdrMsg geom ks tag ge filler path i) = v0AD ++ ge i ++ (xorBytes (F ++ (if
      geom.nrHops > path.size then filler else ByteArray.empty)) ((ks i).extract 0
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength)) ++ (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else
      ByteArray.empty)) :=
    (hdrMsg_last geom ks tag ge filler path i hi F hF).trans ByteArray.append_assoc
  obtain ⟨-, -, -, -, -, -, b6⟩ := peel_bytes nike geom (ks i) (ge i) F (if geom.nrHops > path.size
      then filler else ByteArray.empty) (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else
      ByteArray.empty)
    ByteArray.empty ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
        geom.perHopRoutingInfoLength) hU hFB hR hge
  rw [hm0]
  exact b6

set_option maxHeartbeats 2000000 in
/-- **World 0's relay on the last layer of an onion.** The relay at the last hop `j` of `q`'s
forward path holds the tag `T` and the keystream `U` of its layer. Under that layer's header it
is the last-hop relay for `q`'s recipient. -/
theorem hdrRelay_onion_last (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (K : List HopKeys) (j : ℕ) (U : ByteArray) (T : Vector UInt8 macS.tagSize)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) (hj : j + 1 = q.fwd.hops.length)
    (hU : U.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (ha : a.size = nike.publicKeySize) (hT : pathBuilds geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) 1) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U (K.toArray[j]!)
        (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
        geom.routingInfoLength) (onionMsgStream nike macS streamS geom q r a K j U)) ++
        Util.Bytes.ofVector T)) D {}
      = lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO
          (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
          geom.routingInfoLength) (onionMsgStream nike macS streamS geom q r a K j U)) ++
          Util.Bytes.ofVector T)) q.receiver D := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hsz := RSOR.path_size nike q.fwd [.recipient q.receiver]
  have hlen : q.fwd.hops.length ≤ geom.nrHops := q.fwd.length_le
  have hjl : j < q.fwd.hops.length := by omega
  have hjP : j + 1 = (RSOR.path nike q.fwd [.recipient q.receiver]).size := hj.trans hsz.symm
  have hnP : (RSOR.path nike q.fwd [.recipient q.receiver]).size ≤ geom.nrHops :=
    le_of_eq_of_le hsz hlen
  have hjlt : j < (RSOR.path nike q.fwd [.recipient q.receiver]).size :=
    lt_of_lt_of_eq hjl hsz.symm
  have hmul : (geom.nrHops - (RSOR.path nike q.fwd [.recipient q.receiver]).size) *
      geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1).size =
      (geom.nrHops - (RSOR.path nike q.fwd [.recipient q.receiver]).size) *
      geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hks : ∀ k, ((Function.update (keysKs geom streamS K.toArray) j U) k).size =
      geom.routingInfoLength + geom.perHopRoutingInfoLength :=
    fun k => by
      by_cases hk : k = j
      · rw [hk, Function.update_self]
        exact hU
      · rw [Function.update_of_ne hk]
        exact streamS.keystream_size _ _ _
  have htag : ∀ m x, ((Function.update (keysTag macS K.toArray) j fun _ => Util.Bytes.ofVector T) m
      x).size = macLength := fun m x => by
    by_cases hm : m = j
    · rw [hm, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hm]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  have hge : ((blindElem nike a K.toArray) j).size = nike.publicKeySize := (blindElem_size nike _ _
      _).trans ha
  obtain ⟨F, hF⟩ := pathBuilds_fragment geom (RSOR.path nike q.fwd [.recipient q.receiver]) hT
  rw [show (RSOR.path nike q.fwd [.recipient q.receiver]).size - 1 = j by rw [← hjP]; rfl] at hF
  have hcmd : (RSOR.path nike q.fwd [.recipient q.receiver])[j]!.commands =
      [RoutingCommand.recipient q.receiver] := by
    rw [RSOR.path_getElem! nike _ _ _ hjl]
    exact ite_eq_left hj
  have hM : (onionMsgStream nike macS streamS geom q r a K j U).size = 2 + nike.publicKeySize +
      geom.routingInfoLength :=
    hdrMsg_size_last nike geom (Function.update (keysKs
        geom streamS K.toArray) j U) (keysTag macS K.toArray) (blindElem nike a K.toArray)
        (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
        q.fwd [.recipient q.receiver]) j hjP hnnh (by omega) hrouting hnP hfill hks hge F hF
  rw [Util.Bytes.ofVector_toVecN _ hM]
  refine hdrRelay_eq_lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T
      U _ _ D (Function.update (keysKs geom streamS K.toArray) j U) (Function.update (keysTag macS
      K.toArray) j fun _ => Util.Bytes.ofVector T) (blindElem nike a K.toArray) (RSOR.filler nike
      geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient
      q.receiver]) j q.receiver
    hjP hnP hfill hks htag hge F hF hcmd (Function.update_self _ _ _)
    (by rw [Function.update_self]) ?_
  rw [Util.Bytes.ofVector_toVecN _ (by
    rw [ByteArray.size_append, hM, Util.Bytes.size_ofVector, hhdr, had, hmactag])]
  unfold layerHdr onionMsgStream
  rw [hdrMsg_update_tag geom _ _ _ _ _ j hjlt, Function.update_self]

/-- **World 0 on a draw, at the end of the path, against the last-hop relay in closed form.**
This holds when the path's last hop builds. The relay's blinding seed is not read. -/
theorem strRun_fwd0_last (names : Role → Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A) (U : KEMSphinx.Keystream geom) (u v : Vector
        UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : (x.2.2.c.pos : ℕ) + 1 = x.2.2.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) 1) :
    strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) A x U u v
      = (simulateQ (lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) x)) ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) x))
          (Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x U
            ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
                names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x U)))
          x.2.2.c.req.receiver (fun y => if y = u then (forwardPay nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x) else v))
        (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) A x U u)).run' x.2.2.log := by
  have hk : (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray[(x.2.2.c.pos :
      ℕ)]!
      = restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) x) default).1 default :=
    (payKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        x) default).2
  have h := hdrRelay_onion_last nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      x)) ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) x)) x.2.2.c.req x.2.2.o (groupElem nike (drawKey nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      x.2.2) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray 0) (forwardKeys0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) x) default)) x.2.2.c.pos
    (Util.Bytes.ofVector U) (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x U) (fun y => if y = u
        then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) x) else v) hj (Util.Bytes.size_ofVector _)
    (Util.Bytes.size_ofVector _) hT
  rw [hk] at h
  unfold strRun
  rw [strRunP_eq]
  exact congrArg (fun impl => (simulateQ impl (strGuess nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A x U
      u)).run' x.2.2.log) h

set_option maxHeartbeats 16000000 in
/-- **World 1 on a draw, at the end of the path, against the last-hop relay in closed form.**
The relay patched around the replacement's layer is the last-hop relay for the original's
recipient, with the unchanged block decrypted to the original's payload and a changed block to
`x.2.v`. This holds when the replacement's path builds, both bodies have a payload's length, the
original's two paths build, and `x.2.v` does not begin with the zero tag. -/
theorem finOwnRun_last (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names A)
    (hlast : (x.2.p.c.pos : ℕ) + 1 = x.2.p.c.req.fwd.hops.length)
    (hT' : pathBuilds geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) (RSOR.path nike
        ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]).size)
    (hb : (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1).size =
        geom.forwardPayloadLength)
    (hb' : (RSOR.body nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o)).size = geom.forwardPayloadLength)
    (hr : RSOR.Reliable nike cipher macS kdfS streamS geom x.2.p.c.req x.2.o.1)
    (hv : ¬ ((Util.Bytes.ofVector x.2.v).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
        :
    finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x
      = (simulateQ (lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))))
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2)))) (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).1
          x.2.p.c.req.receiver (fun y => if y = x.2.u then Util.Bytes.toVecN _ (((⟨Array.replicate
          geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS streamS geom
          x.2.p.c.req x.2.o.1)) else x.2.v))
        (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) A (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2) x.2.U x.2.u)).run' x.2.p.log := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hpos : (x.2.p.c.pos : ℕ) < x.2.p.c.req.fwd.hops.length := x.2.p.c.pos.isLt
  have hlen1 : (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length = x.2.p.c.pos + 1 := by
    show (List.take ((x.2.p.c.pos : ℕ) + 1) x.2.p.c.req.fwd.hops).length = x.2.p.c.pos + 1
    rw [List.length_take]
    omega
  have hpos1 : (x.2.p.c.pos : ℕ) < (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length :=
    lt_of_lt_of_eq (Nat.lt_succ_self _) hlen1.symm
  have hszP1 : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size = x.2.p.c.pos + 1 := (RSOR.path_size nike
      _ _).trans hlen1
  have hP1 : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) = (RSOR.path nike (x.2.p.c.req.fwd.take
      (x.2.p.c.pos + 1)) [.recipient x.2.o.2.2.1]) := rfl
  have hnP1 : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size ≤ geom.nrHops := by
    have h2 : x.2.p.c.req.fwd.hops.length ≤ geom.nrHops := x.2.p.c.req.fwd.length_le
    omega
  have hfill : (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).1).size = (geom.nrHops - (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size) *
      geom.perHopRoutingInfoLength := by
    have hmul : (geom.nrHops - (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size) *
        geom.perHopRoutingInfoLength
        ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hT1' : pathBuilds geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) 1 :=
    nikeHdrTrace_isSome_of_le geom _ _ _ _ (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o).receiver]) 1 x.2.p.c.pos (by
      rw [show 1 + (x.2.p.c.pos : ℕ) = (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]).size by omega]
      exact hT')
  obtain ⟨F0, hF0⟩ := pathBuilds_fragment geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) hT1'
  rw [show (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]).size - 1 = (x.2.p.c.pos : ℕ) by omega] at hF0
  have hks1 : ∀ k, ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) k).size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = (x.2.p.c.pos : ℕ)
    · rw [hk, Function.update_self]
      exact Util.Bytes.size_ofVector _
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  have htg1 : ∀ i m, ((Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
      (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
      (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
      i m).size = macLength := fun i m => by
    by_cases hi : i = (x.2.p.c.pos : ℕ)
    · rw [hi, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hi]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  have hge1p : ((blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) x.2.p.c.pos).size = nike.publicKeySize :=
    (blindElem_size nike _ _ _).trans (Util.Bytes.size_ofVector _)
  have hcmds : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver])[(x.2.p.c.pos : ℕ)]!.commands =
      [RoutingCommand.recipient x.2.o.2.2.1] := by
    rw [hP1, RSOR.path_getElem! nike _ _ _ hpos1]
    exact ite_eq_left hlen1.symm
  have hMsz : (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos).size = 2 + nike.publicKeySize +
      geom.routingInfoLength :=
    hdrMsg_size_last nike geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
        𝒮)) .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos hszP1.symm hnnh (by
        omega)
      hrouting hnP1 hfill hks1 hge1p F0 hF0
  have hlt := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2
  have hjk : (x.2.p.c.pos : ℕ) ≤ (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).length :=
    le_of_lt (lt_of_lt_of_eq hlt (hopKeysWith_length nike kdfS _ _ _ _ _).symm)
  have hMINE : finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x = (layerFn nike macS
      kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs
      geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
      (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
      (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
      (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem
      nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
      (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      fun _ => Util.Bytes.ofVector x.2.u) (blindElem nike (groupElem nike (drawKey nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos) :=
    onionOfStream_eq_layerFn nike cipher macS kdfS streamS geom x.2.p.c.pos ((fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
        geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U) (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
          (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
          (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
          (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]) x.2.p.c.pos))))) (Util.Bytes.ofVector x.2.u) hvalid
      hmactag le_rfl (by rw [hszP1]; omega) hjk (Util.Bytes.size_ofVector _)
      ((Util.Bytes.size_ofVector _).trans hmactag) (by rw [Util.Bytes.size_ofVector]; exact h16)
      (Util.Bytes.size_ofVector _)
  have hlastL := layerFn_last nike macS kdfS streamS geom hvalid ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o) (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
    (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector
        (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
        nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
        streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
        (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path
        nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) x.2.u hszP1.symm
        hb' hT' hMsz
    ((Util.Bytes.size_ofVector _).trans hmactag)
  have hL : layerHdr geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
      x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
      geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) (blindElem nike (groupElem nike (drawKey
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
      𝒮)) .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler
      nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos
      = (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
          (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]) x.2.p.c.pos) ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
          x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
          geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
          (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
          (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]) x.2.p.c.pos)))) := by
    unfold layerHdr
    rw [hdrMsg_update_tag geom _ _ _ _ _ x.2.p.c.pos (by rw [hszP1]; omega), Function.update_self]
  have hm1 : (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).1 =
      Util.Bytes.toVecN _ ((hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++ Util.Bytes.ofVector (macS.mac
      (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize
      + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler
      nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) := by
    rw [hMINE, hlastL]
  have hm2 : (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).2 = x.2.u := by rw
      [hMINE, hlastL]
  have hmineHdr : (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).1 =
      Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2) x.2.U
      ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U)) := by
    rw [hm1]
    show Util.Bytes.toVecN _ ((hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike
        (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path
        nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++ Util.Bytes.ofVector
        (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
        nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
        streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
        (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path
        nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
      = Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN _ (hdrMsg geom (Function.update
          (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
          x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
          .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
          ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))
        ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
            (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
            (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
            default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem
            nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
            default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
            hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
            [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
            (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).receiver]) x.2.p.c.pos)))))
    rw [Util.Bytes.ofVector_toVecN _ hMsz]
  have hproc : ∀ o : Onion geom, o.1 = (finMine nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x).1 →
      procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U)) (constStream
          (Util.Bytes.ofVector x.2.U)) geom (fun _ => .ok (restKeys (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default).1 default)) (fun _ _ => (fun y
          => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain (strPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2)) else x.2.v) o.2) (join o) = if ((Util.Bytes.ofVector ((fun y => if y =
          x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2)) else x.2.v) o.2)).extract 0 geom.payloadTagLength).data.all (· == 0) = true then
          some (some ((Util.Bytes.ofVector ((fun y => if y = x.2.u then (forwardPay nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) A).plain (strPay nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) else
              x.2.v) o.2)).extract geom.payloadTagLength
            (geom.payloadTagLength + geom.forwardPayloadLength)),
            Primitives.Hash.Sha512.sha512_256 ((blindElem nike (groupElem nike (drawKey nike cipher
                macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
                𝒮)) .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
                x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
                (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
                cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
                streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
                hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
                h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
                default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
                hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
                names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
                geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
                hmactag h16 x.2)) default)).toArray) x.2.p.c.pos),
            [RoutingCommand.recipient x.2.o.2.2.1], none)
        else none := fun o ho => by
    have ho' : Util.Bytes.ofVector o.1 = layerHdr geom (Function.update (keysKs geom streamS
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector
        x.2.U)) (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
        (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
        (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
        𝒮)) .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) (blindElem nike
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path
        nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos := by
      rw [ho, hm1, hL]
      exact Util.Bytes.ofVector_toVecN _ (by
        rw [ByteArray.size_append, hMsz, Util.Bytes.size_ofVector, hhdr, had, hmactag])
    have h := procD_join_last nike geom (strTag nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U) (Util.Bytes.ofVector x.2.U)
        (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default).1 default) ((fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) else x.2.v) o.2)
      (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag
          macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _ =>
          Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
          (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
          (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
          (S := 𝒮)) .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
          ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])
          x.2.p.c.pos))))) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
          (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
          (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos o hszP1.symm hnnh
          (by omega) hrouting hnP1 hfill hks1
      htg1 hge1p F0 hF0
      (by
        rw [hcmds]
        intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]
        intro hcon
        cases hcon)
      (by rw [hcmds]; rfl) (by rw [hcmds]; rfl) (Function.update_self _ _ _)
      (by rw [Function.update_self]; rfl) ho' (by omega)
    rw [hcmds] at h
    exact h
  have hstep : ∀ o : Onion geom, o.1 = (finMine nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x).1 →
      stepOf geom (procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U))
          (constStream (Util.Bytes.ofVector x.2.U)) geom (fun _ => .ok (restKeys (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default).1 default))
          (fun _ _ => (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2)) else x.2.v) o.2) (join o)) = stepOf geom
          (lastRes geom x.2.o.2.2.1 ((fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) else x.2.v) o.2)) := fun o ho => by
    rw [hproc o ho]
    unfold lastRes
    split
    · exact stepOf_tag geom _ _ _ _
    · rfl
  have hrep : ∀ (m : Msg geom) (o : Onion geom), o.1 = (finMine nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x).1 →
      replyOf cipher geom m (procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)
          x.2.U)) (constStream (Util.Bytes.ofVector x.2.U)) geom (fun _ => .ok (restKeys (payRest
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default).1 default))
          (fun _ _ => (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2)) else x.2.v) o.2) (join o))
        = replyOf cipher geom m (lastRes geom x.2.o.2.2.1 ((fun y => if y = x.2.u then (forwardPay
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) A).plain (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) else
            x.2.v) o.2)) := fun m o ho => by
    rw [hproc o ho]
    unfold lastRes
    split
    · exact replyOf_tag cipher geom _ _ _ _ _
    · rfl
  have hD1u : (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) else x.2.v) x.2.u = Util.Bytes.toVecN _ (((⟨Array.replicate
      geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS streamS geom ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.o))) := by
    show (if x.2.u = x.2.u then Util.Bytes.toVecN _ (encTrace (keysEnc cipher (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2)) default)).toArray) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o).receiver]).size
      (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS
          streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
          (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)))
          ((RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
          (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size - 1 - x.2.p.c.pos)) else
          x.2.v) = _
    rw [ite_eq_left rfl, show (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size - 1 -
        (x.2.p.c.pos : ℕ) = 0 by omega]
    rfl
  have hD0u : (fun y => if y = x.2.u then Util.Bytes.toVecN _ (((⟨Array.replicate
      geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS streamS geom x.2.p.c.req
      x.2.o.1)) else x.2.v) x.2.u = Util.Bytes.toVecN _ (((⟨Array.replicate geom.payloadTagLength
      0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1)) :=
      ite_eq_left rfl
  have hu1 : ((Util.Bytes.ofVector ((fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2)) else x.2.v) (finMine nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x).2)).extract 0 geom.payloadTagLength).data.all (· == 0) = true := by
    rw [hm2, hD1u]
    exact (KEMSphinx.RSOR.zeroTag_block geom (RSOR.body nike macS kdfS streamS geom ((fwd1 nike
        cipher
        macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)
        ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)) hb').1
  have hu0 : ((Util.Bytes.ofVector ((fun y => if y = x.2.u then Util.Bytes.toVecN _
      (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS
      streamS geom x.2.p.c.req x.2.o.1)) else x.2.v) (finMine nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x).2)).extract 0 geom.payloadTagLength).data.all (· == 0) = true := by
    rw [hm2, hD0u]
    exact (KEMSphinx.RSOR.zeroTag_block geom (RSOR.body nike macS kdfS streamS geom x.2.p.c.req
        x.2.o.1)
        hb).1
  have hpl0 : (Util.Bytes.ofVector ((fun y => if y = x.2.u then Util.Bytes.toVecN _
      (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS
      streamS geom x.2.p.c.req x.2.o.1)) else x.2.v) (finMine nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x).2)).extract geom.payloadTagLength
      (geom.payloadTagLength + geom.forwardPayloadLength) = (RSOR.body nike macS kdfS streamS geom
          x.2.p.c.req x.2.o.1) := by
    rw [hm2, hD0u]
    have h := (KEMSphinx.RSOR.zeroTag_block geom (RSOR.body nike macS kdfS streamS geom x.2.p.c.req
        x.2.o.1) hb).2
    rw [Util.Bytes.size_ofVector] at h
    exact h
  have hne : ∀ y, y ≠ (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).2 → ¬
      ((Util.Bytes.ofVector ((fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2)) else x.2.v) y)).extract 0
      geom.payloadTagLength).data.all (· == 0) = true ∧ ¬ ((Util.Bytes.ofVector ((fun y => if y =
      x.2.u then Util.Bytes.toVecN _ (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++
      (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1)) else x.2.v) y)).extract 0
      geom.payloadTagLength).data.all (· == 0) = true :=
    fun y hy => by
      rw [hm2] at hy
      have e1 : (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2)) else x.2.v) y = x.2.v := ite_eq_right hy
      have e0 : (fun y => if y = x.2.u then Util.Bytes.toVecN _ (((⟨Array.replicate
          geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS streamS geom
          x.2.p.c.req x.2.o.1)) else x.2.v) y = x.2.v := ite_eq_right hy
      rw [e1, e0]
      exact ⟨hv, hv⟩
  have hb0 : 0 < x.2.p.c.req.back.hops.length :=
    List.length_pos_iff.2 fun h => by simpa [h] using x.2.p.c.sender
  have hreply : ∀ (m : Msg geom) (out : Option (Name × Onion geom)),
      (x.2.p.c.patchWith (next4Nxt nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2
          (Util.Bytes.ofVector x.1) (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16
          x)) x.2.o.1
          (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x)).reply Role.relay m
              (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x) out
        = replyOf cipher geom m (lastRes geom x.2.p.c.req.receiver ((fun y => if y = x.2.u then
            Util.Bytes.toVecN _ (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++
            (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1)) else x.2.v) (finMine nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x).2)) :=
    fun m out => by
      unfold Protocols.RSOR.ForwardChallenge.patchWith lastRes
      rw [ite_eq_left hu0, hpl0, replyOf_body nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2.p.c.req x.2.o.1 m hr hb0 default x.2.p.c.req.receiver]
      exact ite_eq_left ⟨rfl, rfl, hlast⟩
  have hPO : ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))) =
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) := by
    funext h o
    show (if h = Role.relay then stepOf geom (noneAns nike cipher macS kdfS streamS geom
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.2 (drawElem nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
            := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)) (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
        (join o)) else _) = _
    rw [drawElem_fwd1]
    rfl
  have hRO : ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))) =
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) := by
    funext h m o
    show (if h = Role.relay then replyOf cipher geom m (noneAns nike cipher macS kdfS streamS geom
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.2 (drawElem nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
            := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)) (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
        (join o)) else _) = _
    rw [drawElem_fwd1]
    rfl
  have key := hdrRelay_patchWith_last nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      x.2.p.c (by omega) x.2.o.1 (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x)
    (next4Nxt nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2 (Util.Bytes.ofVector x.1)
        (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x)) ((forwardPay nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2))) ((forwardPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) A).reply (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2))) (strTag nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U)
    (Util.Bytes.ofVector x.2.U) (restKeys (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default).1 default) (fun y => if y = x.2.u then (forwardPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) else x.2.v) (fun y =>
        if y = x.2.u then Util.Bytes.toVecN _ (((⟨Array.replicate geom.payloadTagLength 0⟩ :
        ByteArray)) ++ (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1)) else x.2.v)
        x.2.o.2.2.1 hstep hrep hu1 hu0
    (by rw [hpl0]; exact msgOf_body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1) hne hreply
  unfold finOwnRun
  rw [strRunP_eq, ← hmineHdr]
  refine (congrArg (fun impl => (simulateQ impl
    (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2) x.2.U x.2.u)).run' x.2.p.log) key).trans ?_
  rw [hPO, hRO]

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
