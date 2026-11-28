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

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
