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

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
