/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTagGame
import Cryptlib.Protocols.Sphinx.KEMSphinxLayerIn
import Cryptlib.Protocols.Sphinx.KEMSphinxTailGame
import Cryptlib.Protocols.Sphinx.KEMSphinxTailDef6

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
open Cryptlib.Util.Bytes (ofVector)

/-! # Layer unlinkability at a mix with a replay cache

The adversary is given the packet entering the honest mix and the packet the mix forwards.
`luAdvantage_le` bounds its advantage in telling that pair from a pair with nothing in common:
a packet to the mix with uniform routing info and payload, and a fresh packet on the rest of the
path. After the challenge the mix's oracle refuses packets that carry the challenge's KEM
ciphertext, as a replay cache would. Without that the two packets are linked through the oracle
(`procWith_payload_congr`). -/

section LU

open PRGScheme

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
variable (tmpl : PathHop) (restPath : Array PathHop) (payload : ByteArray)

/-- The filler length for a path of the honest mix followed by `restPath`. -/
abbrev luA : Nat := (geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength

/-- The length of a payload with its tag. -/
abbrev luL : Nat := geom.payloadTagLength + geom.forwardPayloadLength

/-- A packet from its parts: KEM ciphertext, routing info, the MAC over both, payload. -/
def luPkt (ctb : ByteArray) (km : Vector UInt8 32) (W : Vector UInt8 geom.routingInfoLength)
    (pay : ByteArray) : ByteArray :=
  v0AD ++ ctb ++ ofVector W
    ++ ofVector (macS.mac (ofVector km) (v0AD ++ ctb ++ ofVector W ++ ByteArray.empty)) ++ pay

/-- The routing info the mix's layer hides, read off the forwarded packet: the mix's own
fragment, then the forwarded routing info without its last block. -/
def luX (pk : kem.PublicKey) (fwd : ByteArray) : Option ByteArray :=
  match kemRiFragment kem geom (#[honestHop kem tmpl pk] ++ restPath)
      #[ByteArray.empty, fwd.extract 2 (2 + kem.ciphertextSize)]
      (fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength))
      (#[honestHop kem tmpl pk] ++ restPath).size 0 with
  | .ok frag => some (frag ++ fwd.extract (2 + kem.ciphertextSize)
      (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength))
  | .error _ => none

/-- The challenger's randomness other than the mix's seed: the other hops' seeds and the
filler. -/
abbrev LUOth := Vector (Vector UInt8 32) restPath.size × Vector UInt8 (luA geom restPath)

/-- The payload inside the mix's layer: the forwarded packet's payload. -/
def luMsg (o : LUOth geom restPath) (uB : Vector UInt8 geom.perHopRoutingInfoLength) :
    Vector UInt8 (luL geom) :=
  match blockView kem cipher macS kdfS streamS geom restPath payload o.1 o.2 uB with
  | some fwd => Util.Bytes.toVecN (luL geom) (fwd.extract (payloadOffset kem geom) fwd.size)
  | none => Util.Bytes.toVecN (luL geom) ByteArray.empty

/-- The pair the adversary is given, from the mix's KEM ciphertext, its MAC key, the two parts
of its header keystream, and the bytes of the payload. -/
def luViewG (pk : kem.PublicKey) (o : LUOth geom restPath) (ctb : ByteArray)
    (km : Vector UInt8 32) (uA : Vector UInt8 geom.routingInfoLength)
    (uB : Vector UInt8 geom.perHopRoutingInfoLength) (pay : ByteArray) :
    Option (ByteArray × ByteArray) :=
  (blockView kem cipher macS kdfS streamS geom restPath payload o.1 o.2 uB).bind fun fwd =>
    (luX kem geom tmpl restPath pk fwd).map fun X =>
      (luPkt macS geom ctb km (Util.Bytes.toVecN geom.routingInfoLength (xorBytes (ofVector uA) X))
        pay, fwd)

/-- The header keystream in two parts, as a generator from the header key and IV: the part that
masks the routing info, and the last block. The seed is the IV and the key. -/
def streamSplitPRG : PRGScheme (Vector UInt8 16 × Vector UInt8 32)
    (Vector UInt8 geom.routingInfoLength × Vector UInt8 geom.perHopRoutingInfoLength) :=
  ⟨fun k =>
    (Util.Bytes.toVecN geom.routingInfoLength ((streamS.keystream (ofVector k.2) (ofVector k.1)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0 geom.routingInfoLength),
     Util.Bytes.toVecN geom.perHopRoutingInfoLength ((streamS.keystream (ofVector k.2) (ofVector k.1)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract geom.routingInfoLength
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)))⟩

/-- The pair, from the mix's KEM ciphertext and its four keys. -/
def luKeyView (pk : kem.PublicKey) (o : LUOth geom restPath) (c : kem.Ciphertext) (t : KeyTuple) :
    Option (ByteArray × ByteArray) :=
  luViewG kem cipher macS kdfS streamS geom tmpl restPath payload pk o
    (ofVector (kem.encodeCiphertext c)) t.2.2.1
    ((streamSplitPRG streamS geom).gen (t.2.1, t.2.2.2)).1
    ((streamSplitPRG streamS geom).gen (t.2.1, t.2.2.2)).2
    (cipher.encrypt t.1.toArray (ofVector t.2.1)
      (ofVector (luMsg kem cipher macS kdfS streamS geom restPath payload o
        ((streamSplitPRG streamS geom).gen (t.2.1, t.2.2.2)).2)))

/-- The real pair: the packet built on the honest mix followed by `restPath`, and what the mix
forwards. -/
def luRealView (ks s : Vector UInt8 32) (o : LUOth geom restPath) : Option (ByteArray × ByteArray) :=
  match newKEMPacket kem cipher macS kdfS streamS geom (#[s] ++ o.1.toArray) (ofVector o.2)
      (#[honestHop kem tmpl (keygenOf kem ks).1] ++ restPath) payload with
  | .ok pkt =>
    (forwardedView kem cipher macS kdfS streamS geom (honestHop kem tmpl (keygenOf kem ks).1)
      restPath payload (skBytes kem ks) s o.1 o.2).map fun fwd => (pkt, fwd)
  | .error _ => none

set_option maxHeartbeats 1000000 in
/-- **The exact step.** The real pair is the keyed pair, with the keys the KDF derives from the
encapsulated secret. -/
theorem luRealView_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hrest : 1 ≤ restPath.size)
    (hcmdnn : ∀ c ∈ tmpl.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ tmpl.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (ks s : Vector UInt8 32) (o : LUOth geom restPath)
    (hpp : kemSelfPublicKeyBytes kem (skBytes kem ks) = pkBytes kem ks)
    (hrel : ∀ j, j < restPath.size + 1 →
      kem.Reliable (kem.stateFromSeed (#[s] ++ o.1.toArray)[j]!))
    (pkt : ByteArray)
    (hnk : newKEMPacket kem cipher macS kdfS streamS geom (#[s] ++ o.1.toArray) (ofVector o.2)
      (#[honestHop kem tmpl (keygenOf kem ks).1] ++ restPath) payload = Except.ok pkt) :
    luRealView kem cipher macS kdfS streamS geom tmpl restPath payload ks s o
      = luKeyView kem cipher macS kdfS streamS geom tmpl restPath payload (keygenOf kem ks).1 o
          (encapOf kem (keygenOf kem ks).1 s).1
          ((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2) := by
  have hfv := forwardedView_eq kem cipher macS kdfS streamS geom hvalid hmactag h16
    (honestHop kem tmpl (keygenOf kem ks).1) restPath payload (skBytes kem ks) hrest hpp
    hcmdnn hcmdnh s o.1 o.2 hrel pkt hnk
  have hp0 : (#[honestHop kem tmpl (keygenOf kem ks).1] ++ restPath)[0]!
      = honestHop kem tmpl (keygenOf kem ks).1 := by simp
  have hs0 : (#[s] ++ o.1.toArray)[0]! = s := by simp
  have hpsize : (#[honestHop kem tmpl (keygenOf kem ks).1] ++ restPath).size = restPath.size + 1 := by
    simp; omega
  obtain ⟨tag, cmds, fwd, ct, ss, frag, henc, hunw, hfrag, hpkt⟩ :=
    newKEMPacket_layer kem cipher macS kdfS streamS geom hvalid hmactag h16
      (#[s] ++ o.1.toArray) (ofVector o.2) (#[honestHop kem tmpl (keygenOf kem ks).1] ++ restPath)
      payload pkt (skBytes kem ks) (by rw [hpsize]; omega) (by rw [hp0]; exact hpp)
      (by rw [hpsize]; exact hrel) (by rw [hp0]; exact hcmdnn) (by rw [hp0]; exact hcmdnh) hnk
  rw [hp0, hs0] at henc
  obtain ⟨hct, hss⟩ := kemEncap_encapOf kem _ _ _ _ henc
  have hfw : forwardedView kem cipher macS kdfS streamS geom
      (honestHop kem tmpl (keygenOf kem ks).1) restPath payload (skBytes kem ks) s o.1 o.2
      = some (ofVector fwd) := by
    unfold forwardedView
    rw [hnk]
    dsimp only
    rw [hunw]
  have hB : ((streamSplitPRG streamS geom).gen
      (((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2).2.1,
       ((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2).2.2.2)).2
      = firstBlock kem kdfS streamS geom (honestHop kem tmpl (keygenOf kem ks).1) s := by
    unfold firstBlock tailPadBlock headerKeystream
    rw [kemHopKeys_encapOf kem kdfS _ (keygenOf kem ks).1 rfl s]
    show Util.Bytes.toVecN _ (ByteArray.extract _ _ _) = Util.Bytes.toVecN _ (ByteArray.extract _ _ _)
    congr 2 <;> omega
  have hblock : blockView kem cipher macS kdfS streamS geom restPath payload o.1 o.2
      (firstBlock kem kdfS streamS geom (honestHop kem tmpl (keygenOf kem ks).1) s)
      = some (ofVector fwd) := by
    unfold blockView
    rw [← hfv]
    exact hfw
  have hX : luX kem geom tmpl restPath (keygenOf kem ks).1 (ofVector fwd)
      = some (frag ++ (ofVector fwd).extract (2 + kem.ciphertextSize)
        (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength)) := by
    unfold luX
    rw [hfrag]
  unfold luRealView luKeyView luViewG luMsg
  rw [hnk, hB, hblock]
  dsimp only
  rw [hfw]
  simp only [Option.map_some, Option.bind_some]
  rw [hX]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  -- Sizes.
  obtain ⟨-, -, -, hheader, hpacket, -⟩ := id hvalid
  have hadL : adLength = 2 := rfl
  have hv0 : v0AD.size = 2 := rfl
  have hmacL : macLength = 32 := rfl
  have hpay := (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hnk).1
  have hpktsize : pkt.size = geom.packetLength :=
    newKEMPacket_size kem cipher macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hnk hpay
  have hfsize : (ofVector fwd).size = pkt.size := Util.Bytes.size_ofVector _
  have hctsize : ct.size = kem.ciphertextSize := kemEncap_size kem _ _ ct ss henc
  have hkssize : (streamS.keystream (ofVector (deriveHopKeys kdfS ss).headerEncryption)
      (ofVector (deriveHopKeys kdfS ss).headerEncryptionIV)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
      = geom.routingInfoLength + geom.perHopRoutingInfoLength := streamS.keystream_size _ _ _
  have hXsize : (frag ++ (ofVector fwd).extract (2 + kem.ciphertextSize)
      (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength)).size
      = geom.routingInfoLength := by
    have h1 := congrArg ByteArray.size hpkt
    unfold layerIn at h1
    simp only [ByteArray.size_append, size_xorBytes, Util.Bytes.size_ofVector,
      cipher.encrypt_size, ByteArray.size_extract, hv0, hctsize, hfsize] at h1 ⊢
    unfold payloadOffset at h1
    omega
  obtain ⟨ksA, hksA⟩ : ∃ ksA, ksA = (streamS.keystream
      (ofVector (deriveHopKeys kdfS ss).headerEncryption)
      (ofVector (deriveHopKeys kdfS ss).headerEncryptionIV)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0 geom.routingInfoLength :=
    ⟨_, rfl⟩
  have hksAsize : ksA.size = geom.routingInfoLength := by
    rw [hksA, ByteArray.size_extract, hkssize]; omega
  obtain ⟨X, hXdef⟩ : ∃ X, X = frag ++ (ofVector fwd).extract (2 + kem.ciphertextSize)
      (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength) := ⟨_, rfl⟩
  rw [← hXdef] at hXsize hpkt ⊢
  rw [← hksA] at hpkt
  have hgenA : ((streamSplitPRG streamS geom).gen
      (((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2).2.1,
       ((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2).2.2.2)).1
      = Util.Bytes.toVecN geom.routingInfoLength ksA := by
    rw [hksA, hss]; rfl
  have hW : ofVector (Util.Bytes.toVecN geom.routingInfoLength
      (xorBytes (ofVector (Util.Bytes.toVecN geom.routingInfoLength ksA)) X)) = xorBytes X ksA := by
    rw [Util.Bytes.ofVector_toVecN ksA hksAsize,
      Util.Bytes.ofVector_toVecN _ (by rw [size_xorBytes, hksAsize])]
    exact xorBytes_comm_of_size_eq _ _ (by rw [hksAsize, hXsize])
  have hmsg : ofVector (Util.Bytes.toVecN (luL geom)
      ((ofVector fwd).extract (payloadOffset kem geom) (ofVector fwd).size))
      = (ofVector fwd).extract (payloadOffset kem geom) pkt.size := by
    rw [hfsize]
    exact Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_extract, hfsize, hpktsize, hpacket, hheader, hadL]
      unfold payloadOffset luL
      omega)
  rw [hgenA, hmsg]
  unfold luPkt
  rw [hW]
  refine hpkt.trans ?_
  rw [hct, hss]
  rfl

/-- The setup for `hopChain_le`. The path and the message are fixed; the adversary chooses
nothing in its first phase. -/
def luSetup : HopSetup kem (Option (ByteArray × ByteArray)) Bool where
  Ch := Unit
  Oth := LUOth geom restPath
  drawOth _ := do
    let rs ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
    let f ← $ᵗ (Vector UInt8 (luA geom restPath))
    return (rs, f)
  view pk _ o c t := luKeyView kem cipher macS kdfS streamS geom tmpl restPath payload pk o c t
  final _ _ _ _ _ r := r

variable {kem cipher macS kdfS streamS geom tmpl restPath payload}
variable (A : HopAdversary (luSetup kem cipher macS kdfS streamS geom tmpl restPath payload))

/-- **The real game.** The mix's key pair is generated. A packet is built on the mix followed by
`restPath`. The adversary is given that packet and the packet the mix forwards. Its oracle
refuses packets that carry the challenge's KEM ciphertext. -/
def luReal : ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let rs ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let f ← $ᵗ (Vector UInt8 (luA geom restPath))
  simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1)
    (A.post cs.2 (luRealView kem cipher macS kdfS streamS geom tmpl restPath payload ks s (rs, f)))

/-- The draws of the real game. -/
def luDraw : ProbComp (Vector UInt8 32 × (Unit × A.St) × Vector UInt8 32
    × Vector (Vector UInt8 32) restPath.size × Vector UInt8 (luA geom restPath)) := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let rs ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let f ← $ᵗ (Vector UInt8 (luA geom restPath))
  return (ks, cs, s, rs, f)

/-- The draws the exact step does not cover: the generated private key's own public key is not
the generated public key, some seed is not `Reliable`, or the packet cannot be built. -/
def luBad (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
    (geom : Geometry) (tmpl : PathHop) (restPath : Array PathHop) (payload : ByteArray)
    (ks s : Vector UInt8 32) (o : LUOth geom restPath) : Prop :=
  ¬ (kemSelfPublicKeyBytes kem (skBytes kem ks) = pkBytes kem ks ∧
    (∀ j, j < restPath.size + 1 → kem.Reliable (kem.stateFromSeed (#[s] ++ o.1.toArray)[j]!)) ∧
    ∃ pkt, newKEMPacket kem cipher macS kdfS streamS geom (#[s] ++ o.1.toArray) (ofVector o.2)
      (#[honestHop kem tmpl (keygenOf kem ks).1] ++ restPath) payload = Except.ok pkt)

variable [SampleableType kem.Plaintext]

/-- The real game is the keyed game of `hopChain_le`, off `luBad`. -/
theorem luReal_sub_hopReal_le (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hrest : 1 ≤ restPath.size)
    (hcmdnn : ∀ c ∈ tmpl.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ tmpl.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m) :
    |(Pr{let x ← luReal A}[x = true]).toReal
      - (Pr{let x ← hopReal cipher macS kdfS streamS geom A}[x = true]).toReal|
    ≤ (Pr{let d ← luDraw A}[luBad kem cipher macS kdfS streamS geom tmpl restPath payload
        d.1 d.2.2.1 d.2.2.2]).toReal := by
  have hr : luReal A = luDraw A >>= fun d =>
      simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem d.1).2
          (encapOf kem (keygenOf kem d.1).1 d.2.2.1).1)
        (A.post d.2.1.2 (luRealView kem cipher macS kdfS streamS geom tmpl restPath payload
          d.1 d.2.2.1 d.2.2.2)) := by
    unfold luReal luDraw
    simp only [bind_assoc, pure_bind]
  have e : hopReal cipher macS kdfS streamS geom A =ᵈ luDraw A >>= fun d =>
      simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem d.1).2
          (encapOf kem (keygenOf kem d.1).1 d.2.2.1).1)
        (A.post d.2.1.2 (luKeyView kem cipher macS kdfS streamS geom tmpl restPath payload
          (keygenOf kem d.1).1 d.2.2.2 (encapOf kem (keygenOf kem d.1).1 d.2.2.1).1
          ((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem d.1).1 d.2.2.1).2))) := by
    unfold hopReal hopGame luDraw
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    simp only [luSetup, bind_assoc, pure_bind, bind_pure]
    exact EvalDistEq.rfl
  rw [hr, e.prEvent_eq (fun x => x = true)]
  exact prEvent_bind_toReal_sub_le_of_bad (luDraw A) _ _
    (fun d => luBad kem cipher macS kdfS streamS geom tmpl restPath payload d.1 d.2.2.1 d.2.2.2)
    (fun d hd => by
      obtain ⟨hpp, hrel, pkt, hnk⟩ := Classical.not_not.mp hd
      rw [luRealView_eq kem cipher macS kdfS streamS geom tmpl restPath payload hvalid hmactag h16
        hrest hcmdnn hcmdnh d.1 d.2.2.1 d.2.2.2 hpp hrel pkt hnk]) (fun x => x = true)

/-- A one-time pad on a uniform vector. -/
theorem evalDistEq_otp {δ : Type} (n : Nat) (X : ByteArray) (K : Vector UInt8 n → ProbComp δ) :
    ($ᵗ (Vector UInt8 n) >>= fun u => K (Util.Bytes.toVecN n (xorBytes (ofVector u) X)))
      =ᵈ ($ᵗ (Vector UInt8 n) >>= K) := by
  have h := evalDistEq_pair_of_bijective
    (padFiller_bijective (a := 0) (b := n) (c := n) (Nat.zero_add n) X) K
  have hp : ∀ (x : Vector UInt8 0) (y : Vector UInt8 n),
      padFiller (Nat.zero_add n) X x y = Util.Bytes.toVecN n (xorBytes (ofVector y) X) := by
    intro x y
    unfold padFiller
    rw [eq_empty_of_size_zero (ofVector x) (Util.Bytes.size_ofVector _), ByteArray.empty_append]
  simp only [hp] at h
  exact (OracleComp.EvalDistEq.bind_const _ _).symm.trans h

/-- An adversary against the payload cipher on one message: given the IV, it chooses a message of
`L` bytes; given either the message's encryption under a uniform key or `L` uniform bytes, it
guesses which. -/
structure PayloadAdversary (L : Nat) where
  St : Type
  choose : Vector UInt8 16 → ProbComp (Vector UInt8 L × St)
  guess : St → ByteArray → ProbComp Bool

/-- The experiment for `PayloadAdversary`, with the encryption for `b = true`. -/
def payloadExp (cipher : WideBlockCipher) (L : Nat) (B : PayloadAdversary L) (b : Bool) :
    ProbComp Bool := do
  let k ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let ms ← B.choose iv
  let u ← $ᵗ (Vector UInt8 L)
  B.guess ms.2 (if b then cipher.encrypt k.toArray (ofVector iv) (ofVector ms.1) else ofVector u)

/-- The payload adversary that `A` gives. -/
def luPayAdv : PayloadAdversary (luL geom) where
  St := Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 32 × (Unit × A.St)
    × Vector UInt8 32 × LUOth geom restPath
  choose iv := do
    let km ← $ᵗ (Vector UInt8 32)
    let ke ← $ᵗ (Vector UInt8 32)
    let ks ← $ᵗ (Vector UInt8 32)
    let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
      (A.pre (pkBytes kem ks))
    let s ← $ᵗ (Vector UInt8 32)
    let rs ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
    let f ← $ᵗ (Vector UInt8 (luA geom restPath))
    return (luMsg kem cipher macS kdfS streamS geom restPath payload (rs, f)
      ((streamSplitPRG streamS geom).gen (iv, ke)).2, (iv, km, ke, ks, cs, s, (rs, f)))
  guess st y :=
    simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem st.2.2.2.1).2
        (encapOf kem (keygenOf kem st.2.2.2.1).1 st.2.2.2.2.2.1).1)
      (A.post st.2.2.2.2.1.2 (luViewG kem cipher macS kdfS streamS geom tmpl restPath payload
        (keygenOf kem st.2.2.2.1).1 st.2.2.2.2.2.2
        (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem st.2.2.2.1).1 st.2.2.2.2.2.1).1))
        st.2.1 ((streamSplitPRG streamS geom).gen (st.1, st.2.2.1)).1
        ((streamSplitPRG streamS geom).gen (st.1, st.2.2.1)).2 y))

theorem payloadExp_true_evalDistEq :
    payloadExp cipher (luL geom) (luPayAdv A) true =ᵈ hopIdeal cipher macS kdfS streamS geom A := by
  unfold payloadExp luPayAdv hopIdeal hopGame
  simp only [luSetup, luKeyView, SampleableType.uniformSample_prod_eq_bind, bind_assoc, pure_bind,
    bind_pure, ↓reduceIte]
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_const _ _).symm
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun iv =>
    EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun ke =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun cs =>
    EvalDistEq.bind_right _ fun s => EvalDistEq.bind_right _ fun rs =>
    EvalDistEq.bind_right _ fun f => ?_
  exact OracleComp.EvalDistEq.bind_const _ _

/-- The draws every later game shares: a MAC key, the key pair, the adversary's first phase, the
mix's seed, and the other hops' seeds. -/
def luD : ProbComp (Vector UInt8 32 × Vector UInt8 32 × (Unit × A.St) × Vector UInt8 32
    × Vector (Vector UInt8 32) restPath.size) := do
  let km ← $ᵗ (Vector UInt8 32)
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let rs ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  return (km, ks, cs, s, rs)

/-- The adversary against the two parts of the header keystream that `A` gives. The payload is
already uniform. -/
def luStreamAdv : PRGAdversary
    (Vector UInt8 geom.routingInfoLength × Vector UInt8 geom.perHopRoutingInfoLength) := fun g =>
  luD A >>= fun d => do
    let f ← $ᵗ (Vector UInt8 (luA geom restPath))
    let U ← $ᵗ (Vector UInt8 (luL geom))
    simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem d.2.1).2
        (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1)
      (A.post d.2.2.1.2 (luViewG kem cipher macS kdfS streamS geom tmpl restPath payload
        (keygenOf kem d.2.1).1 (d.2.2.2.2, f)
        (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1))
        d.1 g.1 g.2 (ofVector U)))

omit [SampleableType kem.Plaintext] in
theorem payloadExp_false_evalDistEq :
    payloadExp cipher (luL geom) (luPayAdv A) false
      =ᵈ prgRealExperiment (streamSplitPRG streamS geom) (luStreamAdv A) := by
  unfold payloadExp luPayAdv prgRealExperiment luStreamAdv luD
  simp only [SampleableType.uniformSample_prod_eq_bind, bind_assoc, pure_bind, Bool.false_eq_true,
    ↓reduceIte]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.bind_right _ fun iv => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- The pair with nothing in common: a packet to the mix with routing info `W` and payload `pay`,
and the packet `fwdOpt`. -/
def luRandView (kem : KEM) (macS : MAC) (geom : Geometry) (tmpl : PathHop)
    (restPath : Array PathHop) (pk : kem.PublicKey) (ctb : ByteArray) (km : Vector UInt8 32)
    (W : Vector UInt8 geom.routingInfoLength) (pay : ByteArray) (fwdOpt : Option ByteArray) :
    Option (ByteArray × ByteArray) :=
  fwdOpt.bind fun fwd => (luX kem geom tmpl restPath pk fwd).map fun _ =>
    (luPkt macS geom ctb km W pay, fwd)

/-- **The ideal game.** The adversary is given a packet to the mix whose routing info and
payload are uniform, and a fresh packet on `restPath` built from its own seeds and a uniform
filler. The two share nothing but the mix's MAC key being used once. -/
def luIdeal : ProbComp Bool :=
  luD A >>= fun d => do
    let f' ← $ᵗ (Vector UInt8 (luA geom restPath + geom.perHopRoutingInfoLength))
    let U ← $ᵗ (Vector UInt8 (luL geom))
    let W ← $ᵗ (Vector UInt8 geom.routingInfoLength)
    simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem d.2.1).2
        (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1)
      (A.post d.2.2.1.2 (luRandView kem macS geom tmpl restPath (keygenOf kem d.2.1).1
        (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1))
        d.1 W (ofVector U)
        (freshView kem cipher macS kdfS streamS geom restPath payload d.2.2.2.2 f')))

/-- The game after the keystream is uniform, as a function of the forwarded packet's filler. -/
def luPostF (d : Vector UInt8 32 × Vector UInt8 32 × (Unit × A.St) × Vector UInt8 32
      × Vector (Vector UInt8 32) restPath.size)
    (uA : Vector UInt8 geom.routingInfoLength)
    (z : Vector UInt8 (luA geom restPath + geom.perHopRoutingInfoLength)) : ProbComp Bool := do
  let U ← $ᵗ (Vector UInt8 (luL geom))
  simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem d.2.1).2
      (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1)
    (A.post d.2.2.1.2
      ((freshView kem cipher macS kdfS streamS geom restPath payload d.2.2.2.2 z).bind fun fwd =>
        (luX kem geom tmpl restPath (keygenOf kem d.2.1).1 fwd).map fun X =>
          (luPkt macS geom
            (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1)) d.1
            (Util.Bytes.toVecN geom.routingInfoLength (xorBytes (ofVector uA) X)) (ofVector U), fwd)))

omit [SampleableType kem.Plaintext] in
theorem prgIdeal_luStreamAdv_evalDistEq :
    prgIdealExperiment (luStreamAdv A) =ᵈ luIdeal A := by
  unfold prgIdealExperiment luStreamAdv luIdeal
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun d => ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun uA =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  have step1 : ∀ uA : Vector UInt8 geom.routingInfoLength,
      (do let f ← $ᵗ (Vector UInt8 (luA geom restPath))
          let uB ← $ᵗ (Vector UInt8 geom.perHopRoutingInfoLength)
          luPostF A d uA (restFiller kem kdfS streamS geom restPath d.2.2.2.2 f uB))
        =ᵈ ($ᵗ (Vector UInt8 (luA geom restPath + geom.perHopRoutingInfoLength))
            >>= luPostF A d uA) := fun uA =>
    evalDistEq_pair_of_bijective
      (restFiller_bijective kem kdfS streamS geom restPath d.2.2.2.2
        (a := luA geom restPath) (b := geom.perHopRoutingInfoLength)) (luPostF A d uA)
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun uA => step1 uA) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun z => ?_
  unfold luPostF luRandView
  cases hfv : freshView kem cipher macS kdfS streamS geom restPath payload d.2.2.2.2 z with
  | none =>
    simp only [Option.bind_none]
    exact (OracleComp.EvalDistEq.bind_const _ _).trans
      (EvalDistEq.bind_right _ fun U => (OracleComp.EvalDistEq.bind_const _ _).symm)
  | some fwd =>
    simp only [Option.bind_some]
    cases hx : luX kem geom tmpl restPath (keygenOf kem d.2.1).1 fwd with
    | none =>
      simp only [Option.map_none]
      exact (OracleComp.EvalDistEq.bind_const _ _).trans
        (EvalDistEq.bind_right _ fun U => (OracleComp.EvalDistEq.bind_const _ _).symm)
    | some X =>
      simp only [Option.map_some]
      refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
      refine EvalDistEq.bind_right _ fun U => ?_
      exact evalDistEq_otp geom.routingInfoLength X fun W =>
        simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem d.2.1).2
            (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1)
          (A.post d.2.2.1.2 (some (luPkt macS geom
            (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem d.2.1).1 d.2.2.2.1).1)) d.1
            W (ofVector U), fwd)))

/-- **Layer unlinkability at a mix with a replay cache, for KEM Sphinx.** The honest mix is the
first hop of the packet the adversary is given; the rest of the path and the message are fixed.
The adversary's advantage in telling the packet entering the mix and the packet leaving it from
a packet with uniform routing info and payload and an independent fresh packet is at most the
sum of:

- the advantage of `hopKEMAdv` against the KEM, with a decapsulation oracle that refuses the
  challenge ciphertext;
- the advantage of `hopKeyAdv` in telling the four keys the KDF derives from a uniform shared
  secret from uniform keys;
- the advantage of `luPayAdv` in telling one payload encryption under a uniform key from
  uniform bytes;
- the advantage of `luStreamAdv` in telling the header keystream under a uniform key and IV
  from uniform bytes;
- the probability of `luBad`.

Nothing is assumed of the MAC: the oracle refuses the only ciphertext the MAC key belongs to. -/
theorem luAdvantage_le (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hrest : 1 ≤ restPath.size)
    (hcmdnn : ∀ c ∈ tmpl.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ tmpl.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m) :
    |(Pr{let x ← luReal A}[x = true]).toReal - (Pr{let x ← luIdeal A}[x = true]).toReal|
    ≤ |(Pr{let x ← kemCCAExp (hopKEMAdv cipher macS kdfS streamS geom A) true}[x = true]).toReal
        - (Pr{let x ← kemCCAExp (hopKEMAdv cipher macS kdfS streamS geom A) false}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (hopKeysPRG kem kdfS)
                        (hopKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                        (hopKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal|
      + |(Pr{let x ← payloadExp cipher (luL geom) (luPayAdv A) true}[x = true]).toReal
        - (Pr{let x ← payloadExp cipher (luL geom) (luPayAdv A) false}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (streamSplitPRG streamS geom)
                        (luStreamAdv A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment (luStreamAdv A)}[x = true]).toReal|
      + (Pr{let d ← luDraw A}[luBad kem cipher macS kdfS streamS geom tmpl restPath payload
          d.1 d.2.2.1 d.2.2.2]).toReal := by
  have h0 := luReal_sub_hopReal_le A hvalid hmactag h16 hrest hcmdnn hcmdnh
  have h1 := hopChain_le cipher macS kdfS streamS geom A
  have e1 := (payloadExp_true_evalDistEq A).prEvent_eq (fun x => x = true)
  have e2 := (payloadExp_false_evalDistEq A).prEvent_eq (fun x => x = true)
  have e3 := (prgIdeal_luStreamAdv_evalDistEq A).prEvent_eq (fun x => x = true)
  rw [e1, e2, e3]
  have t1 := abs_sub_le
    (Pr{let x ← luReal A}[x = true]).toReal
    (Pr{let x ← hopReal cipher macS kdfS streamS geom A}[x = true]).toReal
    (Pr{let x ← luIdeal A}[x = true]).toReal
  have t2 := abs_sub_le
    (Pr{let x ← hopReal cipher macS kdfS streamS geom A}[x = true]).toReal
    (Pr{let x ← hopIdeal cipher macS kdfS streamS geom A}[x = true]).toReal
    (Pr{let x ← luIdeal A}[x = true]).toReal
  have t3 := abs_sub_le
    (Pr{let x ← hopIdeal cipher macS kdfS streamS geom A}[x = true]).toReal
    (Pr{let x ← prgRealExperiment (streamSplitPRG streamS geom) (luStreamAdv A)}[x = true]).toReal
    (Pr{let x ← luIdeal A}[x = true]).toReal
  linarith

end LU

end Cryptlib.Protocols.Sphinx.KEMSphinx
