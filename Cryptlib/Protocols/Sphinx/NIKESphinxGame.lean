/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxHeaderFn
import Cryptlib.Protocols.Sphinx.KEMSphinxTailOracle

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.KEMSphinx (ProcResult procSpec KeyTuple)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Util.Bytes (ofVector)

/-! # The key game of NIKE Sphinx

Scherer, Weis and Strufe prove Sphinx's properties from one game on its key derivation,
Sphinx-KEM-IND-CCA: an honest relay's keys for the sender's group element, its blinding factor
among them, are replaced by uniform ones, and the hops after it are derived from the replacement.
They prove that game hard under Gap Diffie-Hellman with the hashes as random oracles. Here the
keys come from a KDF, so the game is stated for the NIKE and the KDF, and its advantage is the
term the properties of NIKE Sphinx carry.

The paper's relay refuses the challenge element. Here it answers that element with the keys the
adversary is handed, which the adversary could do itself. -/

section Game

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- What a relay returns for a packet, its keys had from the packet's group element by
`keysOf`. -/
def procWith (keysOf : ByteArray → Except String HopKeys) (pkt : ByteArray) : ProcResult :=
  match unwrapNIKEWith nike cipher macS streamS geom keysOf pkt with
  | .ok (p, t, c, f) => some (p, t, c, f.map ofVector)
  | .error _ => none

open Cryptlib.Protocols.Sphinx.Constants (macLength) in
open Cryptlib.Protocols.Sphinx.Common (v0AD) in
/-- A relay that accepts a packet has checked its MAC under the MAC key of the keys it had for
the packet's group element. -/
theorem procWith_mac (keysOf : ByteArray → Except String HopKeys) (pkt : ByteArray) (t : HopKeys)
    (res : Option ByteArray × Vector UInt8 32 × List Commands.RoutingCommand × Option ByteArray)
    (hk : keysOf (pkt.extract 2 (2 + nike.publicKeySize)) = .ok t)
    (h : procWith nike cipher macS streamS geom keysOf pkt = some res) :
    ¬ pkt.size < (2 + nike.publicKeySize + geom.routingInfoLength) + macLength ∧
      (ofVector (macS.mac (ofVector t.headerMAC) (pkt.extract 0 (2 + nike.publicKeySize +
          geom.routingInfoLength)))).data
        = (pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength) ((2 + nike.publicKeySize +
            geom.routingInfoLength) + macLength)).data := by
  unfold procWith unwrapNIKEWith at h
  dsimp only at h
  by_cases h1 : pkt.size < 2 + nike.publicKeySize + geom.routingInfoLength + macLength
  · rw [dite_eq_left h1] at h; cases h
  rw [dite_eq_right h1] at h
  by_cases h2 : (pkt.extract 0 2).data ≠ v0AD.data
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2, hk] at h
  dsimp only [Bind.bind, Except.bind] at h
  refine ⟨h1, ?_⟩
  by_contra h3
  rw [ite_eq_left h3] at h
  cases h

open Cryptlib.Protocols.Sphinx.Constants (macLength) in
/-- **A packet a relay accepts under another header is a forgery.** If the packet's header is
not the message `M` followed by its tag, the packet carries the right tag on a message other
than `M`. -/
theorem procWith_forgery (hmactag : macS.tagSize = macLength)
    (keysOf : ByteArray → Except String HopKeys) (pkt M : ByteArray) (t : HopKeys)
    (hk : keysOf (pkt.extract 2 (2 + nike.publicKeySize)) = .ok t)
    (h : (procWith nike cipher macS streamS geom keysOf pkt).isSome = true)
    (hne : pkt.extract 0 ((2 + nike.publicKeySize + geom.routingInfoLength) + macS.tagSize) ≠ M ++
        ofVector (macS.mac (ofVector t.headerMAC) M)) :
    pkt.extract 0 (2 + nike.publicKeySize + geom.routingInfoLength) ≠ M ∧
      macS.mac (ofVector t.headerMAC) (pkt.extract 0 (2 + nike.publicKeySize +
          geom.routingInfoLength))
        = Util.Bytes.toVecN macS.tagSize (pkt.extract (2 + nike.publicKeySize +
            geom.routingInfoLength) ((2 + nike.publicKeySize + geom.routingInfoLength) +
            macS.tagSize)) := by
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hsz, hd⟩ := procWith_mac nike cipher macS streamS geom keysOf pkt t res hk hres
  have e : (2 + nike.publicKeySize + geom.routingInfoLength) + macS.tagSize = (2 +
      nike.publicKeySize + geom.routingInfoLength) + macLength := by rw [hmactag]
  rw [e] at hne ⊢
  have hm : ofVector (macS.mac (ofVector t.headerMAC) (pkt.extract 0 (2 + nike.publicKeySize +
      geom.routingInfoLength)))
      = pkt.extract (2 + nike.publicKeySize + geom.routingInfoLength) ((2 + nike.publicKeySize +
          geom.routingInfoLength) + macLength) := ByteArray.ext hd
  refine ⟨fun hp => hne ?_, (Util.Bytes.toVecN_ofVector _).symm.trans
    (congrArg (Util.Bytes.toVecN macS.tagSize) hm)⟩
  rw [KEMSphinx.extract_split pkt (2 + nike.publicKeySize + geom.routingInfoLength) ((2 +
      nike.publicKeySize + geom.routingInfoLength) + macLength) (by omega) (by omega), ← hm, hp]

/-- Under a header whose tag is known, a relay uses its MAC key for that tag only. -/
theorem procWith_const (t : HopKeys) (km : Vector UInt8 32) (pkt : ByteArray) :
    procWith nike cipher macS streamS geom (fun _ => .ok t) pkt
      = procWith nike cipher (Primitives.MAC.MAC.const (macS.mac (ofVector t.headerMAC)
          (pkt.extract 0 (2 + nike.publicKeySize + geom.routingInfoLength)))) streamS geom
        (fun _ => .ok { t with headerMAC := km }) pkt := by
  unfold procWith unwrapNIKEWith
  rfl

/-- The keys a relay derives for a group element. -/
def relayKeys (sk : nike.PrivateKey) (ge : ByteArray) : Except String HopKeys :=
  deriveHopKeys kdfS <$> nikeDH nike sk ge

/-- A relay's keys, except that for the element `a` they are `t`. -/
def keysExcept (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys) (ge : ByteArray) :
    Except String HopKeys :=
  if ge = a then pure t else relayKeys nike kdfS sk ge

/-- A relay asks for the keys of one element only: the packet's. -/
theorem procWith_keysOf (keysOf : ByteArray → Except String HopKeys) (pkt : ByteArray) :
    procWith nike cipher macS streamS geom keysOf pkt
      = procWith nike cipher macS streamS geom
        (fun _ => keysOf (pkt.extract 2 (2 + nike.publicKeySize))) pkt := by
  unfold procWith unwrapNIKEWith
  rfl

/-- The relay handed the keys `t` for the element `a` answers a packet with that element by `t`,
and any other as it does with its own key. -/
theorem procWith_keysExcept (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys)
    (pkt : ByteArray) :
    procWith nike cipher macS streamS geom (keysExcept nike kdfS sk a t) pkt
      = if pkt.extract 2 (2 + nike.publicKeySize) = a then
          procWith nike cipher macS streamS geom (fun _ => .ok t) pkt
        else procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt := by
  rw [procWith_keysOf nike cipher macS streamS geom (keysExcept nike kdfS sk a t)]
  by_cases h : pkt.extract 2 (2 + nike.publicKeySize) = a
  · simp only [keysExcept, h, ite_true]
    rfl
  · simp only [keysExcept, h, ite_false]
    exact (procWith_keysOf nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt).symm

/-- **A relay is `procWith` on the keys it derives.** -/
theorem unwrap_eq_procWith (sk : nike.PrivateKey) (pkt : ByteArray) :
    RSOR.unwrap nike cipher macS kdfS streamS geom sk pkt
      = (procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt).map
        fun r => (r.1, r.2.2.1, r.2.2.2) := by
  unfold RSOR.unwrap procWith
  rw [unwrapNIKE_eq_unwrapNIKEWith]
  have e : (fun ge => do
        let sk' ← nikeDecodePrivateKey nike (ofVector (nike.encodePrivateKey sk))
        let ss ← nikeDH nike sk' ge
        pure (deriveHopKeys kdfS ss)) = relayKeys nike kdfS sk := by
    funext ge
    unfold nikeDecodePrivateKey relayKeys
    rw [Common.toVecN_ofVector, nike.decode_encode_priv]
    rfl
  rw [e]
  cases unwrapNIKEWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt <;> rfl

open Cryptlib.Primitives.NIKE.NIKE (telescopeElem telescopeSecret telescope_agree) in
/-- The group elements are the sender's public key under the factors of the keys in front. -/
theorem groupElem_eq (c : nike.PrivateKey) (ks : Array HopKeys) (i : ℕ) :
    groupElem nike c ks i = ofVector (nike.encodePublicKey
      (telescopeElem nike c (fun n => RSOR.factor nike ks[n]!) i).1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hdec : nike.decodePrivateKey (Common.toVecN nike.privateKeySize ks[i]!.blindingFactor)
        = some (RSOR.factor nike ks[i]!) := by
      obtain ⟨x, hx⟩ := nike.decodePrivateKey_total
        (Common.toVecN nike.privateKeySize ks[i]!.blindingFactor)
      unfold RSOR.factor
      rw [hx]
      rfl
    rw [groupElem, ih, nikeBlind_bridge nike _ _ (telescopeElem nike c _ i).2 _ hdec]
    rfl

open Cryptlib.Primitives.NIKE.NIKE (telescopeElem telescopeSecret telescope_agree) in
/-- **The relay derives the sender's keys.** For the element that reaches its place on the path,
a relay derives the keys the sender derived for that place. -/
theorem relayKeys_groupElem (c sk : nike.PrivateKey) (hops : Array PathHop)
    (ks : Array HopKeys) (j : ℕ)
    (hpk : hops[j]!.publicKey = ofVector (nike.encodePublicKey (nike.derivePublicKey sk)))
    (hks : RSOR.hopKeys nike kdfS c hops j = (List.range j).map (ks[·]!)) :
    relayKeys nike kdfS sk (groupElem nike c ks j) = .ok (RSOR.hopKey nike kdfS c hops j) := by
  unfold relayKeys RSOR.hopKey
  rw [groupElem_eq, nikeDH_bridge nike sk _ (telescopeElem nike c _ j).2, hks, List.map_map, hpk]
  have e := RSOR.foldl_dh nike c sk (fun n => RSOR.factor nike ks[n]!) j
  rw [telescope_agree]
  exact congrArg (fun x => Except.ok (deriveHopKeys kdfS x)) e.symm

theorem hopKeys_eq_map (c : nike.PrivateKey) (hops : Array PathHop) (n : ℕ) :
    RSOR.hopKeys nike kdfS c hops n = (List.range n).map (RSOR.hopKey nike kdfS c hops) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RSOR.hopKeys_succ, ih, List.range_succ, List.map_append]; rfl

open Cryptlib.Primitives.NIKE.NIKE (telescopeElem) in
/-- The blinded element depends on the sender's private key through its public key, and on the
factors in front. -/
theorem telescopeElem_congr (c c' : nike.PrivateKey) (f f' : ℕ → nike.PrivateKey) (i : ℕ)
    (hc : nike.derivePublicKey c = nike.derivePublicKey c') (hf : ∀ n < i, f n = f' n) :
    telescopeElem nike c f i = telescopeElem nike c' f' i := by
  induction i with
  | zero => exact Subtype.ext hc
  | succ i ih =>
    apply Subtype.ext
    show nike.reinterpret (nike.groupAction (f i) (telescopeElem nike c f i))
      = nike.reinterpret (nike.groupAction (f' i) (telescopeElem nike c' f' i))
    rw [ih fun n hn => hf n (by omega), hf i (by omega)]

open Cryptlib.Protocols.Sphinx.KEMSphinx (keysKs keysTag keysEnc) in
/-- **A sender's packet is `nikePktFn` on the sender's hop keys** and the elements they blind. -/
theorem layer_zero_pktFn (hops : Array PathHop) (d : RSOR.Draw nike geom)
    (payload pkt : ByteArray)
    (h0 : RSOR.layer nike cipher macS kdfS streamS geom hops d payload 0 = .ok pkt)
    (hkeys : ∀ j < hops.size, ∃ sk,
      hops[j]!.publicKey = ofVector (nike.encodePublicKey (nike.derivePublicKey sk))) :
    nikePktFn geom
        (keysKs geom streamS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) hops
          hops.size).toArray)
        (keysTag macS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) hops hops.size).toArray)
        (keysEnc cipher (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) hops
          hops.size).toArray)
        (groupElem nike (RSOR.clientKey nike geom d)
          (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) hops hops.size).toArray)
        (RSOR.filler nike geom hops d) hops payload = some pkt := by
  choose! tsk htsk using hkeys
  have hnk : newNIKEPacket nike cipher macS kdfS streamS geom (ofVector d.1)
      (RSOR.filler nike geom hops d) hops payload = .ok pkt := by
    obtain ⟨p, hp, hpp⟩ :=
      (RSOR.layer_ok nike cipher macS kdfS streamS geom hops d payload 0 pkt).1 h0
    rw [hp]
    exact congrArg Except.ok hpp
  obtain ⟨clientSk, f, ge, keys, hgs, hks, hself, hchain, hfn⟩ :=
    newNIKEPacket_pktFn nike macS kdfS streamS geom cipher _ _ hops payload pkt hnk tsk
      (fun i hi => htsk i hi)
  have hcpub : nike.derivePublicKey clientSk
      = nike.derivePublicKey (RSOR.clientKey nike geom d) := by
    obtain ⟨c0, hc0⟩ := nike.decodePrivateKey_total d.1
    have hck : RSOR.clientKey nike geom d = c0 := by
      unfold RSOR.clientKey
      rw [hc0]
      rfl
    unfold nikeSelfPublicKeyBytes at hself
    rw [Common.toVecN_ofVector, hc0] at hself
    have := congrArg (fun b => nike.decodePublicKey (Common.toVecN nike.publicKeySize b)) hself
    simp only [Common.toVecN_ofVector, nike.decode_encode_pub, Option.some.injEq] at this
    rw [hck]
    exact this.symm
  obtain ⟨-, hK⟩ := RSOR.hopKey_eq nike kdfS (RSOR.clientKey nike geom d) hops keys tsk f
    hops.size (fun i hi => htsk i hi) (fun j hj => ⟨by
      rw [(hchain j hj).2.1, RSOR.telescopeSecret_congr nike _ _ _ f hcpub j], (hchain j hj).2.2⟩)
  have hget : ∀ i < hops.size,
      (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) hops hops.size).toArray[i]!
        = keys[i]! := fun i hi => by
    rw [hopKeys_eq_map, ← hK i hi]
    simp [hi]
  have hpos : 0 < hops.size := by
    obtain ⟨-, hdr, sprp, -, hcreate, -⟩ :=
      newNIKEPacket_unfold nike cipher macS kdfS streamS geom _ _ hops payload pkt hnk
    have := (createHeader_unfold nike macS kdfS streamS geom _ _ hops hdr sprp hcreate tsk
      (fun i hi => htsk i hi)).1
    omega
  rw [← hfn]
  refine nikePktFn_congr geom _ _ _ _ _ _ _ _ _ _ _ hpos fun i hi => ⟨?_, ?_, ?_, ?_⟩
  · simp only [keysKs, hget i hi]
  · funext m
    simp only [keysTag, hget i hi]
  · funext b
    simp only [keysEnc, hget i hi]
  · rw [groupElem_eq, (hchain i hi).1]
    congr 2
    refine congrArg Subtype.val (telescopeElem_congr nike _ _ _ _ i hcpub.symm fun n hn => ?_)
    show RSOR.factor nike _ = f n
    rw [hget n (by omega)]
    unfold RSOR.factor
    rw [(hchain n (by omega)).2.2]
    rfl

/-- **With the sender's keys, the relay handed the keys of its place is the relay.** -/
theorem keysExcept_hopKeys (c sk : nike.PrivateKey) (hops : Array PathHop) (n j : ℕ)
    (hj : j < n)
    (hpk : hops[j]!.publicKey = ofVector (nike.encodePublicKey (nike.derivePublicKey sk))) :
    keysExcept nike kdfS sk (groupElem nike c (RSOR.hopKeys nike kdfS c hops n).toArray j)
        (RSOR.hopKeys nike kdfS c hops n).toArray[j]!
      = relayKeys nike kdfS sk := by
  have hget : ∀ i < n, (RSOR.hopKeys nike kdfS c hops n).toArray[i]!
      = RSOR.hopKey nike kdfS c hops i := fun i hi => by
    rw [hopKeys_eq_map]
    simp [hi]
  funext ge
  unfold keysExcept
  split
  · next h =>
    subst h
    rw [relayKeys_groupElem nike kdfS c sk hops _ j hpk (by
      rw [hopKeys_eq_map]
      exact List.map_congr_left fun i hi =>
        (hget i (lt_trans (List.mem_range.1 hi) hj)).symm), hget j hj]
    rfl
  · rfl

/-- The relay's oracle, answering the element `a` with the keys `t`. -/
def procImplK (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys) : QueryImpl procSpec ProbComp :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    pure (procWith nike cipher macS streamS geom (keysExcept nike kdfS sk a t) pkt)

/-- The relay's oracle. -/
def procImpl (sk : nike.PrivateKey) : QueryImpl procSpec ProbComp :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    pure (procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt)

/-- **In the game's real world the relay is the honest relay**: handed the sender's keys for its
place, it answers as it does with its own key. -/
theorem procImplK_hopKeys (c sk : nike.PrivateKey) (hops : Array PathHop) (n j : ℕ)
    (hj : j < n)
    (hpk : hops[j]!.publicKey = ofVector (nike.encodePublicKey (nike.derivePublicKey sk))) :
    procImplK nike cipher macS kdfS streamS geom sk
        (groupElem nike c (RSOR.hopKeys nike kdfS c hops n).toArray j)
        (RSOR.hopKeys nike kdfS c hops n).toArray[j]!
      = procImpl nike cipher macS kdfS streamS geom sk := by
  unfold procImplK procImpl
  rw [keysExcept_hopKeys nike kdfS c sk hops n j hj hpk]

/-- Hop keys from uniform draws: four keys, and the seed of the blinding factor. -/
def keysOfDraw (u : KeyTuple × Vector UInt8 32) : HopKeys where
  payloadEncryption := u.1.1
  headerEncryptionIV := u.1.2.1
  headerMAC := u.1.2.2.1
  headerEncryption := u.1.2.2.2
  blindingFactor := blindingFactorPrivKey u.2

/-- An adversary on the key game. With the relay's oracle it chooses a path and the relay's
place on it; then it is given the sender's group element and every hop's keys. -/
structure KeyAdversary where
  St : RSOR.Key nike → Type
  pre : (pk : RSOR.Key nike) → OracleComp procSpec ((Array PathHop × ℕ) × St pk)
  post : {pk : RSOR.Key nike} → St pk → ByteArray → List HopKeys → OracleComp procSpec Bool

variable {nike}

/-- **The key game.** The honest relay is put at the place the adversary chose. With `b` the
hops' keys are the sender's; without, the relay's keys are uniform and the hops after it are
derived from them. The relay answers the element it receives with the keys of its place. A
place off the path loses. -/
def keyGame (A : KeyAdversary nike) (b : Bool) : ProbComp Bool := do
  let u ← $ᵗ (KeyTuple × Vector UInt8 32)
  let k ← RSOR.keygen nike
  let cs ← simulateQ (procImpl nike cipher macS kdfS streamS geom k.2) (A.pre k.1)
  let d ← $ᵗ Vector UInt8 nike.privateKeySize
  let c := (nike.decodePrivateKey d).getD default
  let hops := cs.1.1.modify cs.1.2 fun h =>
    { h with publicKey := ofVector (nike.encodePublicKey k.1.1) }
  let keys := hopKeysWith nike kdfS c hops cs.1.2
    (if b then RSOR.hopKey nike kdfS c hops cs.1.2 else keysOfDraw u) hops.size
  if cs.1.2 < hops.size then
    simulateQ (procImplK nike cipher macS kdfS streamS geom k.2
        (groupElem nike c keys.toArray cs.1.2) keys.toArray[cs.1.2]!)
      (A.post cs.2 (groupElem nike c keys.toArray 0) keys)
  else pure false

/-- The adversary's advantage in the key game. -/
noncomputable def keyAdvantage (A : KeyAdversary nike) : ℝ :=
  |(Pr{let x ← keyGame cipher macS kdfS streamS geom A true}[x = true]).toReal
    - (Pr{let x ← keyGame cipher macS kdfS streamS geom A false}[x = true]).toReal|

end Game

end Cryptlib.Protocols.Sphinx.NIKESphinx
