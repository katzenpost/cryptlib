/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.RSOR
import Cryptlib.Protocols.Sphinx.NIKESphinxTheorems
import Cryptlib.Protocols.Sphinx.KEMSphinxRSOR

/-! # NIKE Sphinx as a repliable service onion routing scheme

`scheme` is NIKE Sphinx as a `Protocols.RSOR.Scheme`: the algorithms, and the four correctness laws
proved of `newNIKEPacket`, `unwrapNIKE`, `newNIKESURB`, `newPacketFromSURB` and
`decryptSURBPayload`. It follows `KEMSphinxRSOR` and shares its names, messages, onions and
payload layout.

A KEM Sphinx layer is a packet on the rest of the path. A NIKE Sphinx layer is not: each relay
blinds the group element it passes on. So the layer for position `i` is the sender's packet with
`i` relays' work done on it by `peel`, under the hop keys the sender derived. -/

namespace Cryptlib.Protocols.Sphinx.NIKESphinx.RSOR

open OracleComp OracleSpec
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.KEMSphinx (extract_append_tail encrypt_decrypt)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join msgOf pad surbKeys delivers
  size_tagged join_split decryptSURBPayload_surbKeys newPacketFromSURB_eq)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE telescopeElem telescopeSecret telescope_agree)
open Cryptlib.Primitives.Hash.Sha512 (sha512_256)
open Cryptlib.Util.Bytes (ofVector)

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- What a sender draws for one path: its private key for the path, and the filler. A path
shorter than `geom.nrHops` uses a prefix of the filler. -/
abbrev Draw := Vector UInt8 nike.privateKeySize × Vector UInt8 geom.routingInfoLength

/-- The draws for the forward path and for the backward path, the SURB's payload key, and its
ID. -/
abbrev Randomness := Draw nike geom × Draw nike geom × Vector UInt8 64 × Vector UInt8 16

/-- A relay's public key: one that some private key gives. -/
abbrev Key := {k : nike.PublicKey // ∃ sk, k = nike.derivePublicKey sk}

abbrev Request := Protocols.RSOR.Request geom.nrHops Name (Key nike) (Msg geom) Name

variable {geom} in
/-- A route as `newNIKEPacket` takes it. Only its last hop has commands. -/
def path (R : Protocols.RSOR.Route geom.nrHops Name (Key nike)) (last : List RoutingCommand) :
    Array PathHop :=
  (R.hops.mapIdx fun i h =>
    ⟨h.name, ofVector (nike.encodePublicKey h.key.1),
      if i + 1 = R.hops.length then last else []⟩).toArray

/-- The key pair of a relay. -/
def keygen : ProbComp (Key nike × nike.PrivateKey) := do
  let s ← $ᵗ Vector UInt8 32
  return (⟨nike.derivePublicKey (nike.privateKeyFromSeed s), _, rfl⟩, nike.privateKeyFromSeed s)

theorem key_of_keygen (k : Key nike) (sk : nike.PrivateKey)
    (h : (k, sk) ∈ support (keygen nike)) : k.1 = nike.derivePublicKey sk := by
  simp only [keygen, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    Prod.mk.injEq] at h
  obtain ⟨s, -, h1, h2⟩ := h
  rw [h1, h2]

/-! ## The sender's hop keys -/

/-- The group action on encoded keys. Empty when `pk` is not the encoding of a safe key. -/
def dh (sk : nike.PrivateKey) (pk : ByteArray) : ByteArray :=
  (nikeDH nike sk pk).toOption.getD .empty

/-- The factor a relay blinds the group element by. -/
def factor (k : HopKeys) : nike.PrivateKey :=
  (nike.decodePrivateKey (toVecN nike.privateKeySize k.blindingFactor)).getD default

/-- The keys of the first `n` hops, as the sender with private key `c` derives them: the secret it
shares with a hop, acted on by the factors of the hops before. -/
def hopKeys (c : nike.PrivateKey) (hops : Array PathHop) : ℕ → List HopKeys
  | 0 => []
  | n + 1 =>
    let ks := hopKeys c hops n
    ks ++ [deriveHopKeys kdfS
      ((ks.map (factor nike)).foldl (fun ss f => dh nike f ss) (dh nike c hops[n]!.publicKey))]

/-- The keys of hop `n`. -/
def hopKey (c : nike.PrivateKey) (hops : Array PathHop) (n : ℕ) : HopKeys :=
  deriveHopKeys kdfS (((hopKeys nike kdfS c hops n).map (factor nike)).foldl
    (fun ss f => dh nike f ss) (dh nike c hops[n]!.publicKey))

theorem hopKeys_succ (c : nike.PrivateKey) (hops : Array PathHop) (n : ℕ) :
    hopKeys nike kdfS c hops (n + 1) = hopKeys nike kdfS c hops n ++ [hopKey nike kdfS c hops n] :=
  rfl

/-! ## The layers -/

/-- The next relay and the MAC of its header, if the command names them. -/
def nextHop : RoutingCommand → Option (Vector UInt8 32 × Vector UInt8 32)
  | .nextNodeHop id m => some (id, m)
  | _ => none

/-- What the relay with hop keys `k` sends on when it forwards `pkt`: the blinded group element,
the routing information and MAC of the next hop, and the payload with one layer removed. -/
def peel (k : HopKeys) (pkt : ByteArray) : ByteArray :=
  let riOff := 2 + nike.publicKeySize
  let macOff := riOff + geom.routingInfoLength
  let payloadOff := macOff + macLength
  let b0 := pkt.extract riOff macOff ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩
  let b := xorBytes b0
    (streamS.keystream (ofVector k.headerEncryption) (ofVector k.headerEncryptionIV) b0.size)
  let mac : Vector UInt8 32 := match parseAll (b.extract 0 geom.perHopRoutingInfoLength) with
    | .ok cmds => ((cmds.findSome? nextHop).map (·.2)).getD default
    | .error _ => default
  let raw := pkt.extract payloadOff pkt.size
  let dec :=
    if raw.size > 0 then
      cipher.decrypt k.payloadEncryption.toArray (ofVector k.headerEncryptionIV) raw
    else raw
  v0AD ++ nikeBlind nike (pkt.extract 2 riOff) k.blindingFactor
    ++ b.extract geom.perHopRoutingInfoLength b.size ++ ofVector mac
    ++ (if dec.size > 0 then dec else raw)

/-- The sender's private key for a path. -/
def clientKey (d : Draw nike geom) : nike.PrivateKey := (nike.decodePrivateKey d.1).getD default

/-- The filler for a path: as much of the draw as the unused hops take. -/
def filler (hops : Array PathHop) (d : Draw nike geom) : ByteArray :=
  (ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)

/-- The layer of a packet that the hop at position `i` receives: the packet, forwarded by the
`i` hops before. -/
def layer (hops : Array PathHop) (d : Draw nike geom) (payload : ByteArray) (i : ℕ) :
    Except String ByteArray :=
  (newNIKEPacket nike cipher macS kdfS streamS geom (ofVector d.1) (filler nike geom hops d) hops
    payload).map fun pkt =>
      (hopKeys nike kdfS (clientKey nike geom d) hops i).foldl
        (fun p k => peel nike cipher streamS geom k p) pkt

/-- The SURB for the backward path and the keys that open its reply. An empty backward path has
none. -/
def surb (q : Request nike geom) (r : Randomness nike geom) : ByteArray × ByteArray :=
  let hops := path nike q.back [.surbReply r.2.2.2]
  match newNIKESURB nike macS kdfS streamS geom (ofVector r.2.1.1) r.2.2.1
      (filler nike geom hops r.2.1) hops with
  | .ok x => x
  | .error _ => (⟨Array.replicate geom.surbLength 0⟩, .empty)

/-- The forward payload: a flag for the SURB, a reserved byte, the SURB, and the message. -/
def body (q : Request nike geom) (r : Randomness nike geom) : ByteArray :=
  ⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ ++ (surb nike macS kdfS streamS geom q r).1
    ++ ofVector q.msg

def form (q : Request nike geom) (r : Randomness nike geom) (i : Fin q.fwd.hops.length) :
    Onion geom :=
  match layer nike cipher macS kdfS streamS geom (path nike q.fwd [.recipient q.receiver]) r.1
      (body nike macS kdfS streamS geom q r) i with
  | .ok pkt => split geom pkt
  | .error _ => default

/-- What a relay with private key `sk` gets from a packet: the payload if the packet ends here,
the commands, and the packet to send on if it does not. -/
def unwrap (sk : nike.PrivateKey) (pkt : ByteArray) :
    Option (Option ByteArray × List RoutingCommand × Option ByteArray) :=
  match unwrapNIKE nike cipher macS kdfS streamS geom (ofVector (nike.encodePrivateKey sk)) pkt with
  | .ok (p, _, cmds, fwd) => some (p, cmds, fwd.map ofVector)
  | .error _ => none

/-- A relay unwraps the packet and reads its commands. A relay does not use its own name. -/
def proc (sk : nike.PrivateKey) (o : Onion geom) :
    Option (Protocols.RSOR.Step Name (Onion geom) (Msg geom) Name
      (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) :=
  match unwrap nike cipher macS kdfS streamS geom sk (join o) with
  | some (none, cmds, some fwd) => cmds.findSome? fun
    | .nextNodeHop next _ => some (.forward next (split geom fwd))
    | _ => none
  | some (some p, cmds, none) => cmds.findSome? fun
    | .recipient receiver => some (.deliver (msgOf geom p) receiver)
    | .surbReply _ => some (.reply (toVecN _ p))
    | _ => none
  | _ => none

/-- The draws from which the first layer on a path can be built. Every later layer can then be
built too. A NIKE cannot fail, so nothing else is asked. -/
def Builds (R : Protocols.RSOR.Route geom.nrHops Name (Key nike)) (last : List RoutingCommand)
    (d : Draw nike geom) (payload : ByteArray) : Prop :=
  0 < R.hops.length →
    ∃ pkt, layer nike cipher macS kdfS streamS geom (path nike R last) d payload 0 = .ok pkt

/-- The reply packet the exit relay builds from the SURB, and the relay it sends it to. -/
def replyPacket (q : Request nike geom) (r : Randomness nike geom) (m : Msg geom) :
    ByteArray × Name :=
  match SURB.newPacketFromSURB cipher geom (surb nike macS kdfS streamS geom q r).1
      (pad geom m) with
  | .ok x => x
  | .error _ => (.empty, default)

/-- A payload after the relay with hop keys `k` has decrypted it. -/
def dec (k : HopKeys) (p : ByteArray) : ByteArray :=
  cipher.decrypt k.payloadEncryption.toArray (ofVector k.headerEncryptionIV) p

/-- A payload after the relays with hop keys `ks` have each decrypted it. -/
def peeled (ks : List HopKeys) (p : ByteArray) : ByteArray := ks.foldl (fun p k => dec cipher k p) p

/-- The layer of a reply that the relay at backward position `j` receives: the header of the
SURB's packet at that position, and the payload as the relays before left it. -/
def formBack (q : Request nike geom) (r : Randomness nike geom) (m : Msg geom)
    (j : Fin q.back.hops.length) : Onion geom :=
  let hops := path nike q.back [.surbReply r.2.2.2]
  match layer nike cipher macS kdfS streamS geom hops r.2.1
      ⟨Array.replicate geom.forwardPayloadLength 0⟩ j with
  | .ok pkt =>
    let first := (replyPacket nike cipher macS kdfS streamS geom q r m).1
    split geom (pkt.extract 0 geom.headerLength ++ peeled cipher
      (hopKeys nike kdfS (clientKey nike geom r.2.1) hops j)
      (first.extract geom.headerLength first.size))
  | .error _ => default

/-- The exit relay answers with the SURB it finds in the payload. A relay replies only to a
packet it delivers: a reply packet's payload is not read for a SURB. -/
def reply (sk : nike.PrivateKey) (m : Msg geom) (o : Onion geom) : Option (Name × Onion geom) :=
  match unwrap nike cipher macS kdfS streamS geom sk (join o) with
  | some (some p, cmds, none) =>
    if delivers cmds = true ∧ p.get! 0 = 1 then
      match SURB.newPacketFromSURB cipher geom (p.extract 2 (2 + geom.surbLength)) (pad geom m) with
      | .ok (pkt, next) => some (next, split geom pkt)
      | .error _ => none
    else none
  | _ => none

/-- The sender opens a reply with the keys it kept from the SURB. -/
def recover (q : Request nike geom) (r : Randomness nike geom)
    (p : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) : Option (Msg geom) :=
  match SURB.decryptSURBPayload cipher geom (surb nike macS kdfS streamS geom q r).2
      (ofVector p) with
  | .ok b => some (toVecN _ (b.extract 0 geom.userForwardPayloadLength))
  | .error _ => none

/-- The draws for which both paths can be built. -/
def Reliable (q : Request nike geom) (r : Randomness nike geom) : Prop :=
  Builds nike cipher macS kdfS streamS geom q.fwd [.recipient q.receiver] r.1
    (body nike macS kdfS streamS geom q r) ∧
  Builds nike cipher macS kdfS streamS geom q.back [.surbReply r.2.2.2] r.2.1
    ⟨Array.replicate geom.forwardPayloadLength 0⟩


/-! ## The sender derives the relays' keys -/

theorem dh_encode (sk : nike.PrivateKey) (pk : nike.PublicKey) (h : nike.Safe pk) :
    dh nike sk (ofVector (nike.encodePublicKey pk))
      = ofVector (nike.encodeSharedSecret (nike.groupAction sk ⟨pk, h⟩)) := by
  unfold dh
  rw [nikeDH_bridge nike sk pk h]
  rfl

/-- The secret the sender `c` shares with the relay `t`, acted on by `n` factors. -/
theorem foldl_dh (c t : nike.PrivateKey) (f : ℕ → nike.PrivateKey) (n : ℕ) :
    ((List.range n).map f).foldl (fun ss f => dh nike f ss)
        (dh nike c (ofVector (nike.encodePublicKey (nike.derivePublicKey t))))
      = ofVector (nike.encodeSharedSecret (telescopeSecret nike c t f n).1) := by
  induction n with
  | zero => exact dh_encode nike c _ (nike.derive_safe t)
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [← nike.encodePublicKey_reinterpret, dh_encode nike (f n) _ (telescopeSecret nike c t f n).2]
    rfl

/-- The secret depends on the sender's private key through its public key only. -/
theorem telescopeSecret_congr (c c' t : nike.PrivateKey) (f : ℕ → nike.PrivateKey)
    (h : nike.derivePublicKey c = nike.derivePublicKey c') (n : ℕ) :
    telescopeSecret nike c t f n = telescopeSecret nike c' t f n := by
  induction n with
  | zero =>
    apply Subtype.ext
    show nike.groupAction c _ = nike.groupAction c' _
    rw [nike.commutes c t, nike.commutes c' t]
    congr 1
    exact Subtype.ext h
  | succ n ih =>
    apply Subtype.ext
    show nike.groupAction (f n) ⟨nike.reinterpret (telescopeSecret nike c t f n).1, _⟩
      = nike.groupAction (f n) ⟨nike.reinterpret (telescopeSecret nike c' t f n).1, _⟩
    congr 1
    exact Subtype.ext (congrArg (fun x => nike.reinterpret x.1) ih)

/-- The sender derives the keys `createHeader` does. -/
theorem hopKey_eq (c : nike.PrivateKey) (hops : Array PathHop) (keys : Array HopKeys)
    (t f : ℕ → nike.PrivateKey) (n : ℕ)
    (hpk : ∀ i < n,
      hops[i]!.publicKey = ofVector (nike.encodePublicKey (nike.derivePublicKey (t i))))
    (hk : ∀ i < n,
      keys[i]! = deriveHopKeys kdfS
        (ofVector (nike.encodeSharedSecret (telescopeSecret nike c (t i) f i).1)) ∧
      nike.decodePrivateKey (toVecN nike.privateKeySize keys[i]!.blindingFactor) = some (f i)) :
    hopKeys nike kdfS c hops n = (List.range n).map (keys[·]!) ∧
      ∀ i < n, hopKey nike kdfS c hops i = keys[i]! := by
  induction n with
  | zero => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hpk i (by omega)) (fun i hi => hk i (by omega))
    have hn : hopKey nike kdfS c hops n = keys[n]! := by
      have hf : (hopKeys nike kdfS c hops n).map (factor nike) = (List.range n).map f := by
        rw [ih1, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp, factor, (hk i (by have := List.mem_range.1 hi; omega)).2,
          Option.getD_some]
      unfold hopKey
      rw [hf, hpk n (by omega), foldl_dh, (hk n (by omega)).1]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hopKeys_succ, ih1, hn, List.range_succ, List.map_append]
      rfl
    · by_cases hin : i < n
      · exact ih2 i hin
      · obtain rfl : i = n := by omega
        exact hn

/-! ## The payload at each hop -/

/-- The payloads `newNIKEPacket` would have gone through for the hop at position `i` to receive
`P`: `P` with the layers of the hops from `i` on removed, and then each put back. -/
def trace (sprp : Array SPRPKey) (P : ByteArray) (i : ℕ) : ℕ → ByteArray
  | 0 => (List.range' i (sprp.size - i)).foldl
      (fun p a => cipher.decrypt sprp[a]!.key.toArray (ofVector sprp[a]!.iv) p) P
  | j + 1 => payloadEncryptStep cipher sprp (trace sprp P i j) j

theorem trace_size (sprp : Array SPRPKey) (P : ByteArray) (i : ℕ) :
    (trace cipher sprp P i 0).size = P.size :=
  List.foldl_size_preserving _ _ (fun _ _ => cipher.decrypt_size _ _ _) P

theorem trace_succ (sprp : Array SPRPKey) (P : ByteArray) (i : ℕ) (hi : i < sprp.size) :
    trace cipher sprp P i
      = trace cipher sprp (cipher.decrypt sprp[i]!.key.toArray (ofVector sprp[i]!.iv) P)
        (i + 1) := by
  funext j
  induction j with
  | zero =>
    show List.foldl _ P (List.range' i (sprp.size - i)) = List.foldl _ _ _
    rw [show sprp.size - i = sprp.size - (i + 1) + 1 by omega, List.range'_succ, List.foldl_cons]
  | succ j ih => rw [trace, trace, ih]

/-- The hop at position `i` receives `P`. -/
theorem trace_at (sprp : Array SPRPKey) (m : ℕ) : ∀ (i : ℕ) (P : ByteArray),
    sprp.size - i = m → i ≤ sprp.size → 16 ≤ P.size → trace cipher sprp P i m = P := by
  induction m with
  | zero =>
    intro i P hm _ _
    show List.foldl _ P (List.range' i (sprp.size - i)) = P
    rw [hm]
    rfl
  | succ m ih =>
    intro i P hm hi h16
    rw [trace_succ cipher sprp P i (by omega), trace,
      ih (i + 1) _ (by omega) (by omega) (by rw [cipher.decrypt_size]; exact h16)]
    unfold payloadEncryptStep
    rw [show sprp.size - 1 - m = i by omega]
    exact encrypt_decrypt cipher _ _ _ h16

/-- The hop after position `i` receives `P` with the layer of the hop at `i` removed. -/
theorem trace_next (sprp : Array SPRPKey) (P : ByteArray) (i : ℕ) (hi : i < sprp.size)
    (h16 : 16 ≤ P.size) :
    trace cipher sprp P i (sprp.size - (i + 1))
      = cipher.decrypt sprp[i]!.key.toArray (ofVector sprp[i]!.iv) P := by
  rw [trace_succ cipher sprp P i hi]
  exact trace_at cipher sprp _ (i + 1) _ rfl (by omega) (by rw [cipher.decrypt_size]; exact h16)

/-! ## What a relay forwards -/

theorem unwrap_of_ok (sk : nike.PrivateKey) (pkt : ByteArray) (p : Option ByteArray)
    (tag : Vector UInt8 32) (cmds : List RoutingCommand) (fwd : Option (Vector UInt8 pkt.size))
    (h : unwrapNIKE nike cipher macS kdfS streamS geom (ofVector (nike.encodePrivateKey sk)) pkt
      = .ok (p, tag, cmds, fwd)) :
    unwrap nike cipher macS kdfS streamS geom sk pkt = some (p, cmds, fwd.map ofVector) := by
  unfold unwrap
  rw [h]

/-- A check that throws: if what follows succeeds, the check passed. -/
theorem of_ite_throw {c : Prop} [Decidable c] {β : Type} {e : String} {K : Unit → Except String β}
    {x : β} (h : (if c then (throw e >>= K) else K ()) = Except.ok x) : ¬c ∧ K () = .ok x := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    cases h
  · rw [ite_eq_right hc] at h
    exact ⟨hc, h⟩

theorem of_ite {c : Prop} [Decidable c] {α : Type} {a b x : α} (h : (if c then a else b) = x) :
    a = x ∨ b = x := by
  by_cases hc : c
  · exact .inl (by rwa [ite_eq_left hc] at h)
  · exact .inr (by rwa [ite_eq_right hc] at h)

set_option maxHeartbeats 1000000 in
/-- The packet a relay forwards is `peel` of the packet it got, under the keys it derived. -/
theorem unwrapNIKE_forward (priv pkt : ByteArray) (sk : nike.PrivateKey)
    (hsk : nike.decodePrivateKey (toVecN nike.privateKeySize priv) = some sk)
    (tag : Vector UInt8 32) (cmds : List RoutingCommand) (fwd : Vector UInt8 pkt.size)
    (h : unwrapNIKE nike cipher macS kdfS streamS geom priv pkt = .ok (none, tag, cmds, some fwd)) :
    ∃ ss, nikeDH nike sk (pkt.extract 2 (2 + nike.publicKeySize)) = .ok ss ∧
      ofVector fwd = peel nike cipher streamS geom (deriveHopKeys kdfS ss) pkt := by
  unfold unwrapNIKE at h
  dsimp only at h
  by_cases h1 : pkt.size < 2 + nike.publicKeySize + geom.routingInfoLength + macLength
  · rw [dite_eq_left h1] at h
    cases h
  rw [dite_eq_right h1] at h
  replace h := (of_ite_throw h).2
  obtain ⟨privSk, hpriv, h⟩ := Except.eq_ok_of_bind_eq_ok h
  obtain ⟨ss, hss, h⟩ := Except.eq_ok_of_bind_eq_ok h
  obtain rfl : privSk = sk := by
    unfold nikeDecodePrivateKey at hpriv
    rw [hsk] at hpriv
    cases hpriv
    rfl
  refine ⟨ss, hss, ?_⟩
  replace h := (of_ite_throw h).2
  obtain ⟨cmds', hparse, h⟩ := Except.eq_ok_of_bind_eq_ok h
  generalize hfs : List.findSome? _ cmds' = o at h
  cases o with
  | none =>
    dsimp only at h
    replace h := (of_ite_throw h).2
    rcases of_ite h with h | h
    · exact absurd (congrArg (fun x => x.1) (Except.ok.inj h)) (Option.some_ne_none _)
    · exact absurd (congrArg (fun x => x.1) (Except.ok.inj (of_ite_throw h).2))
        (Option.some_ne_none _)
  | some p =>
    obtain ⟨id, mac⟩ := p
    have hfs' : cmds'.findSome? nextHop = some (id, mac) := hfs
    dsimp only at h
    obtain rfl := Option.some.inj (congrArg (fun x => x.2.2.2) (Except.ok.inj h))
    unfold peel
    dsimp only
    rw [hparse]
    dsimp only
    rw [hfs']
    rfl

/-! ## What a relay does with a layer -/

theorem layer_ok (hops : Array PathHop) (d : Draw nike geom) (payload : ByteArray) (i : ℕ)
    (pkt : ByteArray) :
    layer nike cipher macS kdfS streamS geom hops d payload i = .ok pkt ↔
      ∃ p, newNIKEPacket nike cipher macS kdfS streamS geom (ofVector d.1)
          (filler nike geom hops d) hops payload = .ok p ∧
        (hopKeys nike kdfS (clientKey nike geom d) hops i).foldl
          (fun p k => peel nike cipher streamS geom k p) p = pkt := by
  unfold layer
  cases newNIKEPacket nike cipher macS kdfS streamS geom (ofVector d.1)
    (filler nike geom hops d) hops payload <;> simp [Except.map]

theorem layer_succ (hops : Array PathHop) (d : Draw nike geom) (payload : ByteArray) (i : ℕ)
    (pkt : ByteArray) (h : layer nike cipher macS kdfS streamS geom hops d payload i = .ok pkt) :
    layer nike cipher macS kdfS streamS geom hops d payload (i + 1)
      = .ok (peel nike cipher streamS geom (hopKey nike kdfS (clientKey nike geom d) hops i)
        pkt) := by
  obtain ⟨p, hp, rfl⟩ := (layer_ok nike cipher macS kdfS streamS geom hops d payload i pkt).1 h
  exact (layer_ok nike cipher macS kdfS streamS geom hops d payload (i + 1) _).2
    ⟨p, hp, by rw [hopKeys_succ, List.foldl_append]; rfl⟩

set_option maxHeartbeats 2000000 in
/-- **What a relay does with a layer.** Before the end of the path it gets the next relay's name
and the next layer. At the end it gets the last hop's commands and the payload. With the payload
replaced by `P`, it passes on or hands over `P` decrypted under its hop key. -/
theorem unwrap_layer (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : Draw nike geom) (payload pkt0 : ByteArray)
    (h0 : layer nike cipher macS kdfS streamS geom hops d payload 0 = .ok pkt0)
    (hkeys : ∀ j < hops.size, ∃ sk,
      hops[j]!.publicKey = ofVector (nike.encodePublicKey (nike.derivePublicKey sk)))
    (hnn : ∀ j < hops.size, ∀ c ∈ hops[j]!.commands, c ≠ RoutingCommand.null)
    (hnh : ∀ j < hops.size, ∀ c ∈ hops[j]!.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (i : ℕ) (hi : i < hops.size) (sk : nike.PrivateKey)
    (hsk : hops[i]!.publicKey = ofVector (nike.encodePublicKey (nike.derivePublicKey sk))) :
    ∃ (pkt hdr : ByteArray) (sprp : Array SPRPKey),
      layer nike cipher macS kdfS streamS geom hops d payload i = .ok pkt ∧
      pkt.size = geom.packetLength ∧
      createHeader nike macS kdfS streamS geom (ofVector d.1) (filler nike geom hops d) hops
        = .ok (hdr, sprp) ∧
      sprp.size = hops.size ∧
      (∀ j < hops.size, sprp[j]!
        = ⟨(hopKey nike kdfS (clientKey nike geom d) hops j).payloadEncryption,
          (hopKey nike kdfS (clientKey nike geom d) hops j).headerEncryptionIV⟩) ∧
      pkt0.extract 0 geom.headerLength = hdr ∧
      (i + 1 < hops.size → ∃ pkt' mac,
        layer nike cipher macS kdfS streamS geom hops d payload (i + 1) = .ok pkt' ∧
        unwrap nike cipher macS kdfS streamS geom sk pkt
          = some (none, hops[i]!.commands ++ [.nextNodeHop hops[i + 1]!.id mac], some pkt') ∧
        ∀ P : ByteArray, P.size = geom.payloadTagLength + geom.forwardPayloadLength →
          unwrap nike cipher macS kdfS streamS geom sk (pkt.extract 0 geom.headerLength ++ P)
            = some (none, hops[i]!.commands ++ [.nextNodeHop hops[i + 1]!.id mac],
              some (pkt'.extract 0 geom.headerLength
                ++ dec cipher (hopKey nike kdfS (clientKey nike geom d) hops i) P))) ∧
      (i + 1 = hops.size →
        ((∀ c ∈ hops[i]!.commands, ∀ id, c ≠ RoutingCommand.surbReply id) →
          unwrap nike cipher macS kdfS streamS geom sk pkt
            = some (some payload, hops[i]!.commands, none)) ∧
        (hops[i]!.commands.any (fun c => match c with
            | RoutingCommand.surbReply _ => true | _ => false) = true →
          ∀ P : ByteArray, P.size = geom.payloadTagLength + geom.forwardPayloadLength →
            unwrap nike cipher macS kdfS streamS geom sk (pkt.extract 0 geom.headerLength ++ P)
              = some (some (dec cipher (hopKey nike kdfS (clientKey nike geom d) hops i) P),
                hops[i]!.commands, none))) := by
  obtain ⟨-, -, -, hheader, hpacket, -⟩ := id hvalid
  -- The relays' private keys: `sk` at position `i`.
  choose! tsk htsk using hkeys
  have htarget : ∀ j (_ : j < hops.size), hops[j]!.publicKey = ofVector (nike.encodePublicKey
      (nike.derivePublicKey (Function.update tsk i sk j))) := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self]
      exact hsk
    · rw [Function.update_of_ne hji]
      exact htsk j hj
  obtain ⟨targetSk, htarget, hti⟩ : ∃ targetSk : ℕ → nike.PrivateKey,
      (∀ j (_ : j < hops.size), hops[j]!.publicKey = ofVector (nike.encodePublicKey
        (nike.derivePublicKey (targetSk j)))) ∧ targetSk i = sk :=
    ⟨Function.update tsk i sk, htarget, Function.update_self ..⟩
  have hnk : newNIKEPacket nike cipher macS kdfS streamS geom (ofVector d.1)
      (filler nike geom hops d) hops payload = .ok pkt0 := by
    obtain ⟨p, hp, hpp⟩ := (layer_ok nike cipher macS kdfS streamS geom hops d payload 0 pkt0).1 h0
    rw [hp]
    exact congrArg Except.ok hpp
  obtain ⟨hpaysize, hdr, sprpKeys, t, hcreate, ht0content, htstep, hpkteq⟩ :=
    newNIKEPacket_unfold nike cipher macS kdfS streamS geom _ _ hops payload pkt0 hnk
  obtain ⟨hpne, hgen, hfsize, clientSk, f, groupElements, keys, riKeyStream, riPadding, s,
    hgsize, hksize, hriKSsize, hriPadArrSize, hself, hgcontent, hriContent, hs0eq, hstep, hhdreq,
    hsprpeq⟩ := createHeader_unfold nike macS kdfS streamS geom _ _ hops hdr sprpKeys hcreate
      targetSk htarget
  have hsprp : sprpKeys.size = hops.size := by rw [hsprpeq]; simp
  have hgesize : ∀ j (hj : j < groupElements.size),
      (groupElements[j]'hj).size = nike.publicKeySize := by
    intro j hj
    rw [← getElem!_pos groupElements j hj, (hgcontent j (by omega)).1]
    exact Util.Bytes.size_ofVector _
  have hle : ∀ j (_ : j < hops.size), (j + 1) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength + geom.perHopRoutingInfoLength := by
    intro j hj
    obtain ⟨-, -, hrouting, -, -, -⟩ := id hvalid
    rw [hrouting]
    have h1 : (j + 1) * geom.perHopRoutingInfoLength
        ≤ geom.perHopRoutingInfoLength * geom.nrHops := by
      rw [Nat.mul_comm geom.perHopRoutingInfoLength geom.nrHops]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hpadsize := createHeader_loop2_padsize_of_content streamS geom keys hops.size riKeyStream
    riPadding hriContent hle
  have hs0size : (s 0).1.size = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength := by
    rw [hs0eq]
    split
    · next hc => rw [hfsize hc]
    · next hc =>
      rw [show geom.nrHops - hops.size = 0 by omega, Nat.zero_mul]
      rfl
  have hsprpkey : ∀ j (hj : j < sprpKeys.size), (sprpKeys[j]'hj).key = keys[j]!.payloadEncryption ∧
      (sprpKeys[j]'hj).iv = keys[j]!.headerEncryptionIV := by
    intro j hj
    simp only [hsprpeq, Array.getElem_ofFn]
    trivial
  have ht0size : (t 0).size = geom.payloadTagLength + geom.forwardPayloadLength := by
    rw [ht0content, size_tagged, hpaysize]
  have htsize := newNIKEPacket_payload_size_trace cipher sprpKeys t htstep
  -- The sender's key for a path gives the public key `createHeader` used, so the same hop keys.
  have hcpub : nike.derivePublicKey clientSk = nike.derivePublicKey (clientKey nike geom d) := by
    obtain ⟨c0, hc0⟩ := nike.decodePrivateKey_total d.1
    have hck : clientKey nike geom d = c0 := by
      unfold clientKey
      rw [hc0]
      rfl
    unfold nikeSelfPublicKeyBytes at hself
    rw [toVecN_ofVector, hc0] at hself
    have := congrArg (fun b => nike.decodePublicKey (toVecN nike.publicKeySize b)) hself
    simp only [toVecN_ofVector, nike.decode_encode_pub, Option.some.injEq] at this
    rw [hck]
    exact this.symm
  obtain ⟨-, hK⟩ := hopKey_eq nike kdfS (clientKey nike geom d) hops keys targetSk f hops.size
    htarget (fun j hj => ⟨by
      rw [(hgcontent j hj).2.1, telescopeSecret_congr nike _ _ _ f hcpub j], (hgcontent j hj).2.2⟩)
  have hsprpK : ∀ j < hops.size, sprpKeys[j]!
      = ⟨(hopKey nike kdfS (clientKey nike geom d) hops j).payloadEncryption,
        (hopKey nike kdfS (clientKey nike geom d) hops j).headerEncryptionIV⟩ := by
    intro j hj
    rw [hK j hj, getElem!_pos sprpKeys j (by omega)]
    simp only [hsprpeq, Array.getElem_ofFn]
  -- One hop of unwrapping, for any payload trace.
  have NT := fun (t' : ℕ → ByteArray)
      (ht0' : (t' 0).size = geom.payloadTagLength + geom.forwardPayloadLength)
      (hts' : ∀ j (_ : j < sprpKeys.size), t' (j + 1) = payloadEncryptStep cipher sprpKeys (t' j) j)
      (k : ℕ) (hk : k + 1 < hops.size) (priv : ByteArray)
      (hpp : nike.decodePrivateKey (toVecN nike.privateKeySize priv) = some (targetSk k)) =>
    unwrapNIKE_hopPacket_nonterminal nike cipher macS kdfS streamS geom hops keys groupElements
      riKeyStream riPadding sprpKeys hops.size s t' clientSk f targetSk hvalid hmactag hs0size hstep
      hgsize hgesize hgcontent hpadsize (fun i hi => (hriContent i hi).1)
      (fun i hi => (hriContent i hi).2)
      (newNIKEPacket_payload_size_trace cipher sprpKeys t' hts') ht0' hts' hsprpkey hsprp hgen h16
      k hk (hnn k (by omega)) (hnh k (by omega)) priv hpp
  have LT := fun (t' : ℕ → ByteArray)
      (ht0' : (t' 0).size = geom.payloadTagLength + geom.forwardPayloadLength)
      (hts' : ∀ j (_ : j < sprpKeys.size), t' (j + 1) = payloadEncryptStep cipher sprpKeys (t' j) j)
      (k : ℕ) (hk : k + 1 = hops.size) (priv : ByteArray)
      (hpp : nike.decodePrivateKey (toVecN nike.privateKeySize priv) = some (targetSk k)) =>
    unwrapNIKE_hopPacket_last nike cipher macS kdfS streamS geom hops keys groupElements
      riKeyStream riPadding sprpKeys hops.size s t' clientSk f targetSk hvalid hmactag hs0size hstep
      hgsize hgesize hgcontent hpadsize (fun i hi => (hriContent i hi).1)
      (newNIKEPacket_payload_size_trace cipher sprpKeys t' hts') ht0' hts' hsprpkey hsprp hgen h16
      k hk (hnn k (by omega)) (hnh k (by omega)) priv hpp
  -- A hop packet is a header and the payload of its trace.
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ByteArray, ∀ (t' : ℕ → ByteArray) k,
      hopPacket groupElements riPadding s t' hops.size k = H k ++ t' (hops.size - k) :=
    ⟨fun k => v0AD ++ groupElements[k]!
      ++ ((s (hops.size - k)).1 ++ (if k > 0 then riPadding[k - 1]! else ByteArray.empty))
      ++ (s (hops.size - k)).2, fun _ _ => rfl⟩
  have hpsize := fun k (hk : k < hops.size) => hopPacket_size nike macS geom hops keys groupElements
    riKeyStream riPadding sprpKeys hops.size s t hvalid hmactag hs0size hstep hgsize hgesize
    hpadsize
    htsize ht0size hsprp hgen k hk
  have hHsize : ∀ k, k < hops.size → (H k).size = geom.headerLength := by
    intro k hk
    have := hpsize k hk
    rw [hH, ByteArray.size_append, htsize _ (by omega), ht0size, hpacket] at this
    omega
  have hext : ∀ k, k < hops.size →
      (hopPacket groupElements riPadding s t hops.size k).extract 0 geom.headerLength = H k := by
    intro k hk
    rw [hH, ← hHsize k hk]
    exact Util.Bytes.extract_append_left _ _
  -- The layers are the hop packets.
  have hpriv : ∀ k, nike.decodePrivateKey (toVecN nike.privateKeySize
      (ofVector (nike.encodePrivateKey (targetSk k)))) = some (targetSk k) := fun k => by
    rw [toVecN_ofVector, nike.decode_encode_priv]
  have hlayer : ∀ k, k < hops.size → layer nike cipher macS kdfS streamS geom hops d payload k
      = .ok (hopPacket groupElements riPadding s t hops.size k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [h0, hpkteq, hhdreq]
      unfold hopPacket
      rw [Nat.sub_zero, ite_eq_right (lt_irrefl 0), ByteArray.append_empty, hsprp]
    | succ k ih =>
      intro hk
      obtain ⟨tag, cmds, hsz, hun, -⟩ := NT t ht0size htstep k hk _ (hpriv k)
      obtain ⟨ss, hss, hfwd⟩ := unwrapNIKE_forward nike cipher macS kdfS streamS geom _ _
        (targetSk k) (hpriv k) tag cmds _ hun
      have hdh : nikeDH nike (targetSk k) groupElements[k]! = Except.ok (ofVector
          (nike.encodeSharedSecret (telescopeSecret nike clientSk (targetSk k) f k).1)) := by
        rw [(hgcontent k (by omega)).1, nikeDH_bridge nike (targetSk k)
          (telescopeElem nike clientSk f k).1 (telescopeElem nike clientSk f k).2,
          telescope_agree nike clientSk (targetSk k) f k]
      rw [(hopPacket_slices nike macS geom hops keys groupElements riKeyStream riPadding sprpKeys
        hops.size s t hvalid hmactag hs0size hstep hgsize hgesize hpadsize htsize ht0size hsprp hgen
        k (by omega)).2.1, hdh] at hss
      obtain rfl := Except.ok.inj hss
      rw [← (hgcontent k (by omega)).2.1, ← hK k (by omega)] at hfwd
      rw [layer_succ nike cipher macS kdfS streamS geom hops d payload k _ (ih (by omega)), ← hfwd]
      rfl
  have hti' : nike.decodePrivateKey (toVecN nike.privateKeySize
      (ofVector (nike.encodePrivateKey sk))) = some (targetSk i) := by
    rw [hti, toVecN_ofVector, nike.decode_encode_priv]
  -- The packet at position `i` with its payload replaced by `P`.
  have hP : ∀ P : ByteArray, P.size = geom.payloadTagLength + geom.forwardPayloadLength →
      (trace cipher sprpKeys P i 0).size = geom.payloadTagLength + geom.forwardPayloadLength ∧
      hopPacket groupElements riPadding s (trace cipher sprpKeys P i) hops.size i
        = (hopPacket groupElements riPadding s t hops.size i).extract 0 geom.headerLength ++ P := by
    intro P hPs
    refine ⟨by rw [trace_size, hPs], ?_⟩
    rw [hH, hext i hi, ← hsprp,
      trace_at cipher sprpKeys (sprpKeys.size - i) i P rfl (by omega) (by omega)]
  refine ⟨_, hdr, sprpKeys, hlayer i hi, hpsize i hi, hcreate, hsprp, hsprpK, ?_, fun hlt => ?_,
    fun hlast => ⟨fun hns => ?_, fun hs P hPs => ?_⟩⟩
  · rw [hpkteq, ← createHeader_hdr_size nike macS kdfS streamS geom _ _ hops hdr sprpKeys hvalid
      hmactag hcreate]
    exact Util.Bytes.extract_append_left _ _
  · obtain ⟨tag, cmds, hsz, hun, hc⟩ := NT t ht0size htstep i hlt _ hti'
    refine ⟨_, toVec32 (s (hops.size - 1 - i)).2, hlayer (i + 1) hlt, ?_, fun P hPs => ?_⟩
    · rw [unwrap_of_ok nike cipher macS kdfS streamS geom sk _ _ _ _ _ hun, hc]
      rfl
    · obtain ⟨hs0', hpk⟩ := hP P hPs
      obtain ⟨tag', cmds', hsz', hun', hc'⟩ :=
        NT (trace cipher sprpKeys P i) hs0' (fun _ _ => rfl) i hlt _ hti'
      have hu : unwrap nike cipher macS kdfS streamS geom sk
          (hopPacket groupElements riPadding s (trace cipher sprpKeys P i) hops.size i)
          = some (none, cmds', some (hopPacket groupElements riPadding s
            (trace cipher sprpKeys P i) hops.size (i + 1))) :=
        unwrap_of_ok nike cipher macS kdfS streamS geom sk _ _ _ _ _ hun'
      rw [hpk] at hu
      rw [hu, hc', hH, hext (i + 1) hlt, ← hsprp,
        trace_next cipher sprpKeys P i (by omega) (by omega), hsprpK i hi]
      rfl
  · exact unwrap_of_ok nike cipher macS kdfS streamS geom sk _ _ _ _ _
      (unwrapNIKE_hopPacket_terminal nike cipher macS kdfS streamS geom hops keys groupElements
        riKeyStream riPadding sprpKeys hops.size s t clientSk f targetSk hvalid hmactag hs0size
        hstep hgsize hgesize hgcontent hpadsize (fun i hi => (hriContent i hi).1) htsize ht0size
        htstep hsprpkey hsprp hgen h16 i hlast (hnn i hi) (hnh i hi) hns payload hpaysize
        ht0content _ hti')
  · obtain ⟨hs0', hpk⟩ := hP P hPs
    have hu : unwrap nike cipher macS kdfS streamS geom sk
        (hopPacket groupElements riPadding s (trace cipher sprpKeys P i) hops.size i)
        = some (some (trace cipher sprpKeys P i 0), hops[i]!.commands, none) :=
      unwrap_of_ok nike cipher macS kdfS streamS geom sk _ _ _ _ _
        ((LT (trace cipher sprpKeys P i) hs0' (fun _ _ => rfl) i hlast _ hti').trans
          (ite_eq_left hs))
    have h0' := trace_next cipher sprpKeys P i (by omega) (by omega)
    rw [show sprpKeys.size - (i + 1) = 0 by omega, hsprpK i hi] at h0'
    rw [hpk] at hu
    rw [hu, h0']
    rfl

/-! ## The four laws -/

variable {geom} in
theorem path_size (R : Protocols.RSOR.Route geom.nrHops Name (Key nike))
    (last : List RoutingCommand) : (path nike R last).size = R.hops.length := by
  simp [path]

variable {geom} in
theorem path_getElem! (R : Protocols.RSOR.Route geom.nrHops Name (Key nike))
    (last : List RoutingCommand) (j : ℕ) (h : j < R.hops.length) :
    (path nike R last)[j]! = ⟨R.hops[j].name, ofVector (nike.encodePublicKey R.hops[j].key.1),
      if j + 1 = R.hops.length then last else []⟩ := by
  simp [path, h]

variable {geom} in
/-- Every relay on a route has a private key. -/
theorem path_keys (R : Protocols.RSOR.Route geom.nrHops Name (Key nike))
    (last : List RoutingCommand) : ∀ j < (path nike R last).size, ∃ sk,
      (path nike R last)[j]!.publicKey
        = ofVector (nike.encodePublicKey (nike.derivePublicKey sk)) := by
  intro j hj
  rw [path_size] at hj
  obtain ⟨sk, hsk⟩ := R.hops[j].key.2
  exact ⟨sk, by rw [path_getElem! nike R last j hj, hsk]⟩

variable {geom} in
/-- A hop of a route has the commands of the last hop, or none. -/
theorem path_commands (R : Protocols.RSOR.Route geom.nrHops Name (Key nike))
    (last : List RoutingCommand) (p : RoutingCommand → Prop) (hp : ∀ c ∈ last, p c) :
    ∀ j < (path nike R last).size, ∀ c ∈ (path nike R last)[j]!.commands, p c := by
  intro j hj c hc
  rw [path_size] at hj
  rw [path_getElem! nike R last j hj] at hc
  dsimp only at hc
  split at hc
  · exact hp c hc
  · simp at hc

theorem peeled_size (ks : List HopKeys) (p : ByteArray) : (peeled cipher ks p).size = p.size :=
  List.foldl_size_preserving _ _ (fun _ _ => cipher.decrypt_size _ _ _) p

theorem peeled_concat (ks : List HopKeys) (k : HopKeys) (p : ByteArray) :
    peeled cipher (ks ++ [k]) p = dec cipher k (peeled cipher ks p) := by
  simp [peeled]

/-- A relay on the forward path gets the next layer, and the exit relay the message. -/
theorem proc_form (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request nike geom) (r : Randomness nike geom) (i : Fin q.fwd.hops.length)
    (sk : nike.PrivateKey)
    (hr : Builds nike cipher macS kdfS streamS geom q.fwd [.recipient q.receiver] r.1
      (body nike macS kdfS streamS geom q r))
    (hk : (q.fwd.hops[i].key, sk) ∈ support (keygen nike)) :
    proc nike cipher macS kdfS streamS geom sk (form nike cipher macS kdfS streamS geom q r i)
      = some (if h : i + 1 < q.fwd.hops.length
        then .forward q.fwd.hops[i.val + 1].name
          (form nike cipher macS kdfS streamS geom q r ⟨i + 1, h⟩)
        else .deliver q.msg q.receiver) := by
  obtain ⟨pkt0, h0⟩ := hr (List.length_pos_iff.2 q.fwd_ne)
  have hn := path_size nike q.fwd [RoutingCommand.recipient q.receiver]
  obtain ⟨pkt, -, -, hpkt, hsz, -, -, -, -, hmid, hlast⟩ := unwrap_layer nike cipher macS kdfS
    streamS geom hvalid hmactag h16 _ r.1 _ pkt0 h0 (path_keys nike q.fwd _)
    (path_commands nike q.fwd _ _ (by simp)) (path_commands nike q.fwd _ _ (by simp)) i
    (by rw [hn]; exact i.isLt) sk
    (by
      rw [path_getElem! nike _ _ _ i.isLt]
      exact congrArg (fun k => ofVector (nike.encodePublicKey k)) (key_of_keygen nike _ _ hk))
  obtain ⟨-, -, -, -, hpacket, -⟩ := id hvalid
  unfold proc form
  rw [hpkt]
  dsimp only
  rw [join_split geom pkt (by omega) (by omega)]
  by_cases h : i + 1 < q.fwd.hops.length
  · obtain ⟨pkt', mac, hpkt', hun, -⟩ := hmid (by rw [hn]; exact h)
    rw [hun, dite_eq_left h, hpkt', path_getElem! nike _ _ _ i.isLt, path_getElem! nike _ _ _ h]
    simp [show ¬ (i.val + 1 = q.fwd.hops.length) by omega]
  · have hcmd : (path nike q.fwd [RoutingCommand.recipient q.receiver])[i.val]!.commands
        = [RoutingCommand.recipient q.receiver] := by
      rw [path_getElem! nike _ _ _ i.isLt, ite_eq_left (by omega)]
    have hmsg : msgOf geom (body nike macS kdfS streamS geom q r) = q.msg := by
      unfold msgOf body
      have := Cryptlib.Util.Bytes.extract_append_right
        (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ ++ (surb nike macS kdfS streamS geom q r).1)
        (ofVector q.msg)
      rw [Cryptlib.Util.Bytes.size_ofVector] at this
      rw [ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector, Nat.add_sub_cancel, this,
        toVecN_ofVector]
    rw [(hlast (by rw [hn]; omega)).1 (by rw [hcmd]; simp), dite_eq_right h, hcmd]
    simp [hmsg]

theorem newNIKESURB_eq (ck : ByteArray) (kp : Vector UInt8 64) (fill : ByteArray)
    (hops : Array PathHop) (hdr : ByteArray) (keys : Array SPRPKey)
    (h : createHeader nike macS kdfS streamS geom ck fill hops = .ok (hdr, keys)) :
    newNIKESURB nike macS kdfS streamS geom ck kp fill hops
      = .ok (hdr ++ ofVector (hops[0]!).id ++ ofVector kp, surbKeys keys kp) := by
  unfold newNIKESURB
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rw [h]
  rfl

/-- A reply's payload as the exit relay sends it: the padded message under the SURB's payload
key. -/
def sealed (kp : Vector UInt8 64) (m : Msg geom) : ByteArray :=
  cipher.encrypt ((ofVector kp).extract 0 48).data ((ofVector kp).extract 48 64)
    ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pad geom m)

/-- The SURB of a request with a backward path: its keys are the hops' payload keys, and a reply
packet built from it has the header of the first layer on that path. -/
theorem reply_spec (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request nike geom) (r : Randomness nike geom) (m : Msg geom)
    (hr : Reliable nike cipher macS kdfS streamS geom q r) (hb : 0 < q.back.hops.length) :
    (sealed cipher geom r.2.2.1 m).size = geom.payloadTagLength + geom.forwardPayloadLength ∧
    (pad geom m).size = geom.forwardPayloadLength ∧
    ∃ (x0 : ByteArray) (sprp : Array SPRPKey),
      layer nike cipher macS kdfS streamS geom (path nike q.back [.surbReply r.2.2.2]) r.2.1
        ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok x0 ∧
      sprp.size = q.back.hops.length ∧
      (∀ j < q.back.hops.length, sprp[j]!
        = ⟨(hopKey nike kdfS (clientKey nike geom r.2.1)
            (path nike q.back [.surbReply r.2.2.2]) j).payloadEncryption,
          (hopKey nike kdfS (clientKey nike geom r.2.1)
            (path nike q.back [.surbReply r.2.2.2]) j).headerEncryptionIV⟩) ∧
      (surb nike macS kdfS streamS geom q r).1
        = x0.extract 0 geom.headerLength ++ ofVector q.back.hops[0].name ++ ofVector r.2.2.1 ∧
      (x0.extract 0 geom.headerLength).size = geom.headerLength ∧
      (surb nike macS kdfS streamS geom q r).2 = surbKeys sprp r.2.2.1 ∧
      SURB.newPacketFromSURB cipher geom (surb nike macS kdfS streamS geom q r).1 (pad geom m)
        = .ok (x0.extract 0 geom.headerLength ++ sealed cipher geom r.2.2.1 m,
          q.back.hops[0].name) ∧
      (replyPacket nike cipher macS kdfS streamS geom q r m).1.extract geom.headerLength
          (replyPacket nike cipher macS kdfS streamS geom q r m).1.size
        = sealed cipher geom r.2.2.1 m := by
  have hpad : (pad geom m).size = geom.forwardPayloadLength := by
    obtain ⟨pk, hpk⟩ := hr.1 (List.length_pos_iff.2 q.fwd_ne)
    obtain ⟨p, hp, -⟩ := (layer_ok nike cipher macS kdfS streamS geom _ _ _ 0 pk).1 hpk
    have h := (newNIKEPacket_unfold nike cipher macS kdfS streamS geom _ _ _ _ _ hp).1
    rw [body, ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector] at h
    rw [pad, ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector]
    show _ + (Array.replicate _ (0 : UInt8)).size = _
    rw [Array.size_replicate]
    omega
  obtain ⟨x0, hx0⟩ := hr.2 hb
  have hn := path_size nike q.back [RoutingCommand.surbReply r.2.2.2]
  obtain ⟨sk0, hsk0⟩ := (q.back.hops[0]'hb).key.2
  obtain ⟨pkt, hdr, sprp, hpkt, -, hcreate, hsprp, hsprpK, hhdr, -, -⟩ := unwrap_layer nike cipher
    macS kdfS streamS geom hvalid hmactag h16 _ r.2.1 _ x0 hx0 (path_keys nike q.back _)
    (path_commands nike q.back _ _ (by simp)) (path_commands nike q.back _ _ (by simp)) 0
    (by rw [hn]; exact hb) sk0 (by rw [path_getElem! nike _ _ _ hb, hsk0])
  obtain ⟨-, -, -, -, -, hsl⟩ := id hvalid
  have hh := createHeader_hdr_size nike macS kdfS streamS geom _ _ _ hdr sprp hvalid hmactag hcreate
  have hsurb : surb nike macS kdfS streamS geom q r
      = (hdr ++ ofVector q.back.hops[0].name ++ ofVector r.2.2.1, surbKeys sprp r.2.2.1) := by
    unfold surb
    dsimp only
    rw [newNIKESURB_eq nike macS kdfS streamS geom _ _ _ _ _ _ hcreate, path_getElem! nike _ _ 0 hb]
  have hnp := newPacketFromSURB_eq cipher geom hdr q.back.hops[0].name r.2.2.1 (pad geom m) hh
    (by rw [hsl]; rfl)
  refine ⟨by rw [sealed, cipher.encrypt_size, size_tagged, hpad], hpad, x0, sprp, hx0,
    by rw [hsprp, hn], fun j hj => hsprpK j (by rw [hn]; exact hj), by rw [hsurb, hhdr],
    by rw [hhdr, hh], by rw [hsurb], by rw [hsurb, hhdr]; exact hnp, ?_⟩
  unfold replyPacket
  rw [hsurb, hnp]
  exact extract_append_tail _ _ _ _ hh (by rw [ByteArray.size_append, hh])

/-- The exit relay's reply is the first layer of the reply onion. -/
theorem reply_form (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request nike geom) (r : Randomness nike geom) (m : Msg geom) (i : Fin q.fwd.hops.length)
    (j : Fin q.back.hops.length) (sk : nike.PrivateKey)
    (hr : Reliable nike cipher macS kdfS streamS geom q r) (hi : i + 1 = q.fwd.hops.length)
    (hj : j.val = 0) (hk : (q.fwd.hops[i].key, sk) ∈ support (keygen nike)) :
    reply nike cipher macS kdfS streamS geom sk m (form nike cipher macS kdfS streamS geom q r i)
      = some (q.back.hops[j].name, formBack nike cipher macS kdfS streamS geom q r m j) := by
  have hjlt : 0 < q.back.hops.length := j.pos
  obtain rfl : j = ⟨0, hjlt⟩ := Fin.ext hj
  obtain ⟨pkt0, h0⟩ := hr.1 (List.length_pos_iff.2 q.fwd_ne)
  have hn := path_size nike q.fwd [RoutingCommand.recipient q.receiver]
  obtain ⟨pkt, -, -, hpkt, hsz, -, -, -, -, -, hlast⟩ := unwrap_layer nike cipher macS kdfS
    streamS geom hvalid hmactag h16 _ r.1 _ pkt0 h0 (path_keys nike q.fwd _)
    (path_commands nike q.fwd _ _ (by simp)) (path_commands nike q.fwd _ _ (by simp)) i
    (by rw [hn]; exact i.isLt) sk
    (by
      rw [path_getElem! nike _ _ _ i.isLt]
      exact congrArg (fun k => ofVector (nike.encodePublicKey k)) (key_of_keygen nike _ _ hk))
  obtain ⟨-, -, -, -, hpacket, -⟩ := id hvalid
  have hcmd : (path nike q.fwd [RoutingCommand.recipient q.receiver])[i.val]!.commands
      = [RoutingCommand.recipient q.receiver] := by
    rw [path_getElem! nike _ _ _ i.isLt, ite_eq_left hi]
  have hp := (hlast (by rw [hn]; exact hi)).1 (by rw [hcmd]; simp)
  obtain ⟨-, -, x0, sprp, hx0, -, -, hs1, hxs, -, hnp, hfirst⟩ :=
    reply_spec nike cipher macS kdfS streamS geom hvalid hmactag h16 q r m hr hjlt
  have hss : (surb nike macS kdfS streamS geom q r).1.size = geom.surbLength := by
    have := hnp
    unfold SURB.newPacketFromSURB at this
    by_contra hne
    simp [hne] at this
    cases this
  have hfl : (body nike macS kdfS streamS geom q r).get! 0 = 1 := by
    have hne : ¬ q.back.hops.isEmpty := by
      rw [List.isEmpty_iff]; exact List.ne_nil_of_length_pos hjlt
    have h2 : (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray).size = 2 := rfl
    unfold body
    rw [KEMSphinx.get!_eq_getElem _ 0
        (by rw [ByteArray.size_append, ByteArray.size_append, h2]; omega),
      ByteArray.getElem_append_left (by rw [ByteArray.size_append, h2]; omega),
      ByteArray.getElem_append_left (by rw [h2]; omega)]
    simp only [hne]
    rfl
  have hsb : (body nike macS kdfS streamS geom q r).extract 2 (2 + geom.surbLength)
      = (surb nike macS kdfS streamS geom q r).1 := by
    unfold body
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
      rw [ByteArray.size_append, hss]; exact Nat.le_refl _)]
    exact extract_append_tail _ _ _ _ rfl (by rw [hss])
  unfold reply form formBack
  dsimp only
  rw [hpkt]
  dsimp only
  rw [join_split geom pkt (by omega) (by omega), hp]
  dsimp only
  rw [ite_eq_left ⟨by rw [hcmd]; rfl, hfl⟩, hsb, hnp, hx0]
  dsimp only
  rw [hfirst]
  rfl

/-- A relay on the backward path gets the next layer. -/
theorem proc_formBack (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request nike geom) (r : Randomness nike geom) (m : Msg geom) (i : Fin q.back.hops.length)
    (h : i.val + 1 < q.back.hops.length) (sk : nike.PrivateKey)
    (hr : Reliable nike cipher macS kdfS streamS geom q r)
    (hk : (q.back.hops[i].key, sk) ∈ support (keygen nike)) :
    proc nike cipher macS kdfS streamS geom sk (formBack nike cipher macS kdfS streamS geom q r m i)
      = some (.forward q.back.hops[i.val + 1].name
          (formBack nike cipher macS kdfS streamS geom q r m ⟨i.val + 1, h⟩)) := by
  obtain ⟨hE, -, x0, sprp, hx0, -, -, -, -, -, -, hfirst⟩ :=
    reply_spec nike cipher macS kdfS streamS geom hvalid hmactag h16 q r m hr (by omega)
  have hn := path_size nike q.back [RoutingCommand.surbReply r.2.2.2]
  obtain ⟨pkt, -, -, hpkt, hsz, -, -, -, -, hmid, -⟩ := unwrap_layer nike cipher macS kdfS
    streamS geom hvalid hmactag h16 _ r.2.1 _ x0 hx0 (path_keys nike q.back _)
    (path_commands nike q.back _ _ (by simp)) (path_commands nike q.back _ _ (by simp)) i
    (by rw [hn]; exact i.isLt) sk
    (by
      rw [path_getElem! nike _ _ _ i.isLt]
      exact congrArg (fun k => ofVector (nike.encodePublicKey k)) (key_of_keygen nike _ _ hk))
  obtain ⟨-, -, -, -, hpacket, -⟩ := id hvalid
  obtain ⟨pkt', mac, hpkt', -, hP⟩ := hmid (by rw [hn]; exact h)
  unfold proc formBack
  dsimp only
  rw [hpkt, hpkt']
  dsimp only
  rw [hfirst, join_split geom _ (by rw [ByteArray.size_append, ByteArray.size_extract]; omega)
      (by rw [ByteArray.size_append, ByteArray.size_extract, peeled_size, hE]; omega),
    hP _ (by rw [peeled_size, hE]), path_getElem! nike _ _ _ i.isLt, path_getElem! nike _ _ _ h,
    hopKeys_succ, peeled_concat]
  simp [show ¬ (i.val + 1 = q.back.hops.length) by omega]

/-- The last relay of the backward path gets a payload that the sender opens to the reply. -/
theorem recover_formBack (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request nike geom) (r : Randomness nike geom) (m : Msg geom) (i : Fin q.back.hops.length)
    (sk : nike.PrivateKey) (hr : Reliable nike cipher macS kdfS streamS geom q r)
    (hi : i.val + 1 = q.back.hops.length)
    (hk : (q.back.hops[i].key, sk) ∈ support (keygen nike)) :
    ∃ p, proc nike cipher macS kdfS streamS geom sk
        (formBack nike cipher macS kdfS streamS geom q r m i) = some (.reply p) ∧
      recover nike cipher macS kdfS streamS geom q r p = some m := by
  obtain ⟨hE, hpad, x0, sprp, hx0, hsprp, hsprpK, -, -, hs2, -, hfirst⟩ :=
    reply_spec nike cipher macS kdfS streamS geom hvalid hmactag h16 q r m hr (by omega)
  have hn := path_size nike q.back [RoutingCommand.surbReply r.2.2.2]
  obtain ⟨pkt, -, -, hpkt, hsz, -, -, -, -, -, hlast⟩ := unwrap_layer nike cipher macS kdfS
    streamS geom hvalid hmactag h16 _ r.2.1 _ x0 hx0 (path_keys nike q.back _)
    (path_commands nike q.back _ _ (by simp)) (path_commands nike q.back _ _ (by simp)) i
    (by rw [hn]; exact i.isLt) sk
    (by
      rw [path_getElem! nike _ _ _ i.isLt]
      exact congrArg (fun k => ofVector (nike.encodePublicKey k)) (key_of_keygen nike _ _ hk))
  obtain ⟨-, -, -, -, hpacket, -⟩ := id hvalid
  have hcmd : (path nike q.back [RoutingCommand.surbReply r.2.2.2])[i.val]!.commands
      = [RoutingCommand.surbReply r.2.2.2] := by
    rw [path_getElem! nike _ _ _ i.isLt, ite_eq_left hi]
  have hP := (hlast (by rw [hn]; exact hi)).2 (by rw [hcmd]; rfl)
  refine ⟨toVecN _ (peeled cipher (hopKeys nike kdfS (clientKey nike geom r.2.1)
    (path nike q.back [.surbReply r.2.2.2]) (i + 1)) (sealed cipher geom r.2.2.1 m)), ?_, ?_⟩
  · unfold proc formBack
    dsimp only
    rw [hpkt]
    dsimp only
    rw [hfirst, join_split geom _ (by rw [ByteArray.size_append, ByteArray.size_extract]; omega)
        (by rw [ByteArray.size_append, ByteArray.size_extract, peeled_size, hE]; omega),
      hP _ (by rw [peeled_size, hE]), hcmd, hopKeys_succ, peeled_concat]
    rfl
  · have hd := decryptSURBPayload_surbKeys cipher geom sprp r.2.2.1 (pad geom m)
      (fun j => peeled cipher (hopKeys nike kdfS (clientKey nike geom r.2.1)
        (path nike q.back [.surbReply r.2.2.2]) j) (sealed cipher geom r.2.2.1 m))
      (by rw [hpad]; exact h16) rfl
      (fun j hj => by rw [hsprpK j (by omega), hopKeys_succ, peeled_concat]; rfl)
    rw [hsprp, ← hi] at hd
    unfold recover
    rw [hs2, ofVector_toVecN _ (by rw [peeled_size, hE]), hd]
    dsimp only
    have := Cryptlib.Util.Bytes.extract_append_left (ofVector m)
      ⟨Array.replicate (geom.forwardPayloadLength - geom.userForwardPayloadLength) 0⟩
    rw [Cryptlib.Util.Bytes.size_ofVector] at this
    rw [pad, this, toVecN_ofVector]

/-- NIKE Sphinx is a repliable service onion routing scheme. A relay does not use its own name. -/
def scheme (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) : Protocols.RSOR.Scheme where
  Name := Name
  Key := Key nike
  Secret := nike.PrivateKey
  Randomness := Randomness nike geom
  Msg := Msg geom
  Receiver := Name
  Header := Vector UInt8 geom.headerLength
  Payload := Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
  maxHops := geom.nrHops
  keygen _ := keygen nike
  form := form nike cipher macS kdfS streamS geom
  formBack := formBack nike cipher macS kdfS streamS geom
  proc sk _ := proc nike cipher macS kdfS streamS geom sk
  reply sk _ := reply nike cipher macS kdfS streamS geom sk
  recover := recover nike cipher macS kdfS streamS geom
  reliable := Reliable nike cipher macS kdfS streamS geom
  proc_form q r i sk hr hk :=
    proc_form nike cipher macS kdfS streamS geom hvalid hmactag h16 q r i sk hr.1 hk
  reply_form q r m i j sk hr hi hj hk :=
    reply_form nike cipher macS kdfS streamS geom hvalid hmactag h16 q r m i j sk hr hi hj hk
  proc_formBack q r m i h sk hr hk :=
    proc_formBack nike cipher macS kdfS streamS geom hvalid hmactag h16 q r m i h sk hr hk
  recover_formBack q r m i sk hr hi hk :=
    recover_formBack nike cipher macS kdfS streamS geom hvalid hmactag h16 q r m i sk hr hi hk

end Cryptlib.Protocols.Sphinx.NIKESphinx.RSOR
