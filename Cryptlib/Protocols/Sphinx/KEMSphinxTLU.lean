/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxKeyed

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

/-! # A packet with one hop's ciphertext and keys given

`packetK` is the packet `newKEMPacket` builds, except that hop `j`'s KEM ciphertext and four keys
are arguments. With the ciphertext and keys the hop's seed gives, it is `newKEMPacket`'s packet
(`packetK_real`). The games that replace an honest relay's keys show the adversary `packetK`. -/

section PacketK

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- A hop's KEM ciphertext, as `createKEMHeader` makes it from the hop's seed. -/
def kemHopCt (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (i : Nat) : ByteArray :=
  match kemEncap kem (path[i]!).publicKey (seeds[i]!) with
  | .ok (ct, _) => ct
  | .error _ => .empty

/-- Hop keys from the four KEM Sphinx uses. -/
def hopKeysOf (t : KeyTuple) : HopKeys := ⟨t.2.2.1, t.2.2.2, t.2.1, t.1, .empty⟩

theorem keyTuple_hopKeysOf (t : KeyTuple) : keyTuple (hopKeysOf t) = t := rfl

/-- `newKEMPacket`'s packet, with hop `j`'s ciphertext `c` and keys `t` given. -/
def packetK (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload : ByteArray) (j : Nat) (c : ByteArray) (t : KeyTuple) : Except String ByteArray :=
  newKEMPacketFrom kem cipher macS streamS geom
    (Array.ofFn fun i : Fin path.size => if i.val = j then c else kemHopCt kem path seeds i)
    (Array.ofFn fun i : Fin path.size =>
      if i.val = j then hopKeysOf t else kemHopKeys kem kdfS path seeds i)
    filler path payload

/-- With the ciphertext and the keys hop `j`'s seed gives, `packetK` is `newKEMPacket`'s
packet. -/
theorem packetK_real (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload pkt : ByteArray) (j : Nat) (c ss : ByteArray)
    (hj : kemEncap kem (path[j]!).publicKey (seeds[j]!) = .ok (c, ss))
    (h : newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload = .ok pkt) :
    packetK kem cipher macS kdfS streamS geom seeds filler path payload j c
      (keyTuple (deriveHopKeys kdfS ss)) = .ok pkt := by
  obtain ⟨-, hdr, sprpKeys, t, hcreate, -, -, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom seeds filler path payload pkt h
  obtain ⟨hpos, hgen, hseeds, hfsize, ke, keys, -, -, s, -, -, -, -, hkc, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom seeds filler path hdr sprpKeys hcreate
  have key := newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom seeds filler
    path payload
    (Array.ofFn fun i : Fin path.size => kemHopCt kem path seeds i)
    (Array.ofFn fun i : Fin path.size => kemHopKeys kem kdfS path seeds i)
    hpos hgen hseeds hfsize (by simp) (by simp) (fun i hi => by
      obtain ⟨ct, ss', henc, -, -⟩ := hkc i hi
      refine ⟨ct, ss', henc, ?_, ?_⟩
      · rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
        unfold kemHopCt
        rw [henc]
      · rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
        unfold kemHopKeys
        rw [henc])
  rw [h] at key
  have hke : (Array.ofFn fun i : Fin path.size =>
      if i.val = j then c else kemHopCt kem path seeds i)
      = Array.ofFn fun i : Fin path.size => kemHopCt kem path seeds i := by
    congr 1
    funext i
    split_ifs with hi
    · subst hi
      unfold kemHopCt
      rw [hj]
    · rfl
  have hk : ∀ i : Nat,
      keyTuple ((Array.ofFn fun i : Fin path.size => if i.val = j
        then hopKeysOf (keyTuple (deriveHopKeys kdfS ss))
        else kemHopKeys kem kdfS path seeds i)[i]!)
      = keyTuple ((Array.ofFn fun i : Fin path.size => kemHopKeys kem kdfS path seeds i)[i]!) := by
    intro i
    by_cases hi : i < path.size
    · rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i (by simpa using hi)]
      simp only [Array.getElem_ofFn]
      split_ifs with hij
      · subst hij
        rw [keyTuple_hopKeysOf]
        unfold kemHopKeys
        rw [hj]
      · rfl
    · simp [hi]
  unfold packetK
  rw [key, hke]
  exact newKEMPacketFrom_congr kem cipher macS streamS geom _ _ _ filler path payload
    (fun i => congrArg (·.2.2.1) (hk i)) (fun i => congrArg (·.2.2.2) (hk i))
    (fun i => congrArg (·.2.1) (hk i)) (fun i => congrArg (·.1) (hk i))

/-- `packetK` does not use hop `j`'s seed. -/
theorem packetK_congr (seeds seeds' : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload : ByteArray) (j : Nat) (c : ByteArray) (t : KeyTuple)
    (h : ∀ i, i ≠ j → seeds[i]! = seeds'[i]!) :
    packetK kem cipher macS kdfS streamS geom seeds filler path payload j c t
      = packetK kem cipher macS kdfS streamS geom seeds' filler path payload j c t := by
  unfold packetK
  congr 2 <;>
    · funext i
      split_ifs with hi
      · rfl
      · simp only [kemHopCt, kemHopKeys, h i hi]

end PacketK

/-! # Tagging-forward layer unlinkability: the worlds as keyed games -/

section Forward

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry) (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- The honest relays of a game, from their names and keys. -/
def honOf (names : Role → RSOR.Name) (pk kb ks : Key kem) : Protocols.RSOR.Honest 𝒮 :=
  Protocols.RSOR.Property.honestOf (S := 𝒮) names (pk, kem.privI.default)
    (kb, kem.privI.default) (ks, kem.privI.default)

/-- What the adversary's first phase leaves the challenger: the key pairs of the two honest
relays that are not behind the oracle, and the challenge. -/
structure ForwardCh (names : Role → RSOR.Name) (pk : Key kem) where
  kb : Key kem × kem.PrivateKey
  ks : Key kem × kem.PrivateKey
  c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
    (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb.1 ks.1)

/-- The first layer of the challenge's onion, with the honest relay's KEM ciphertext and keys
given. -/
def forwardOnionK (names : Role → RSOR.Name) {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (t : KeyTuple) : RSOR.Onion geom :=
  let hops := RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]
  match packetK kem cipher macS kdfS streamS geom (r.1.1.toArray.extract 0 hops.size)
      ((ofVector r.1.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
      hops (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
      (ofVector (kem.encodeCiphertext c)) t with
  | .ok pkt => RSOR.split geom pkt
  | .error _ => default

theorem extract_setIfInBounds_getElem? {α : Type} (a : Array α) (j m i : ℕ) (s : α)
    (h : i ≠ j) : ((a.setIfInBounds j s).extract 0 m)[i]? = (a.extract 0 m)[i]? := by
  simp [Array.getElem?_extract, Ne.symm h]

/-- The challenger's randomness with the seed for forward position `j` replaced. -/
def setSeed (r : RSOR.Randomness geom) (j : Nat) (s : Vector UInt8 32) : RSOR.Randomness geom :=
  ((r.1.1.setIfInBounds j s, r.1.2), r.2)

theorem setIfInBounds_getElem_self {α : Type} {n : ℕ} (v : Vector α n) (j : ℕ) (h : j < n) :
    v.setIfInBounds j v[j] = v := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_setIfInBounds]
  split_ifs with hji
  · subst hji; rfl
  · rfl

/-- Drawing the challenger's randomness and a seed, and putting the seed at forward position
`j`, is drawing the randomness. -/
theorem evalDistEq_setSeed {δ : Type} (j : ℕ) (hj : j < geom.nrHops)
    (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (setSeed geom r j s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  have hg : Function.Bijective (Function.uncurry
      fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) => (setSeed geom r j s, r.1.1[j])) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun p => (setSeed geom p.1 j p.2, p.1.1.1[j]), ?_, ?_⟩ <;>
    · rintro ⟨r, s⟩
      simp [setSeed, Function.uncurry, setIfInBounds_getElem_self _ _ hj]
  have hp := evalDistEq_pair_of_bijective
    (g := fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) => (r, s))
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => h, fun p => ⟨p, rfl⟩⟩ (fun p => K p.1)
  exact ((evalDistEq_pair_of_bijective hg
    (fun p : RSOR.Randomness geom × Vector UInt8 32 => K p.1)).trans hp.symm).trans
    (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r))

/-- With the ciphertext and keys that the seed `s` gives at the honest relay's position, the
keyed first layer is the first layer of the challenge's onion, built from the randomness with
`s` at that position. -/
theorem forwardOnionK_real (names : Role → RSOR.Name) {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (s : Vector UInt8 32) (c : kem.Ciphertext) (ss pkt : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
      (setSeed geom r ch.c.pos s).1
      (RSOR.body kem macS kdfS streamS geom ch.c.req (setSeed geom r ch.c.pos s)) 0 = .ok pkt) :
    forwardOnionK kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c
        (keyTuple (deriveHopKeys kdfS ss))
      = RSOR.form kem cipher macS kdfS streamS geom ch.c.req (setSeed geom r ch.c.pos s)
          ch.c.req.first := by
  have hn := RSOR.path_size kem ch.c.req.fwd [.recipient ch.c.req.receiver]
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hle : ch.c.req.fwd.hops.length ≤ geom.nrHops := ch.c.req.fwd.length_le
  have hkey : (ch.c.req.fwd.hops[(ch.c.pos : ℕ)]'hpos).key = pk := congrArg (·.key) ch.c.relay
  have hposn : (ch.c.pos : ℕ)
      < (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size := by
    rw [hn]; exact hpos
  have hlen : (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size ≤ geom.nrHops := by
    rw [hn]; exact hle
  have hpub :
      ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos : ℕ)]!).publicKey
        = ofVector (kem.encodePublicKey pk.1) := by
    rw [RSOR.path_getElem! kem _ _ _ hpos]
    exact congrArg (fun k : Key kem => ofVector (kem.encodePublicKey k.1)) hkey
  have hform : RSOR.form kem cipher macS kdfS streamS geom ch.c.req (setSeed geom r ch.c.pos s)
      ch.c.req.first = RSOR.split geom pkt := by
    unfold RSOR.form
    rw [show RSOR.layer kem cipher macS kdfS streamS geom _ _ _ (ch.c.req.first : ℕ) = .ok pkt
      from hpkt]
  rw [hform]
  unfold RSOR.layer at hpkt
  dsimp only at hpkt
  simp only [RSOR.fillerAt, Array.extract_size] at hpkt
  have hs : ((setSeed geom r ch.c.pos s).1.1.toArray.extract 0
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)[(ch.c.pos : ℕ)]! = s := by
    rw [getElem!_extract_zero _ _ _ hposn (by rw [Vector.size_toArray]; exact hlen)]
    simp [setSeed, lt_of_lt_of_le hposn hlen]
  have h1 := packetK_real kem cipher macS kdfS streamS geom _ _ _ _ pkt ch.c.pos
    (ofVector (kem.encodeCiphertext c)) ss
    (by rw [hs, hpub]; exact henc) hpkt
  have h2 := packetK_congr kem cipher macS kdfS streamS geom
    (r.1.1.toArray.extract 0 (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
    ((setSeed geom r ch.c.pos s).1.1.toArray.extract 0
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
    ((ofVector r.1.2).extract 0
      ((geom.nrHops - (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
        * geom.perHopRoutingInfoLength))
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
    (ofVector (kem.encodeCiphertext c)) (keyTuple (deriveHopKeys kdfS ss))
    (fun i hi => by
      simp only [setSeed, Vector.setIfInBounds, Array.getElem!_eq_getD,
        Array.getD_eq_getD_getElem?]
      rw [extract_setIfInBounds_getElem? _ _ _ _ _ hi])
  unfold forwardOnionK
  dsimp only
  rw [h2]
  have h1' : packetK kem cipher macS kdfS streamS geom
      ((setSeed geom r ch.c.pos s).1.1.toArray.extract 0
        (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
      ((ofVector r.1.2).extract 0
        ((geom.nrHops - (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
          * geom.perHopRoutingInfoLength))
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
      (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
      (ofVector (kem.encodeCiphertext c)) (keyTuple (deriveHopKeys kdfS ss)) = .ok pkt := h1
  rw [h1']

/-- World 0 of TLU→ around the honest relay's ciphertext and keys: the challenger draws its
randomness and shows the first layer of the adversary's own onion. -/
def forwardSetup (names : Role → RSOR.Name) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool where
  Ch := ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names
  Oth := RSOR.Randomness geom
  drawOth _ := $ᵗ RSOR.Randomness geom
  view ch r c t :=
    { onion := forwardOnionK kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c t }
  final _ _ _ _ out := out

/-- The adversary of the keyed game that an adversary of TLU→ gives. It draws the keys of the
two honest relays that are not behind the oracle, and answers for all three. -/
def forwardAdv (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    KeyedAdversary (forwardSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names) where
  St := A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)
  pre pk := do
    let kb ← (liftM (keygen kem) : OracleComp procSpec _)
    let ks ← (liftM (keygen kem) : OracleComp procSpec _)
    let sk : Role → kem.PrivateKey := fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2
    let out ← (simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 sk {})
      (A.choose (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb.1
        ks.1))).run {}
    return (⟨kb, ks, out.1.1⟩, (out.1.2, out.2, sk))
  post st w :=
    (simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 st.2.2 w.patch)
      (A.guess st.1 w.onion)).run' st.2.1

/-- The first phase of `forwardAdv`, answered by the honest relay: it is the first phase of the
adversary of TLU→ against the game's honest relays. -/
theorem forwardAdv_pre (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (k : Key kem × kem.PrivateKey) :
    simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
        ((forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)
      = (do
        let kb ← keygen kem
        let ks ← keygen kem
        let out ← (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
            (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) {})
          (A.choose (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1
            ks.1))).run {}
        return (⟨kb, ks, out.1.1⟩,
          (out.1.2, out.2, fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2))) := by
  have hv : ∀ (kb ks : Key kem × kem.PrivateKey) {α : Type}
      (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α),
      simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
          ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16
            (fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2) {}) oa).run {})
        = (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
            (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) {}) oa).run {} :=
    fun kb ks _ oa => viaOracle_honest kem cipher macS kdfS streamS geom hvalid hmactag h16 _
      (fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2)
      (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2)
      (fun h hr => by cases h <;> first | rfl | exact absurd rfl hr) {} oa {}
  unfold forwardAdv
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_procImpl_liftM, hv]

/-- The second phase of `forwardAdv`, answered by the keyed relay with the keys of the
ciphertext's own secret: it is the second phase of the adversary of TLU→ against the game's
honest relays. -/
theorem forwardAdv_post (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (k kb ks : Key kem × kem.PrivateKey)
    (c : kem.Ciphertext) (K : kem.Plaintext) (hdec : decapOf kem k.2 c = some K)
    (st : A.State) (log : Protocols.RSOR.Log 𝒮) (w : Protocols.RSOR.World 𝒮) :
    simulateQ (procImplK kem cipher macS kdfS streamS geom k.2 c ((hopKeysPRG kem kdfS).gen K))
        ((forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post
          (st, log, fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2) w)
      = (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
            (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) w.patch)
          (A.guess st w.onion)).run' log := by
  have hv := viaOracle_honest kem cipher macS kdfS streamS geom hvalid hmactag h16
    (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
    (fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2)
    (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2)
    (fun h hr => by cases h <;> first | rfl | exact absurd rfl hr) w.patch (A.guess st w.onion) log
  rw [procImplK_real kem cipher macS kdfS streamS geom k.2 c K hdec]
  unfold forwardAdv
  simp only [StateT.run', simulateQ_map]
  exact congrArg (fun x => (·.1) <$> x) hv

end Forward

end Cryptlib.Protocols.Sphinx.KEMSphinx
