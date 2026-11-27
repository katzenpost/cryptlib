/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxProp

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.KEMSphinx (keysKs keysTag keysEnc evalDistEq_pair_of_bijective
  prEvent_bind_toReal_sub_le_of_bad relayImpl)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # TLU→ for NIKE Sphinx: the worlds as views of the hops' keys -/

section Onion

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- The first layer of `q`'s onion, from the forward path's first group element and its hops'
keys. Of the randomness it reads the filler and the backward path's draws. -/
def onionOfKeys (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
      (RSOR.path nike q.fwd [.recipient q.receiver])
      (RSOR.body nike macS kdfS streamS geom q r) with
  | some pkt => split geom (peels nike cipher streamS geom ks i pkt)
  | none => default

variable {nike geom} in
/-- The randomness with the forward path's secret replaced. -/
def setKey (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) :
    RSOR.Randomness nike geom :=
  ((d, r.1.2), r.2)

/-- **On the sender's own keys it is the sender's onion**, at any layer, when the onion
builds. -/
theorem onionOfKeys_real (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (d : Vector UInt8 nike.privateKeySize) (pkt : ByteArray) (i : Fin q.fwd.hops.length)
    (h : RSOR.layer nike cipher macS kdfS streamS geom
      (RSOR.path nike q.fwd [.recipient q.receiver]) (setKey r d).1
      (RSOR.body nike macS kdfS streamS geom q (setKey r d)) 0 = .ok pkt) :
    onionOfKeys nike cipher macS kdfS streamS geom i q r
        (groupElem nike ((nike.decodePrivateKey d).getD default)
          (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
            (RSOR.path nike q.fwd [.recipient q.receiver])
            (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray 0)
        (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
          (RSOR.path nike q.fwd [.recipient q.receiver])
          (RSOR.path nike q.fwd [.recipient q.receiver]).size)
      = RSOR.form nike cipher macS kdfS streamS geom q (setKey r d) i := by
  have hf : RSOR.form nike cipher macS kdfS streamS geom q (setKey r d) i
      = split geom (peels nike cipher streamS geom
        (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom (setKey r d).1) (RSOR.path nike q.fwd
            [.recipient q.receiver]) (RSOR.path nike q.fwd [.recipient q.receiver]).size)
        i pkt) := by
    unfold RSOR.form
    rw [layer_peels nike cipher macS kdfS streamS geom _ _ _ (i : ℕ) (RSOR.path nike q.fwd
        [.recipient q.receiver]).size
      (by rw [RSOR.path_size]; exact le_of_lt i.isLt), h]
    rfl
  have hp := layer_zero_pktFn nike cipher macS kdfS streamS geom _ _ _ pkt h
    (RSOR.path_keys nike q.fwd [.recipient q.receiver])
  rw [hf]
  unfold onionOfKeys
  rw [show blindElem nike (groupElem nike ((nike.decodePrivateKey d).getD default)
      (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
        (RSOR.path nike q.fwd [.recipient q.receiver])
        (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray 0) _
      = groupElem nike ((nike.decodePrivateKey d).getD default) _ from
    funext fun i => (groupElem_eq_blindElem nike _ _ i).symm]
  dsimp only [setKey, RSOR.clientKey, RSOR.filler, RSOR.body, RSOR.surb] at hp ⊢
  rw [hp]

omit cipher macS kdfS streamS in
/-- Drawing the challenger's randomness and a secret, and putting the secret on the forward
path, is drawing the randomness. -/
theorem evalDistEq_setKey {δ : Type} (K : RSOR.Randomness nike geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness nike geom)
      let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
      K (setKey r d)) =ᵈ ($ᵗ (RSOR.Randomness nike geom) >>= K) := by
  have hg : Function.Bijective (Function.uncurry
      fun (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) =>
        (setKey r d, r.1.1)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun p => (setKey p.1 p.2, p.1.1.1), ?_, ?_⟩ <;>
    · rintro ⟨r, d⟩
      rfl
  have hp := evalDistEq_pair_of_bijective
    (g := fun (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) => (r, d))
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => h, fun p => ⟨p, rfl⟩⟩ (fun p => K p.1)
  exact ((evalDistEq_pair_of_bijective hg
    (fun p : RSOR.Randomness nike geom × Vector UInt8 nike.privateKeySize => K p.1)).trans
      hp.symm).trans
    (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 nike.privateKeySize)) (K r))

/-- The first layer of `q`'s onion, with the tag of hop `j` given. -/
def onionOfTag (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) (j : ℕ) (tag : ByteArray) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray)
      (Function.update (keysTag macS ks.toArray) j fun _ => tag)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
          q.fwd [.recipient q.receiver])
      (RSOR.body nike macS kdfS streamS geom q r) with
  | some pkt => split geom (peels nike cipher streamS geom ks i pkt)
  | none => default

/-- The bytes of `q`'s onion that hop `j`'s tag covers. -/
def onionMsg (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) (j : ℕ) : ByteArray :=
  hdrMsg geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
    (blindElem nike a ks.toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j

omit cipher macS kdfS streamS geom in
theorem toArray_getElem!_congr {α : Type} [Inhabited α] (l l' : List α) (i : ℕ)
    (h : l[i]? = l'[i]?) : l.toArray[i]! = l'.toArray[i]! := by
  simp [getElem!_def, h]

/-- The relays in front of the replaced hop peel with the sender's keys, whatever the
replacement. -/
theorem peels_hopKeysWith (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (t t' : HopKeys)
    (ht : RSOR.factor nike t = RSOR.factor nike t') (n i : ℕ) (hi : i ≤ j) :
    peels nike cipher streamS geom (hopKeysWith nike kdfS c hops j t n) i
      = peels nike cipher streamS geom (hopKeysWith nike kdfS c hops j t' n) i := by
  have htake : (hopKeysWith nike kdfS c hops j t n).take i
      = (hopKeysWith nike kdfS c hops j t' n).take i :=
    List.ext_getElem? fun m => by
      rw [List.getElem?_take, List.getElem?_take]
      split
      · exact (hopKeysWith_congr nike kdfS c hops j t t' ht n).2 m (by omega)
      · rfl
  funext pkt
  unfold peels
  rw [htake]

/-- **The onion uses the replaced hop's MAC key for one tag only.** With the hop's keys replaced,
the onion is the onion built from the replacement without its MAC key and the tag of
`onionMsg` under that key. -/
theorem onionOfKeys_tag (i : ℕ) (q : RSOR.Request nike geom) (rnd : RSOR.Randomness nike geom)
    (a : ByteArray) (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (r : Rest)
    (km : Vector UInt8 32) (n : ℕ) (hj : j < n) (hjp : j < (RSOR.path nike q.fwd [.recipient
        q.receiver]).size)
    (hi : i ≤ j := by omega) :
    onionOfKeys nike cipher macS kdfS streamS geom i q rnd a
        (hopKeysWith nike kdfS c hops j (restKeys r km) n)
      = onionOfTag nike cipher macS kdfS streamS geom i q rnd a
        (hopKeysWith nike kdfS c hops j (restKeys r default) n) j
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (onionMsg nike macS streamS geom q rnd a
            (hopKeysWith nike kdfS c hops j (restKeys r default) n) j))) := by
  have hne : ∀ i, i ≠ j → (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray[i]!
      = (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray[i]! := fun i hi =>
    toArray_getElem!_congr _ _ i ((hopKeysWith_congr nike kdfS c hops j (restKeys r km)
      (restKeys r default) rfl n).2 i hi)
  have hj1 : (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray[j]! = restKeys r km :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j _ n hj)
  have hj0 : (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray[j]!
      = restKeys r default :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j _ n hj)
  have hks : keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray := by
    funext i
    unfold keysKs
    by_cases hi : i = j
    · rw [hi, hj1, hj0]; rfl
    · rw [hne i hi]
  have henc : keysEnc cipher (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = keysEnc cipher (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray := by
    funext i
    unfold keysEnc
    by_cases hi : i = j
    · rw [hi, hj1, hj0]; rfl
    · rw [hne i hi]
  have hge : blindElem nike a (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = blindElem nike a (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray := by
    funext i
    refine blindElem_congr nike a _ _ (fun m => ?_) i
    by_cases hm : m = j
    · rw [hm, hj1, hj0]; rfl
    · rw [hne m hm]
  have htag : keysTag macS (hopKeysWith nike kdfS c hops j (restKeys r km) n).toArray
      = Function.update
        (keysTag macS (hopKeysWith nike kdfS c hops j (restKeys r default) n).toArray) j
        (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) m)) := by
    funext i
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      unfold keysTag
      rw [hj1]
      rfl
    · rw [Function.update_of_ne hi]
      unfold keysTag
      rw [hne i hi]
  have hpl := peels_hopKeysWith nike cipher kdfS streamS geom c hops j (restKeys r km)
    (restKeys r default) rfl n i hi
  unfold onionOfKeys onionOfTag onionMsg
  rw [hpl, hks, henc, hge, htag, nikePktFn_tagAt geom _ _ _ _ _ _ _ j hjp
    (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) m))]

/-- The first layer of `q`'s onion, with the tag of hop `j` and its encryption of the payload
given. -/
def onionOfEnc (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) (j : ℕ) (tag e : ByteArray) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray)
      (Function.update (keysTag macS ks.toArray) j fun _ => tag)
      (Function.update (keysEnc cipher ks.toArray) j fun _ => e) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
          q.fwd [.recipient q.receiver])
      (RSOR.body nike macS kdfS streamS geom q r) with
  | some pkt => split geom (peels nike cipher streamS geom ks i pkt)
  | none => default

/-- The block of `q`'s onion that hop `j` encrypts: the payload after the hops behind it. -/
def onionBlock (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (ks : List HopKeys)
    (j : ℕ) : ByteArray :=
  encTrace (keysEnc cipher ks.toArray) (RSOR.path nike q.fwd [.recipient q.receiver]).size
    ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)
      ++ RSOR.body nike macS kdfS streamS geom q r) ((RSOR.path nike q.fwd [.recipient
          q.receiver]).size - 1 - j)

/-- **The onion uses hop `j`'s payload key for one encryption**, of `onionBlock`. -/
theorem onionOfTag_enc (i : ℕ) (q : RSOR.Request nike geom) (rnd : RSOR.Randomness nike geom)
    (a : ByteArray) (ks : List HopKeys) (j : ℕ) (tag : ByteArray) (hjp : j < (RSOR.path nike q.fwd
        [.recipient q.receiver]).size) :
    onionOfTag nike cipher macS kdfS streamS geom i q rnd a ks j tag
      = onionOfEnc nike cipher macS kdfS streamS geom i q rnd a ks j tag
        (cipher.encrypt (ks.toArray[j]!).payloadEncryption.toArray
          (Util.Bytes.ofVector (ks.toArray[j]!).headerEncryptionIV)
          (onionBlock nike cipher macS kdfS streamS geom q rnd ks j)) := by
  have henc : keysEnc cipher ks.toArray = Function.update (keysEnc cipher ks.toArray) j
      (fun b => cipher.encrypt (ks.toArray[j]!).payloadEncryption.toArray
        (Util.Bytes.ofVector (ks.toArray[j]!).headerEncryptionIV) b) := by
    funext i
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
  unfold onionOfTag onionOfEnc onionBlock
  rw [henc, nikePktFn_encAt geom _ _ _ _ _ _ _ j hjp, ← henc]

/-- **These read hop `j`'s payload key nowhere else.** Two key lists that agree but for hop
`j`'s payload key give the same onion from the encrypted block, the same bytes under hop `j`'s
tag, and the same block for hop `j` to encrypt. -/
theorem onion_payloadKey (i : ℕ) (q : RSOR.Request nike geom) (rnd : RSOR.Randomness nike geom)
    (a : ByteArray) (ks ks' : List HopKeys) (j : ℕ) (tag e : ByteArray) (hjp : j < (RSOR.path nike
        q.fwd [.recipient q.receiver]).size)
    (hne : ∀ i, i ≠ j → ks.toArray[i]! = ks'.toArray[i]!)
    (hj : ks.toArray[j]! = { ks'.toArray[j]! with
      payloadEncryption := (ks.toArray[j]!).payloadEncryption })
    (hpl : peels nike cipher streamS geom ks i = peels nike cipher streamS geom ks' i := by rfl) :
    onionOfEnc nike cipher macS kdfS streamS geom i q rnd a ks j tag e
        = onionOfEnc nike cipher macS kdfS streamS geom i q rnd a ks' j tag e ∧
      onionMsg nike macS streamS geom q rnd a ks j
        = onionMsg nike macS streamS geom q rnd a ks' j ∧
      onionBlock nike cipher macS kdfS streamS geom q rnd ks j
        = onionBlock nike cipher macS kdfS streamS geom q rnd ks' j := by
  have hks : keysKs geom streamS ks.toArray = keysKs geom streamS ks'.toArray := by
    funext i
    unfold keysKs
    by_cases hi : i = j
    · rw [hi, hj]
    · rw [hne i hi]
  have htag : keysTag macS ks.toArray = keysTag macS ks'.toArray := by
    funext i
    unfold keysTag
    by_cases hi : i = j
    · rw [hi, hj]
    · rw [hne i hi]
  have hge : blindElem nike a ks.toArray = blindElem nike a ks'.toArray := by
    funext i
    refine blindElem_congr nike a _ _ (fun m => ?_) i
    by_cases hm : m = j
    · rw [hm, hj]
    · rw [hne m hm]
  have hencne : ∀ i, i ≠ j → keysEnc cipher ks.toArray i = keysEnc cipher ks'.toArray i :=
    fun i hi => by unfold keysEnc; rw [hne i hi]
  refine ⟨?_, ?_, ?_⟩
  · have hu : Function.update (keysEnc cipher ks.toArray) j (fun _ => e)
        = Function.update (keysEnc cipher ks'.toArray) j (fun _ => e) := by
      funext i
      by_cases hi : i = j
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, hencne i hi]
    unfold onionOfEnc
    rw [hks, htag, hge, hu, hpl]
  · unfold onionMsg
    rw [hks, htag, hge]
  · unfold onionBlock
    exact encTrace_congr _ _ _ _ _ (by omega) fun i hi _ => hencne i (by omega)

/-- The first layer of `q`'s onion, with hop `j`'s header keystream, tag and encryption of the
payload given. -/
def onionOfStream (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a :
    ByteArray)
    (ks : List HopKeys) (j : ℕ) (U tag e : ByteArray) : Onion geom :=
  match nikePktFn geom (Function.update (keysKs geom streamS ks.toArray) j U)
      (Function.update (keysTag macS ks.toArray) j fun _ => tag)
      (Function.update (keysEnc cipher ks.toArray) j fun _ => e) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
          q.fwd [.recipient q.receiver])
      (RSOR.body nike macS kdfS streamS geom q r) with
  | some pkt => split geom (peels nike cipher streamS geom ks i pkt)
  | none => default

/-- The bytes of `q`'s onion that hop `j`'s tag covers, with its header keystream given. -/
def onionMsgStream (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) (j : ℕ) (U : ByteArray) : ByteArray :=
  hdrMsg geom (Function.update (keysKs geom streamS ks.toArray) j U) (keysTag macS ks.toArray)
    (blindElem nike a ks.toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j

/-- **The onion reads hop `j`'s header key and IV through its keystream only.** Two key lists
that agree but for those give the same onion, tagged bytes and block, once the keystream is
handed over. -/
theorem onion_streamKey (i : ℕ) (q : RSOR.Request nike geom) (rnd : RSOR.Randomness nike geom)
    (a : ByteArray) (ks ks' : List HopKeys) (j : ℕ) (tag e : ByteArray) (hjp : j < (RSOR.path nike
        q.fwd [.recipient q.receiver]).size)
    (hne : ∀ i, i ≠ j → ks.toArray[i]! = ks'.toArray[i]!)
    (hj : ks.toArray[j]! = { ks'.toArray[j]! with
      headerEncryption := (ks.toArray[j]!).headerEncryption
      headerEncryptionIV := (ks.toArray[j]!).headerEncryptionIV })
    (hpl : peels nike cipher streamS geom ks i = peels nike cipher streamS geom ks' i := by rfl) :
    onionOfEnc nike cipher macS kdfS streamS geom i q rnd a ks j tag e
        = onionOfStream nike cipher macS kdfS streamS geom i q rnd a ks' j
          (keysKs geom streamS ks.toArray j) tag e ∧
      onionMsg nike macS streamS geom q rnd a ks j
        = onionMsgStream nike macS streamS geom q rnd a ks' j (keysKs geom streamS ks.toArray j) ∧
      onionBlock nike cipher macS kdfS streamS geom q rnd ks j
        = onionBlock nike cipher macS kdfS streamS geom q rnd ks' j := by
  have hks : keysKs geom streamS ks.toArray
      = Function.update (keysKs geom streamS ks'.toArray) j (keysKs geom streamS ks.toArray j) := by
    funext i
    by_cases hi : i = j
    · rw [hi, Function.update_self]
    · rw [Function.update_of_ne hi]
      unfold keysKs
      rw [hne i hi]
  have htag : keysTag macS ks.toArray = keysTag macS ks'.toArray := by
    funext i
    unfold keysTag
    by_cases hi : i = j
    · rw [hi, hj]
    · rw [hne i hi]
  have hge : blindElem nike a ks.toArray = blindElem nike a ks'.toArray := by
    funext i
    refine blindElem_congr nike a _ _ (fun m => ?_) i
    by_cases hm : m = j
    · rw [hm, hj]
    · rw [hne m hm]
  have hencne : ∀ i, i ≠ j → keysEnc cipher ks.toArray i = keysEnc cipher ks'.toArray i :=
    fun i hi => by unfold keysEnc; rw [hne i hi]
  refine ⟨?_, ?_, ?_⟩
  · have hu : Function.update (keysEnc cipher ks.toArray) j (fun _ => e)
        = Function.update (keysEnc cipher ks'.toArray) j (fun _ => e) := by
      funext i
      by_cases hi : i = j
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, hencne i hi]
    unfold onionOfEnc onionOfStream
    rw [hu, htag, hge, hpl]
    rw [hks]
    simp only [Function.update_self]
  · unfold onionMsg onionMsgStream
    rw [htag, hge]
    rw [hks]
    simp only [Function.update_self]
  · unfold onionBlock
    exact encTrace_congr _ _ _ _ _ (by omega) fun i hi _ => hencne i (by omega)

end Onion

section Forward

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- Setting a hop's public key to the one it has changes nothing. -/
theorem modify_publicKey_self (hops : Array PathHop) (j : ℕ) (x : ByteArray) (hj : j < hops.size)
    (hx : hops[j]!.publicKey = x) :
    hops.modify j (fun h => { h with publicKey := x }) = hops := by
  refine Array.ext (by simp) fun i h1 h2 => ?_
  rw [Array.getElem_modify]
  split
  · next hji =>
    subst hji
    rw [getElem!_pos hops j hj] at hx
    subst hx
    rfl
  · rfl

/-- What the adversary's first phase of TLU→ leaves the challenger, with the forward relay
behind the oracle. -/
abbrev ForwardCh (names : Role → Name) (pk : RSOR.Key nike) :=
  PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
      := 𝒮)) .relay names pk

/-- A world of TLU→ as the later steps see it: what the challenger draws, the request whose
onion it shows and that onion's randomness, the patch it puts around the onion's layer at the
honest relay, and the path whose keys the key game replaces. That path has the request's relays;
it is fixed before the challenger draws. -/
structure FwdWorld (names : Role → Name) where
  Oth : Type
  draw : ProbComp Oth
  req : {pk : RSOR.Key nike} → ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names pk → Oth → RSOR.Request nike geom
  rnd : Oth → RSOR.Randomness nike geom
  patch : {pk : RSOR.Key nike} → ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names pk → Oth → Onion geom
    → Protocols.RSOR.Patch 𝒮
  hops : {pk : RSOR.Key nike} → ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names pk → Array PathHop
  size_eq : ∀ {pk : RSOR.Key nike} (ch : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names pk) (o : Oth),
    (RSOR.path nike (req ch o).fwd [.recipient (req ch o).receiver]).size = (hops ch).size
  pos_lt : ∀ {pk : RSOR.Key nike} (ch : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names pk), (ch.c.pos : ℕ) < (hops ch).size

/-- World 0: the adversary's own request, no patch. -/
def fwd0 (names : Role → Name) : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag h16
    names where
  Oth := RSOR.Randomness nike geom
  draw := $ᵗ RSOR.Randomness nike geom
  req ch _ := ch.c.req
  rnd r := r
  patch _ _ _ := {}
  hops ch := RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]
  size_eq _ _ := rfl
  pos_lt ch := lt_of_lt_of_eq ch.c.pos.isLt (RSOR.path_size nike ch.c.req.fwd _).symm

/-- The path whose keys the key game replaces, and the honest relay's place on it. -/
def forwardPlace (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {pk : RSOR.Key nike} (ch : ForwardCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 names pk) :
    Array PathHop × ℕ :=
  (W.hops ch, ch.c.pos)

/-- The world shown: the first layer of the request's onion, from the hops' keys, and the patch
around its layer at the honest relay. -/
def forwardView (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {pk : RSOR.Key nike} (ch : ForwardCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 names pk)
    (r : W.Oth) (a : ByteArray) (ks : List HopKeys) :
    Protocols.RSOR.World 𝒮 :=
  { onion := onionOfKeys nike cipher macS kdfS streamS geom 0 (W.req ch r) (W.rnd r) a ks
    patch := W.patch ch r
      (onionOfKeys nike cipher macS kdfS streamS geom ch.c.pos (W.req ch r) (W.rnd r) a ks) }

/-- The adversary on the key game for world 0. -/
abbrev forwardAdv (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    : KeyAdversary nike :=
  propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
      (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
          names W) W.Oth W.draw (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W) A

/-- The draws of a world. -/
abbrev forwardDraw (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    ProbComp (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A) :=
  propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ W.draw A

/-- The honest relay's place is on the path whose keys are replaced. -/
theorem fwd_hops_pos (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A) :
    drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
        (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
        names W) D
      < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names W) D).size := by
  show (D.c.pos : ℕ) < (Array.modify (W.hops (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names D.k.1))
    D.c.pos _).size
  rw [Array.size_modify]
  exact W.pos_lt (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names D.k.1)

/-- The honest relay's place is on the request's path. -/
theorem fwd_path_pos (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A) :
    (D.c.pos : ℕ) < (RSOR.path nike (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names D.k.1) D.o).fwd
      [.recipient (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names D.k.1) D.o).receiver]).size := by
  rw [W.size_eq]
  exact W.pos_lt (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names D.k.1)

/-- World 0 of TLU→ as its draws, then the adversary's guess on the first layer of its own
onion, built with the forward path's secret drawn apart. -/
theorem play_false_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    Protocols.RSOR.Property.play names A false
      =ᵈ forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A >>= fun D =>
        (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag
            h16 .relay names D.k.1 D.keys)
            (fun h => if h = .relay then D.k.2 else (D.keys h).2) {})
          (A.guess D.st (RSOR.form nike cipher macS kdfS streamS geom D.c.req
            (setKey D.o D.d) D.c.req.first))).run' D.log := by
  refine (play_evalDistEq_honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names A false).trans ?_
  unfold Protocols.RSOR.Property.playFrom forwardDraw propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun kb =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun out => ?_
  have h := evalDistEq_setKey nike geom fun r =>
    (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
        .relay names k.1 (keysOf nike .relay kb ks))
        (fun h => if h = .relay then k.2 else (keysOf nike .relay kb ks h).2) {})
      (A.guess out.1.2 (RSOR.form nike cipher macS kdfS streamS geom out.1.1.req r
        out.1.1.req.first))).run' out.2
  have hw : Protocols.RSOR.forwardUnlinkable.world out.1.1 false = (do
      let r ← $ᵗ (RSOR.Randomness nike geom)
      return { onion := (RSOR.form nike cipher macS kdfS streamS geom out.1.1.req r
        out.1.1.req.first) }) := by
    simp [Protocols.RSOR.forwardUnlinkable]
    rfl
  refine EvalDistEq.trans ?_ h.symm
  rw [hw]
  simp only [bind_assoc, pure_bind]
  exact EvalDistEq.rfl

/-- The draws that the exact step does not cover: the adversary's onion cannot be built. -/
def forwardBad {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness nike geom) A) :
        Prop :=
  ¬ ∃ pkt, RSOR.layer nike cipher macS kdfS streamS geom
    (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) (setKey D.o D.d).1
    (RSOR.body nike macS kdfS streamS geom D.c.req (setKey D.o D.d)) 0 = .ok pkt

/-- **World 0 of TLU→ is the key game's real world, off the bad draws.** -/
theorem play_false_sub_keyGame_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyGame cipher macS kdfS streamS geom
          (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) A)
          true)}[x = true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        A)}[forwardBad nike cipher macS kdfS streamS geom hvalid hmactag h16 D]).toReal := by
  rw [(play_false_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyGame_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ _ _ _ A).prEvent_eq (fun x => x
        = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _ (forwardBad nike cipher macS kdfS streamS geom
      hvalid hmactag h16) (fun D hD => ?_)
    (fun x => x = true)
  obtain ⟨pkt, hpkt⟩ := Classical.not_not.mp hD
  have hpos : (D.c.pos : ℕ) < D.c.req.fwd.hops.length := D.c.pos.isLt
  have hsz := RSOR.path_size nike D.c.req.fwd [.recipient D.c.req.receiver]
  have hkey : (D.c.req.fwd.hops[(D.c.pos : ℕ)]'hpos).key = D.k.1 := congrArg (·.key) D.c.relay
  have hmod := modify_publicKey_self
    (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
    (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1)) (by rw [hsz]; exact hpos) (by
      rw [RSOR.path_getElem! nike _ _ _ hpos]
      exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1))
        hkey)
  unfold propRealOf
  dsimp only [forwardPlace, fwd0]
  rw [hmod]
  refine Eq.trans ?_ (ite_eq_left (show (D.c.pos : ℕ)
    < (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size by
      rw [hsz]; exact hpos)).symm
  dsimp only [forwardView, fwd0]
  have e := onionOfKeys_real nike cipher macS kdfS streamS geom D.c.req D.o D.d pkt
    D.c.req.first hpkt
  rw [show onionOfKeys nike cipher macS kdfS streamS geom 0 D.c.req D.o _ _ = _ from e]

/-- **World 0 of TLU→ with the honest relay's keys replaced.** Playing world 0 with the relay's
keys for the adversary's onion uniform, the hops after it derived from them, and the relay
answering that onion's element with them, changes the adversary's guess by at most the chance
that the onion cannot be built and the advantage of `forwardAdv` in the key game. -/
theorem play_false_sub_ideal_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (($ᵗ (KEMSphinx.KeyTuple × Vector UInt8 32)) >>= fun u =>
          forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) A >>= propIdealOf
              nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
                  streamS geom hvalid hmactag h16 names)) _
            (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
                cipher macS kdfS streamS geom hvalid hmactag h16 names)) A u)}[x =
                true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        A)}[forwardBad nike cipher macS kdfS streamS geom hvalid hmactag h16 D]).toReal
      + keyAdvantage cipher macS kdfS streamS geom (forwardAdv nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) A) := by
  have h1 := play_false_sub_keyGame_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
  rw [← (keyGame_false_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names)) _ _
    (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names)) A).prEvent_eq (fun x
        => x = true)]
  unfold keyAdvantage
  exact (abs_sub_le _ _ _).trans (add_le_add h1 le_rfl)

/-- The hops' keys of a draw of world 0, the honest relay's without a MAC key. -/
def forwardKeys0 (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A) : List
    HopKeys :=
  drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
      (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
          names W) x default

/-- The bytes of the adversary's onion that the honest relay's tag covers. -/
def forwardMsg (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x
    : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A) :
    ByteArray :=
  onionMsg nike macS streamS geom (W.req (⟨x.2.keys, x.2.c⟩ : ForwardCh nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names x.2.k.1) x.2.o) (W.rnd x.2.o)
    (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2) (forwardKeys0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names W x).toArray 0)
    (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x) x.2.c.pos

/-- World 0 from the honest relay's tag. -/
def forwardViewT (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A)
    (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  { onion := onionOfTag nike cipher macS kdfS streamS geom 0 (W.req (⟨x.2.keys, x.2.c⟩ : ForwardCh
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names x.2.k.1) x.2.o) (W.rnd x.2.o)
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names W x).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x) x.2.c.pos
          (Util.Bytes.ofVector tag)
    patch := W.patch (⟨x.2.keys, x.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names x.2.k.1) x.2.o
      (onionOfTag nike cipher macS kdfS streamS geom x.2.c.pos (W.req (⟨x.2.keys, x.2.c⟩ : ForwardCh
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names x.2.k.1) x.2.o) (W.rnd x.2.o)
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names W x).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x) x.2.c.pos
          (Util.Bytes.ofVector tag)) }

/-- **The MAC step for world 0 of TLU→.** With the honest relay's keys replaced, the relay may
answer the element of the adversary's onion under that onion's header only, at the cost of a
forgery against the MAC and the chance that the bytes its tag covers do not have a header's
length. -/
theorem forward_ideal_sub_only_le (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS
    geom hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let b ← (keyGame cipher macS kdfS streamS geom
          (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) false)}[b =
              true]).toReal
      - (Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W) _
          W.draw (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) A
          (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W))}[b =
              true]).toReal|
    ≤ (Pr{let b ← (Primitives.MAC.forgeExp macS
          (macForge nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names W) _ W.draw A
            (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W)
                (forwardViewT nike cipher macS kdfS streamS geom hvalid hmactag h16 names W)))}[b =
                true]).toReal
      + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ W.draw
          A)}[¬ (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x).size =
              (2 + nike.publicKeySize + geom.routingInfoLength)]).toReal := by
  refine keyGame_false_sub_gameOnly_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) _ _
    (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) A (forwardMsg nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names W) (forwardViewT nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names W)
    (fun x => (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x).size = (2
        + nike.publicKeySize + geom.routingInfoLength)) (fun x hg => hg) (fun x km _ => ?_)
  have hlt := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x.2
  have hjp := fwd_path_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x.2
  unfold drawView forwardView forwardViewT forwardMsg forwardKeys0
  exact congrArg₂ (fun o m => Protocols.RSOR.World.mk (S := 𝒮) o (W.patch
      (⟨x.2.keys, x.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          x.2.k.1) x.2.o m))
    (onionOfKeys_tag nike cipher macS kdfS streamS geom 0
      (W.req (⟨x.2.keys, x.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names x.2.k.1) x.2.o) (W.rnd x.2.o) _ _ _ _ x.1 km
      _ hlt hjp)
    (onionOfKeys_tag nike cipher macS kdfS streamS geom x.2.c.pos
      (W.req (⟨x.2.keys, x.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names x.2.k.1) x.2.o) (W.rnd x.2.o) _ _ _ _ x.1 km
      _ hlt hjp (le_refl _))

/-! ## World 0 after its MAC step, cut at the honest relay's payload key -/

/-- The draws of world 0 besides the honest relay's payload key: its IV, MAC key, header key
and blinding seed, and the game's draws. -/
abbrev PayX (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :=
  Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 32 × PropDraw nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      W.Oth A

/-- The draws of the MAC step, from those and a payload key. -/
def payRest (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x :
    PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (kp : Vector UInt8 48) : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A :=
  (((kp, x.1, x.2.2.1), x.2.2.2.1), x.2.2.2.2)

/-- The hops' keys with and without the honest relay's payload key: they agree off the relay,
and at the relay they are the relay's draws. -/
theorem payKeys (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (kp : Vector UInt8 48) :
    (∀ i, i ≠ (x.2.2.2.2.c.pos : ℕ) →
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp)).toArray[i]!
        = (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W x default)).toArray[i]!) ∧
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp)).toArray[(x.2.2.2.2.c.pos :
          ℕ)]!
        = restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp).1
            default := by
  have hlt := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x.2.2.2.2
  refine ⟨fun i hi => toArray_getElem!_congr _ _ i ?_, ?_⟩
  · exact (hopKeysWith_congr nike kdfS _ _ _ (restKeys (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names W x kp).1 default)
      (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x default).1
          default) rfl _).2 i hi
  · exact toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hlt)

/-- The honest relay's tag on the adversary's onion. -/
def payTag (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x :
    PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) :
    Vector UInt8 macS.tagSize :=
  macS.mac (Util.Bytes.ofVector x.2.1)
    (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
        (S := 𝒮)) .relay names (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x
            default))

/-- The header of the adversary's onion at the honest relay. -/
def payHeader (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x
    : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) :
    Vector UInt8 geom.headerLength :=
  Util.Bytes.toVecN _ (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W x default)
    ++ Util.Bytes.ofVector (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x))

/-- **World 0 after its MAC step, as a game cut at the honest relay's payload key.** -/
def forwardPay (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    Protocols.RSOR.PayloadGame 𝒮 (geom.payloadTagLength + geom.forwardPayloadLength) where
  role := .relay
  X := PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A
  draw iv := do
    let km ← $ᵗ (Vector UInt8 32)
    let he ← $ᵗ (Vector UInt8 32)
    let seed ← $ᵗ (Vector UInt8 32)
    let D ← forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A
    return (iv, km, he, seed, D)
  header := payHeader nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
  key o := o.2
  step x o y := stepOf geom (procD nike (Primitives.MAC.MAC.const (payTag nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names W x)) streamS geom
    (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x
        default).1 default)) (fun _ _ => y) (join o))
  rep x msg o y := replyOf cipher geom msg (procD nike
    (Primitives.MAC.MAC.const (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
        x)) streamS geom
    (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x
        default).1 default)) (fun _ _ => y) (join o))
  proc x h o := if h = .relay then
      stepOf geom (noneAns nike cipher macS kdfS streamS geom x.2.2.2.2.k.2
        (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names W) x.2.2.2.2) (join o))
    else RSOR.proc nike cipher macS kdfS streamS geom (x.2.2.2.2.keys h).2 o
  reply x h msg o := if h = .relay then
      replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom x.2.2.2.2.k.2
        (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names W) x.2.2.2.2) (join o))
    else RSOR.reply nike cipher macS kdfS streamS geom (x.2.2.2.2.keys h).2 msg o
  plain x := Util.Bytes.toVecN _ (onionBlock nike cipher macS kdfS streamS geom
    (W.req (⟨x.2.2.2.2.keys, x.2.2.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names x.2.2.2.2.k.1) x.2.2.2.2.o) (W.rnd x.2.2.2.2.o) (forwardKeys0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names W x default))
    x.2.2.2.2.c.pos)
  log x := x.2.2.2.2.log
  patch x e := W.patch (⟨x.2.2.2.2.keys, x.2.2.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names x.2.2.2.2.k.1) x.2.2.2.2.o
    (onionOfEnc nike cipher macS kdfS streamS geom x.2.2.2.2.c.pos (W.req
          (⟨x.2.2.2.2.keys, x.2.2.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names x.2.2.2.2.k.1) x.2.2.2.2.o) (W.rnd x.2.2.2.2.o)
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2.2.2)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names W x default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W x default)) x.2.2.2.2.c.pos
        (Util.Bytes.ofVector (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
            x)) (Util.Bytes.ofVector e))
  rest x e :=
    if drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names W) x.2.2.2.2
        < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names W) x.2.2.2.2).size then
      A.guess x.2.2.2.2.st (onionOfEnc nike cipher macS kdfS streamS geom 0 (W.req
          (⟨x.2.2.2.2.keys, x.2.2.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names x.2.2.2.2.k.1) x.2.2.2.2.o) (W.rnd x.2.2.2.2.o)
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2.2.2)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names W x default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W x default)) x.2.2.2.2.c.pos
        (Util.Bytes.ofVector (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
            x)) (Util.Bytes.ofVector e))
    else pure false

/-- The draws of world 0 on which its payload game is exact: the bytes under the honest
relay's tag have a header's length and carry the element that reaches the relay, and the block
the relay encrypts has a payload's length. -/
def payGood (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x :
    PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) : Prop :=
  (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names W x default)).size = (2 + nike.publicKeySize +
      geom.routingInfoLength) ∧
    (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names W x default)).extract 2 (2 +
        nike.publicKeySize)
      = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W) x.2.2.2.2 ∧
    (onionBlock nike cipher macS kdfS streamS geom (W.req (⟨x.2.2.2.2.keys, x.2.2.2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names x.2.2.2.2.k.1)
        x.2.2.2.2.o) (W.rnd x.2.2.2.2.o)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W x default)) x.2.2.2.2.c.pos).size
          = (geom.payloadTagLength + geom.forwardPayloadLength)

set_option maxHeartbeats 2000000 in
/-- **World 0 after its MAC step is its payload game with the cipher, draw by draw.** -/
theorem forwardPay_run (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom
    hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (x : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (kp : Vector UInt8 48) (hg : payGood nike cipher macS kdfS streamS geom hvalid hmactag h16
        names W x) :
    simulateQ (relayImpl (Relay.ansOf
        (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize)
          = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names W) x.2))
        (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp)
        (Relay.onlyT macS (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
            .relay names (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W))
          (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
            (fun _ => .ok (restKeys x.1 default)))
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp)
          (macS.mac (Util.Bytes.ofVector x.2.1)
            (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike cipher
                    macS kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS
                    kdfS streamS geom hvalid hmactag h16 names W x kp))))))
      (drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names W x kp)
        (drawView nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names W) (forwardView nike cipher macS kdfS
                streamS geom hvalid hmactag h16 names W)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp) x.2.1))
    = (simulateQ (Protocols.RSOR.withDec (S := 𝒮) (forwardPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names W A).role
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).header x)
            (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).key
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).step x)
            ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rep x)
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).proc x)
            ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).reply x)
        (fun y => Util.Bytes.toVecN _ (cipher.decrypt kp.toArray (Util.Bytes.ofVector x.1)
          (Util.Bytes.ofVector y)))
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).patch x
            (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray
          (Util.Bytes.ofVector x.1) (Util.Bytes.ofVector ((forwardPay nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names W A).plain x))))))
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rest x
            (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray
          (Util.Bytes.ofVector x.1)
          (Util.Bytes.ofVector ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W A).plain x)))))).run'
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).log x) := by
  obtain ⟨iv, km, he, seed, D⟩ := x
  obtain ⟨hM, hcar, hblk⟩ := hg
  have hlt := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names W D
  have hjp : (D.c.pos : ℕ) < (RSOR.path nike (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o).fwd [.recipient (W.req (⟨D.keys, D.c⟩
      : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1)
      D.o).receiver]).size :=
    fwd_path_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names W D
  obtain ⟨hne, hj⟩ := payKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km,
      he, seed, D) kp
  obtain ⟨-, hj0⟩ := payKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km,
      he, seed, D) default
  have hK : (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
      kp)).toArray[(D.c.pos : ℕ)]!
      = { (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
          default)).toArray[(D.c.pos : ℕ)]! with
        payloadEncryption :=
          ((forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
              kp)).toArray[(D.c.pos : ℕ)]!).payloadEncryption } := by
    rw [hj, hj0]
    rfl
  have hpk := fun (a tag e : ByteArray) => onion_payloadKey nike cipher macS kdfS streamS geom 0
    (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        D.k.1) D.o) (W.rnd D.o) a _ _ (D.c.pos : ℕ) tag e hjp hne hK
  have hmsg : forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp) =
      forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) default) := (hpk _
      .empty
      .empty).2.1
  have hmacEq : macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (iv, km, he, seed, D) kp) = macMsg nike cipher macS kdfS
          streamS geom
      hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) default) := by
    unfold macMsg
    rw [hmsg]
  have hMeq : macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (iv, km, he, seed, D) default) = forwardMsg nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (iv, km, he, seed, D) default) := Util.Bytes.ofVector_toVecN _
          hM
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have hH : Util.Bytes.ofVector (payHeader nike cipher macS kdfS streamS geom hvalid hmactag h16
      names W (iv, km, he, seed, D))
      = macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names W (iv, km, he, seed, D) default) ++ Util.Bytes.ofVector
              (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he,
              seed, D)) :=
    Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hMeq, hM, Util.Bytes.size_ofVector, hmactag, hhdr]
      rfl)
  have hcar' : (Util.Bytes.ofVector (payHeader nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names W (iv, km, he, seed, D))).extract 2
      (2 + nike.publicKeySize) = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W) D := by
    rw [hH, hMeq, ← hcar]
    exact KEMSphinx.extract_of_prefix_eq (n := (forwardMsg nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        names W (iv, km, he, seed, D) default)).size)
      (by rw [Util.Bytes.extract_append_left]; exact ByteArray.extract_zero_size.symm) 2
      (2 + nike.publicKeySize) (by rw [hM]; omega)
  have hans : Relay.ansOf
        (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize)
          = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names W) x.2))
        (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2)) (payRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp)
        (Relay.onlyT macS (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
            .relay names (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W))
          (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
            (fun _ => .ok (restKeys x.1 default))) (payRest nike cipher macS kdfS streamS geom
                hvalid hmactag h16 names W (iv, km, he, seed, D) kp)
          (macS.mac (Util.Bytes.ofVector km) (macMsg nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp))))
      = onlyAns nike cipher macS kdfS streamS geom D.k.2 (drawElem nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
          (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) D) (restKeys
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed,
          D) kp).1 default) (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names W (iv, km, he, seed, D) default)) (payTag nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)) := by
    funext pkt
    unfold Relay.ansOf Relay.onlyT onlyAns payTag
    rw [hmacEq]
    by_cases he : pkt.extract 2 (2 + nike.publicKeySize) = drawElem nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) D
    · exact (ite_eq_left (decide_eq_true he)).trans (ite_eq_left he).symm
    · exact (ite_eq_right fun h => he (of_decide_eq_true h)).trans (ite_eq_right he).symm
  have hrun : ∀ w, drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (iv, km, he, seed, D) kp) w
      = (simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h
          => (D.keys h).2) w.patch)
        (A.guess D.st w.onion)).run' D.log := fun w => ite_eq_left hlt
  rw [show simulateQ (relayImpl _) _ = simulateQ (relayImpl (onlyAns nike cipher macS kdfS streamS
      geom D.k.2 (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) D) (restKeys (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp).1 default) (macMsg nike
          cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) default))
          (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed,
          D)))) _ from
    congrArg (fun f => simulateQ (relayImpl f) _) hans]
  rw [hrun, viaOracle_congr nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h =>
      (D.keys h).2) (fun h => if h = .relay then D.k.2 else (D.keys h).2)
    (fun h hr => (ite_eq_right hr).symm)]
  refine (relayImpl_onlyAns_run nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay (fun h
      => if h = .relay then D.k.2 else (D.keys h).2) _ _ _ _ (payHeader nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)) hH hcar'
    _ _ _).trans ?_
  have hs : (fun (o : Onion geom) (y : Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength)) => stepOf geom (procD nike
        (Primitives.MAC.MAC.const (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (iv, km, he, seed, D))) streamS geom
        (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (iv, km, he, seed, D) kp).1 default)) (fun _ _ => y) (join o)))
      = (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).step (iv, km,
          he, seed, D) := funext fun o => funext fun y =>
    congrArg (stepOf geom) (procD_payloadKey nike _ streamS geom
      (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he,
          seed, D) default).1 default) kp (fun _ => y) (join o)).symm
  have hr : (fun (msg : Msg geom) (o : Onion geom) (y : Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength)) =>
        replyOf cipher geom msg (procD nike
          (Primitives.MAC.MAC.const (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W (iv, km, he, seed, D))) streamS geom
          (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W (iv, km, he, seed, D) kp).1 default)) (fun _ _ => y) (join o)))
      = (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rep (iv, km,
          he,
          seed, D) := funext fun msg => funext fun o => funext fun y =>
    congrArg (replyOf cipher geom msg) (procD_payloadKey nike _ streamS geom
      (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he,
          seed, D) default).1 default) kp (fun _ => y) (join o)).symm
  have hp : (fun (h : Role) (o : Onion geom) => if h = Role.relay then
        stepOf geom (noneAns nike cipher macS kdfS streamS geom ((fun h => if h = .relay then D.k.2
            else (D.keys h).2) Role.relay) (drawElem nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike
                cipher macS kdfS streamS geom hvalid hmactag h16 names W) D) (join o))
      else RSOR.proc nike cipher macS kdfS streamS geom ((fun h => if h = .relay then D.k.2 else
          (D.keys h).2) h) o)
      = (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).proc (iv, km,
          he, seed, D) := funext fun h => funext fun o => by
    by_cases hh : h = Role.relay
    · subst hh
      rfl
    · exact (ite_eq_right hh).trans ((congrArg (fun k =>
        RSOR.proc nike cipher macS kdfS streamS geom k o) (ite_eq_right hh)).trans
        (ite_eq_right hh).symm)
  have hrp : (fun (h : Role) (msg : Msg geom) (o : Onion geom) => if h = Role.relay then
        replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom ((fun h => if h =
            .relay then D.k.2 else (D.keys h).2) Role.relay)
          (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names W) D) (join o))
      else RSOR.reply nike cipher macS kdfS streamS geom ((fun h => if h = .relay then D.k.2 else
          (D.keys h).2) h) msg o)
      = (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).reply (iv, km,
          he, seed, D) := funext fun h => funext fun msg => funext fun o => by
    by_cases hh : h = Role.relay
    · subst hh
      rfl
    · exact (ite_eq_right hh).trans ((congrArg (fun k =>
        RSOR.reply nike cipher macS kdfS streamS geom k msg o) (ite_eq_right hh)).trans
        (ite_eq_right hh).symm)
  have key : ∀ (impl impl' : QueryImpl (Protocols.RSOR.oracleSpec 𝒮)
      (StateT (Protocols.RSOR.Log 𝒮) ProbComp))
      (oa oa' : OracleComp (Protocols.RSOR.oracleSpec 𝒮) Bool) (log : Protocols.RSOR.Log 𝒮),
      impl = impl' → oa = oa' →
        (simulateQ impl oa).run' log = (simulateQ impl' oa').run' log := by
    rintro _ _ _ _ _ rfl rfl
    rfl
  have htagEq : Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
        (onionMsg nike macS streamS geom (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd D.o) (groupElem nike (drawKey
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
            (S := 𝒮)) .relay names D) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (iv, km, he, seed, D) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W (iv, km, he, seed, D) kp)) (D.c.pos : ℕ)))
      = Util.Bytes.ofVector (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
          (iv, km, he, seed, D)) := by
    unfold payTag
    rw [hMeq]
    exact congrArg (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) m))
      (hpk _ .empty .empty).2.1
  have heEq : cipher.encrypt
        ((forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
            kp)).toArray[(D.c.pos : ℕ)]!).payloadEncryption.toArray
        (Util.Bytes.ofVector
          ((forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
              kp)).toArray[(D.c.pos : ℕ)]!).headerEncryptionIV)
        (onionBlock nike cipher macS kdfS streamS geom (W.req (⟨D.keys, D.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd D.o)
            (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp))
          (D.c.pos : ℕ))
      = Util.Bytes.ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
          (cipher.encrypt kp.toArray
        (Util.Bytes.ofVector iv) (Util.Bytes.ofVector ((forwardPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names W A).plain
          (iv, km, he, seed, D))))) := by
    refine Eq.trans (congrArg (fun t : HopKeys => cipher.encrypt t.payloadEncryption.toArray
      (Util.Bytes.ofVector t.headerEncryptionIV)
      (onionBlock nike cipher macS kdfS streamS geom (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd D.o) (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp))
        (D.c.pos : ℕ))) hj) ?_
    rw [(hpk .empty .empty .empty).2.2]
    show _ = Util.Bytes.ofVector (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray
      (Util.Bytes.ofVector iv) (Util.Bytes.ofVector (Util.Bytes.toVecN _
        (onionBlock nike cipher macS kdfS streamS geom (W.req (⟨D.keys, D.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd D.o)
            (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
            default))
          (D.c.pos : ℕ))))))
    rw [Util.Bytes.ofVector_toVecN _ hblk,
      Util.Bytes.ofVector_toVecN _ (by rw [cipher.encrypt_size, hblk])]
    rfl
  have chain := fun (i : ℕ) (hi : i ≤ (D.c.pos : ℕ))
      (hpl : peels nike cipher streamS geom (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          W (iv, km, he, seed, D) kp)) i
        = peels nike cipher streamS geom (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (iv, km, he, seed, D) default)) i) =>
    (onionOfKeys_tag nike cipher macS kdfS streamS geom i (W.req (⟨D.keys, D.c⟩ : ForwardCh nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd D.o) (groupElem
        nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names W (iv, km, he, seed, D) default)).toArray 0) _ _ _ (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp).1 km _
        hlt hjp
      hi).trans ((onionOfTag_enc nike cipher macS kdfS streamS geom i (W.req (⟨D.keys, D.c⟩ :
          ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd
          D.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D) (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names W (iv, km, he, seed, D) default)).toArray 0) _ _ _
          hjp).trans
      (((onion_payloadKey nike cipher macS kdfS streamS geom i (W.req (⟨D.keys, D.c⟩ : ForwardCh
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd D.o)
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D) (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names W (iv, km, he, seed, D) default)).toArray 0) _ _ (D.c.pos :
          ℕ) _ _ hjp
        hne hK hpl).1).trans (congrArg₂ (fun t e => onionOfEnc nike cipher macS kdfS streamS geom
          i (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
              names D.k.1) D.o) (W.rnd D.o) (groupElem nike (drawKey nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D)
              (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
              default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
              (iv, km, he, seed, D) default)) (D.c.pos : ℕ) t e) htagEq heEq)))
  have hpatch := congrArg (W.patch (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names D.k.1) D.o) (chain (D.c.pos : ℕ) (le_refl _)
    (peels_hopKeysWith nike cipher kdfS streamS geom _ _ _ (restKeys (payRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) kp).1 default)
      (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he,
          seed, D) default).1 default) rfl _ _ (le_refl _)))
  refine key _ _ _ _ _
    (Protocols.RSOR.withDec_congr (S := 𝒮) (L := (geom.payloadTagLength +
        geom.forwardPayloadLength)) _ _ _ _ hs hr hp hrp hpatch) ?_
  refine Eq.trans ?_ (ite_eq_left hlt).symm
  exact congrArg (A.guess D.st) (chain 0 (Nat.zero_le _) rfl)

/-- World 0 after its MAC step, on a draw and a payload key. -/
def payOnlyRun (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (x
    : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (kp : Vector UInt8 48) : ProbComp Bool :=
  simulateQ (relayImpl (Relay.ansOf
      (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize)
        = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names W) x.2))
      (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp)
      (Relay.onlyT macS (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
          names (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W))
        (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
          (fun _ => .ok (restKeys x.1 default)))
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp)
        (macS.mac (Util.Bytes.ofVector x.2.1) (macMsg nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike
                cipher macS kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names W x kp))))))
    (drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names W x kp)
      (drawView nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W) (forwardView nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names W)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x kp) x.2.1))

/-- The payload game of world 0 with the cipher, on a draw and a payload key. -/
def payCipherRun (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (kp : Vector UInt8 48) : ProbComp Bool :=
  (simulateQ (Protocols.RSOR.withDec (S := 𝒮) (forwardPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names W A).role
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).header x)
          (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).key
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).step x)
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rep x)
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).proc x)
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).reply x)
      (fun y => Util.Bytes.toVecN _ (cipher.decrypt kp.toArray (Util.Bytes.ofVector x.1)
        (Util.Bytes.ofVector y)))
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).patch x
          (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray
        (Util.Bytes.ofVector x.1) (Util.Bytes.ofVector ((forwardPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names W A).plain x))))))
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rest x
          (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray
        (Util.Bytes.ofVector x.1)
        (Util.Bytes.ofVector ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W A).plain x)))))).run'
    ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).log x)

/-- The draws of world 0 after its MAC step, the honest relay's payload key first. -/
def payDraw (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ProbComp (Vector UInt8 48 × PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
        A)
        := do
  let kp ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let km ← $ᵗ (Vector UInt8 32)
  let he ← $ᵗ (Vector UInt8 32)
  let seed ← $ᵗ (Vector UInt8 32)
  let D ← forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A
  return (kp, iv, km, he, seed, D)

/-- The payload game of world 0 with the cipher, as its draws and then its run. -/
theorem payExp_true_evalDistEq (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS
    geom hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).exp cipher true
      =ᵈ payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A >>= fun z =>
          payCipherRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A z.2 z.1 := by
  unfold Protocols.RSOR.PayloadGame.exp payDraw payCipherRun
  simp only [bind_assoc, pure_bind, ↓reduceIte]
  refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun iv => ?_
  show ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).draw iv >>= fun
      x => _) =ᵈ _
  unfold forwardPay
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun he =>
    EvalDistEq.bind_right _ fun seed => EvalDistEq.bind_right _ fun D => ?_
  exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)

/-- World 0 after its MAC step, as the same draws and then its run. -/
theorem macOnly_evalDistEq_payDraw (names : Role → Name) (W : FwdWorld nike cipher macS kdfS
    streamS geom hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable
        (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W) _
        W.draw (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) A
            (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W)
      =ᵈ payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A >>= fun z =>
          payOnlyRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A z.2 z.1 := by
  have hb : ∀ {α β : Type},
      Function.Bijective (Function.uncurry fun (a : α) (b : β) => (a, b)) :=
    fun {_ _} => Function.bijective_id
  let F : Vector UInt8 32 → Rest → PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A
      → ProbComp Bool := fun km r D =>
    payOnlyRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A (r.1.2.1, km,
        r.1.2.2,
        r.2, D) r.1.1
  have h0 : macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) _
        W.draw (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) A
            (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W)
      = ($ᵗ (Vector UInt8 32)) >>= fun km => ($ᵗ Rest) >>= fun r =>
        forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A >>= fun D => F
            km
            r D := by
    unfold macOnly Relay.gameOnly macDraw
    simp only [bind_assoc, pure_bind]
    rfl
  rw [h0]
  unfold payDraw
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (rk : KEMSphinx.RestKeys) (seed : Vector UInt8 32) => (rk, seed)) hb _).symm ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (kp : Vector UInt8 48) (t : Vector UInt8 16 × Vector UInt8 32) => (kp, t)) hb
    _).symm ?_
  refine EvalDistEq.bind_right _ fun kp => ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (iv : Vector UInt8 16) (he : Vector UInt8 32) => (iv, he)) hb _).symm ?_
  refine EvalDistEq.bind_right _ fun iv => ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun he =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- The two runs agree on a good draw. -/
theorem payRun_eq (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) (kp : Vector UInt8
        48)
        (hg : payGood nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x) :
    payOnlyRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A x kp = payCipherRun
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A x kp := by
  unfold payOnlyRun payCipherRun
  exact forwardPay_run nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A x kp hg

/-- **The payload step for world 0 of TLU→, first half.** World 0 after its MAC step is its
payload game with the cipher, off the draws that are not good. -/
theorem forward_only_sub_pay_le (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS
    geom hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    |(Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names W) _
          W.draw (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) A
          (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W))}[b =
              true]).toReal
      - (Pr{let b ← ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
          A).exp
          cipher true)}[b = true]).toReal|
    ≤ (Pr{let z ← (payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)}[¬
        payGood nike cipher macS kdfS streamS geom hvalid hmactag h16 names W z.2]).toReal := by
  rw [(macOnly_evalDistEq_payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
      A).prEvent_eq (fun b => b = true),
    (payExp_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
        A).prEvent_eq (fun b => b = true)]
  exact prEvent_bind_toReal_sub_le_of_bad (payDraw nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names W A)
    (fun z => payOnlyRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A z.2 z.1)
        (fun z => payCipherRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A z.2
        z.1)
    (fun z => ¬ payGood nike cipher macS kdfS streamS geom hvalid hmactag h16 names W z.2)
    (fun z hz => payRun_eq nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A z.2 z.1
        (Classical.not_not.mp hz)) (fun b => b = true)

/-- **The payload step for world 0 of TLU→.** World 0 after its MAC step differs from its
payload game with an ideal cipher by the one-query advantage of `forwardPay`'s adversary
against the payload cipher, and the chance of a draw that is not good. -/
theorem forward_only_sub_ideal_le (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS
    geom hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names W) _
          W.draw (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) A
          (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W))}[b =
              true]).toReal
      - (Pr{let b ← ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
          A).exp
          cipher false)}[b = true]).toReal|
    ≤ (Pr{let z ← (payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)}[¬
        payGood nike cipher macS kdfS streamS geom hvalid hmactag h16 names W z.2]).toReal
      + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).adv
                true)}[b
                = true]).toReal
          - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).adv
                false)}[b = true]).toReal| := by
  have hwf : ∀ iv, ∀ x ∈ support ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      names W A).draw iv),
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).log x).WF := by
    intro iv (x : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) hx
    change x ∈ support (($ᵗ (Vector UInt8 32)) >>= fun km => ($ᵗ (Vector UInt8 32)) >>= fun he =>
      ($ᵗ (Vector UInt8 32)) >>= fun seed => forwardDraw nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names W A >>= fun D =>
        pure ((iv, km, he, seed, D) : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W A)) at hx
    obtain ⟨km, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain ⟨he, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain ⟨seed, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain ⟨D, hD, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain rfl : x = (iv, km, he, seed, D) := by
      rw [support_pure] at hx
      exact hx
    exact propDraw_log_wf nike cipher macS kdfS streamS geom hvalid hmactag h16 _ .relay names _ _
        A D hD
  have h1 := forward_only_sub_pay_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A
  rw [← Protocols.RSOR.PayloadGame.exp_eq cipher (forwardPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names W A) hwf true,
    ← Protocols.RSOR.PayloadGame.exp_eq cipher (forwardPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names W A) hwf false]
  exact (abs_sub_le _ _ _).trans (add_le_add h1 le_rfl)

/-! ## World 0 after its payload step, cut at the honest relay's header keystream -/

/-- The draws of world 0 besides the honest relay's header key and IV: its MAC key and blinding
seed, and the game's draws. -/
abbrev StrX (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :=
  Vector UInt8 32 × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A

/-- Those draws as draws of the payload game, with no header key or IV. -/
def strPay (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x :
    StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) : PayX nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names W A :=
  (default, x.1, default, x.2.1, x.2.2)

/-- The bytes under the honest relay's tag, from its header keystream. -/
def strMsg (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x :
    StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (U : KEMSphinx.Keystream geom) : ByteArray :=
  Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
      (onionMsgStream nike macS streamS geom
    (W.req (⟨x.2.2.keys, x.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        names x.2.2.k.1) x.2.2.o) (W.rnd x.2.2.o)
    (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W x) default)).toArray 0)
    (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names W x) default)) x.2.2.c.pos
    (Util.Bytes.ofVector U)))

/-- The honest relay's tag, from its header keystream. -/
def strTag (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary} (x :
    StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (U : KEMSphinx.Keystream geom) : Vector UInt8 macS.tagSize :=
  macS.mac (Util.Bytes.ofVector x.1) (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
      names W x U)

/-- World 0 after its payload step, on its draws and the honest relay's header keystream: the
relay answers one header, decrypts the block `u` to the sender's and any other to `v`. -/
def strRun (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (x :
    StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (U : KEMSphinx.Keystream geom) (u v : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) : ProbComp Bool :=
  (simulateQ (Protocols.RSOR.withDec (S := 𝒮) Role.relay
      (Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x U
          ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W x U)))
      (fun o => o.2)
      (fun o y => stepOf geom (procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W x U))
        (constStream (Util.Bytes.ofVector U)) geom
        (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x)
            default).1
            default))
        (fun _ _ => y) (join o)))
      (fun msg o y => replyOf cipher geom msg (procD nike
        (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W x U)) (constStream (Util.Bytes.ofVector U)) geom
        (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x)
            default).1
            default))
        (fun _ _ => y) (join o)))
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).proc (strPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x))
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).reply (strPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x))
      (fun y => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names W A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x)
          else v)
      (W.patch (⟨x.2.2.keys, x.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
          h16 names x.2.2.k.1) x.2.2.o
        (onionOfStream nike cipher macS kdfS streamS geom x.2.2.c.pos (W.req (⟨x.2.2.keys,
          x.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          x.2.2.k.1) x.2.2.o) (W.rnd x.2.2.o)
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W x) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names W x) default)) x.2.2.c.pos
        (Util.Bytes.ofVector U) (Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W x U))
        (Util.Bytes.ofVector u))))
    (if drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names W) x.2.2
        < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names W) x.2.2).size then
      A.guess x.2.2.st (onionOfStream nike cipher macS kdfS streamS geom 0 (W.req (⟨x.2.2.keys,
          x.2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          x.2.2.k.1) x.2.2.o) (W.rnd x.2.2.o)
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names W x) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names W x) default)) x.2.2.c.pos
        (Util.Bytes.ofVector U) (Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W x U))
        (Util.Bytes.ofVector u))
    else pure false)).run' x.2.2.log

/-- **The adversary against the keystream generator**: it plays world 0 after its payload step
from the keystream it is given. -/
def forwardStreamAdv (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    PRGScheme.PRGAdversary (KEMSphinx.Keystream geom) := fun U => do
  let km ← $ᵗ (Vector UInt8 32)
  let seed ← $ᵗ (Vector UInt8 32)
  let D ← forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A
  let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A (km, seed, D) U u v

/-- The payload game of world 0 with the ideal cipher, on its draws. -/
def payIdealRun (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : PayX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)
    (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) : ProbComp Bool :=
  (simulateQ (Protocols.RSOR.withDec (S := 𝒮) (forwardPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names W A).role
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).header x)
          (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).key
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).step x)
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rep x)
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).proc x)
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).reply x)
      (fun y => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names W A).plain x else v)
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).patch x u))
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rest x u)).run'
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).log x)

set_option maxHeartbeats 4000000 in
/-- **The payload game's ideal world reads the relay's header key and IV through its keystream
only**: on a draw it is `strRun` on that keystream. -/
theorem strRun_eq (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (iv : Vector UInt8 16)
    (km he seed : Vector UInt8 32)
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names W.Oth A) (u
        v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) :
    payIdealRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A (iv, km, he, seed,
        D)
        u v
      = strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A (km, seed, D)
          ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u
        v := by
  have hlt := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names W D
  have hjp : (D.c.pos : ℕ) < (RSOR.path nike (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o).fwd [.recipient (W.req (⟨D.keys, D.c⟩
      : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1)
      D.o).receiver]).size :=
    fwd_path_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names W D
  have hne : ∀ i, i ≠ (D.c.pos : ℕ) → (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
      (iv,
      km, he, seed, D) default)).toArray[i]!
      = (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W (km, seed, D)) default)).toArray[i]! := fun i hi
          =>
    toArray_getElem!_congr _ _ i ((hopKeysWith_congr nike kdfS _ _ _ (restKeys (payRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) default).1 default)
      (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (km, seed, D)) default).1
          default)
          rfl _).2 i hi)
  have hj1 : (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
      default)).toArray[(D.c.pos : ℕ)]! = restKeys (payRest nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (iv, km, he, seed, D) default).1 default :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hlt)
  have hj2 : (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names W (km, seed, D)) default)).toArray[(D.c.pos : ℕ)]! =
      restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (km, seed, D)) default).1
          default :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hlt)
  have hK : (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
      default)).toArray[(D.c.pos : ℕ)]!
      = { (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W (km, seed, D)) default)).toArray[(D.c.pos : ℕ)]!
          with
        headerEncryption := ((forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km,
            he,
            seed, D) default)).toArray[(D.c.pos : ℕ)]!).headerEncryption
        headerEncryptionIV :=
          ((forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D)
              default)).toArray[(D.c.pos : ℕ)]!).headerEncryptionIV } := by
    rw [hj1, hj2]
    rfl
  have hsk := fun (a tag e : ByteArray) => onion_streamKey nike cipher macS kdfS streamS geom 0
    (W.req (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        D.k.1) D.o) (W.rnd D.o) a _ _ (D.c.pos : ℕ) tag e hjp hne hK
  have hU : Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))
      = streamS.keystream (Util.Bytes.ofVector he) (Util.Bytes.ofVector iv)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
    Util.Bytes.ofVector_toVecN _ (streamS.keystream_size _ _ _)
  have hKS : keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km,
      he,
      seed, D) default)).toArray (D.c.pos : ℕ)
      = Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) := by
    unfold keysKs
    rw [hj1, hU]
    rfl
  have hmsg : macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardMsg nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W) (payRest nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (iv, km, he, seed, D) default)
      = strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (km, seed, D)
          ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) := by
    refine congrArg (fun m => Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
        geom.routingInfoLength) m)) ?_
    refine ((hsk _ .empty .empty).2.1).trans ?_
    rw [hKS]
    rfl
  have htag : payTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he,
      seed,
      D)
      = strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (km, seed, D)
          ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) := by
    unfold payTag strTag
    rw [hmsg]
  have hhdr : payHeader nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (iv, km, he,
      seed, D)
      = Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
          (km, seed, D)
          ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))
        ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
            (km, seed, D)
          ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) := by
    unfold payHeader
    rw [hmsg, htag]
  have hks : streamS.keystream (Util.Bytes.ofVector (restKeys (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) default).1
      default).headerEncryption)
      (Util.Bytes.ofVector (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names W (iv, km, he, seed, D) default).1 default).headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      = Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) := hU.symm
  have hstep : (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).step
      (iv,
      km, he, seed, D)
      = (fun (o : Onion geom) (y : Vector UInt8 (geom.payloadTagLength +
          geom.forwardPayloadLength)) => stepOf geom (procD nike
        (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (km, seed, D) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))
            (constStream
            (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) geom
        (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (km, seed,
            D)) default).1 default)) (fun _ _ => y) (join o))) :=
    funext fun o => funext fun y => by
      show stepOf geom (procD nike (Primitives.MAC.MAC.const (payTag nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names W (iv, km, he, seed, D)))
        streamS geom (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names W (iv, km, he, seed, D) default).1 default)) (fun _ _ => y) (join o))
            =
            _
      rw [htag, procD_stream nike _ streamS geom (restKeys (payRest nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names W (iv, km, he, seed, D) default).1 default) default default
        (fun _ => y) (join o), hks]
      rfl
  have hrep : (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rep (iv,
      km, he, seed, D)
      = (fun (msg : Msg geom) (o : Onion geom) (y : Vector UInt8 (geom.payloadTagLength +
          geom.forwardPayloadLength)) =>
        replyOf cipher geom msg (procD nike
          (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W (km, seed, D) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))
              (constStream (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he,
              iv)))) geom
          (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (km,
              seed,
              D)) default).1 default)) (fun _ _ => y) (join o))) :=
    funext fun msg => funext fun o => funext fun y => by
      show replyOf cipher geom msg (procD nike
        (Primitives.MAC.MAC.const (payTag nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (iv, km, he, seed, D)))
        streamS geom (fun _ => .ok (restKeys (payRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names W (iv, km, he, seed, D) default).1 default)) (fun _ _ => y) (join o))
            =
            _
      rw [htag, procD_stream nike _ streamS geom (restKeys (payRest nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names W (iv, km, he, seed, D) default).1 default) default default
        (fun _ => y) (join o), hks]
      rfl
  have hpl : (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).plain (iv,
      km, he, seed, D)
      = (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).plain (strPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (km, seed, D)) :=
    congrArg (Util.Bytes.toVecN _) (hsk .empty .empty .empty).2.2
  have chainS := fun (i : ℕ)
      (hpl' : peels nike cipher streamS geom (forwardKeys0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names W (iv, km, he, seed, D) default)) i
        = peels nike cipher streamS geom (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (km,
            seed, D)) default)) i) =>
    (congrArg (fun t => onionOfEnc nike cipher macS kdfS streamS geom i (W.req (⟨D.keys, D.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd
        D.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names W (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        names W (km, seed, D)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names W (iv, km, he, seed, D) default)) (D.c.pos : ℕ) t
        (Util.Bytes.ofVector u)) (congrArg Util.Bytes.ofVector htag)).trans
      (((onion_streamKey nike cipher macS kdfS streamS geom i (W.req (⟨D.keys, D.c⟩ : ForwardCh
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o) (W.rnd D.o)
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D) (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS streamS geom hvalid hmactag
          h16 names W (km, seed, D)) default)).toArray 0) _ _ (D.c.pos : ℕ) _ _ hjp hne hK
          hpl').1).trans
        (congrArg (fun V => onionOfStream nike cipher macS kdfS streamS geom i (W.req (⟨D.keys,
            D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1)
            D.o) (W.rnd D.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D) (forwardKeys0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W (km, seed, D)) default)).toArray 0) (forwardKeys0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W (km, seed, D)) default)) (D.c.pos : ℕ) V
          (Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              W (km, seed, D) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))
              (Util.Bytes.ofVector u)) hKS))
  have hoa : (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).rest (iv,
      km, he, seed, D) u
      = (if drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names W) D
          < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names W) D).size then
        A.guess D.st (onionOfStream nike cipher macS kdfS streamS geom 0 (W.req (⟨D.keys, D.c⟩ :
            ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names D.k.1) D.o)
            (W.rnd D.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D) (forwardKeys0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W (km, seed, D)) default)).toArray 0) (forwardKeys0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W (km, seed, D)) default)) D.c.pos
          (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))
              (Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W (km, seed, D) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))
              (Util.Bytes.ofVector u))
      else pure false) :=
    congrArg (fun on => if drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names W) D
      < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names W) D).size then A.guess D.st on
      else pure false) (chainS 0 rfl)
  have hpatchS : (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).patch
      (iv, km, he, seed, D) u
      = W.patch (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names D.k.1) D.o (onionOfStream nike cipher macS kdfS streamS geom D.c.pos (W.req
          (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          D.k.1) D.o) (W.rnd D.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names D)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names W (km, seed, D)) default)).toArray 0) (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names W (strPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names W (km, seed, D)) default)) D.c.pos
        (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))
            (Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
            names W (km, seed, D) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))
            (Util.Bytes.ofVector u)) :=
    congrArg (W.patch (⟨D.keys, D.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names D.k.1) D.o) (chainS (D.c.pos : ℕ)
      (peels_hopKeysWith nike cipher kdfS streamS geom _ _ _ (restKeys (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names W (iv, km, he, seed, D) default).1 default)
        (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (km, seed, D)) default).1
            default) rfl _ _ (le_refl _)))
  have key2 : ∀ (H H' : (𝒮).Header)
      (step step' : (𝒮).Onion → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) →
          Option (𝒮).Step)
      (rep rep' : (𝒮).Msg → (𝒮).Onion → Vector UInt8 (geom.payloadTagLength +
          geom.forwardPayloadLength) → Option ((𝒮).Name × (𝒮).Onion))
      (proc : Role → (𝒮).Onion → Option (𝒮).Step)
      (reply : Role → (𝒮).Msg → (𝒮).Onion → Option ((𝒮).Name × (𝒮).Onion))
      (pl pl' : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) (patch patch' :
          Protocols.RSOR.Patch 𝒮)
      (oa oa' : OracleComp (Protocols.RSOR.oracleSpec 𝒮) Bool) (log : Protocols.RSOR.Log 𝒮),
      H = H' → step = step' → rep = rep' → pl = pl' → patch = patch' → oa = oa' →
      (simulateQ (Protocols.RSOR.withDec (S := 𝒮) Role.relay H (fun o => o.2) step rep proc reply
          (fun y => if y = u then pl else v) patch) oa).run' log
        = (simulateQ (Protocols.RSOR.withDec (S := 𝒮) Role.relay H' (fun o => o.2) step' rep'
          proc reply (fun y => if y = u then pl' else v) patch') oa').run' log := by
    rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    rfl
  exact key2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhdr hstep hrep hpl hpatchS hoa

set_option maxHeartbeats 4000000 in
/-- **The keystream step for world 0 of TLU→.** Its payload game with the ideal cipher is the
real experiment of the keystream generator for `forwardStreamAdv`. -/
theorem payExp_false_evalDistEq_prg (names : Role → Name) (W : FwdWorld nike cipher macS kdfS
    streamS geom hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).exp cipher false
      =ᵈ PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
        (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) := by
  have hb : ∀ {α β : Type},
      Function.Bijective (Function.uncurry fun (a : α) (b : β) => (a, b)) :=
    fun {_ _} => Function.bijective_id
  have of_eq : ∀ {a b : ProbComp Bool}, a = b → a =ᵈ b := fun h => h ▸ EvalDistEq.rfl
  have h0 : (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).exp cipher
      false
      = ($ᵗ (Vector UInt8 48)) >>= fun _ => ($ᵗ (Vector UInt8 16)) >>= fun iv =>
        ($ᵗ (Vector UInt8 32)) >>= fun km => ($ᵗ (Vector UInt8 32)) >>= fun he =>
        ($ᵗ (Vector UInt8 32)) >>= fun seed => forwardDraw nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names W A >>= fun D =>
        ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) >>= fun u => ($ᵗ
            (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) >>= fun v =>
          payIdealRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A (iv, km, he,
              seed, D) u v := by
    unfold Protocols.RSOR.PayloadGame.exp payIdealRun
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine bind_congr fun kp => bind_congr fun iv => ?_
    show ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).draw iv >>=
        fun x => _) = _
    unfold forwardPay
    simp only [bind_assoc, pure_bind]
  rw [h0]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  unfold PRGScheme.prgRealExperiment forwardStreamAdv
  refine EvalDistEq.trans ?_ (evalDistEq_pair_of_bijective
    (g := fun (he : Vector UInt8 32) (iv : Vector UInt8 16) => (he, iv)) hb _)
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun he => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun iv => EvalDistEq.bind_right _ fun km =>
    EvalDistEq.bind_right _ fun seed => EvalDistEq.bind_right _ fun D =>
    EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun v => of_eq ?_
  exact strRun_eq nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A iv km he seed D u
      v

/-- **World 0 of TLU→ after its MAC step, down to a uniform keystream.** It differs from world
0 played from a uniform header keystream, an ideal payload cipher and one header by the cipher's
one-query advantage, the keystream generator's advantage, and the chance of a draw that is not
good. -/
theorem forward_only_sub_stream_le (names : Role → Name) (W : FwdWorld nike cipher macS kdfS
    streamS geom hvalid hmactag h16 names) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names W) _
          W.draw (forwardView nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) A
          (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W))}[b =
              true]).toReal
      - (Pr{let b ← (PRGScheme.prgIdealExperiment
          (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A))}[b =
              true]).toReal|
    ≤ (Pr{let z ← (payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A)}[¬
        payGood nike cipher macS kdfS streamS geom hvalid hmactag h16 names W z.2]).toReal
      + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).adv
                true)}[b
                = true]).toReal
          - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).adv
                false)}[b = true]).toReal|
      + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
            (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A))}[b =
                true]).toReal
          - (Pr{let b ← (PRGScheme.prgIdealExperiment
            (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A))}[b =
                true]).toReal| := by
  have h1 := forward_only_sub_ideal_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      W A
  rw [(payExp_false_evalDistEq_prg nike cipher macS kdfS streamS geom hvalid hmactag h16 names W
      A).prEvent_eq (fun b => b = true)] at h1
  exact (abs_sub_le _ _ _).trans (add_le_add h1 le_rfl)

/-- **World 0 of TLU→ for NIKE Sphinx, down to its draws.** World 0 differs from the game played
from a uniform header keystream at the honest relay, an ideal payload cipher there and the relay
answering the adversary's onion under one header, by at most: the advantage of `forwardAdv` in
the key game; a forgery against the MAC; the one-query advantage against the payload cipher;
the keystream generator's advantage; and the chances of three events on draws: the onion cannot
be built, the bytes under the relay's tag do not have a header's length, and a draw is not good
for the payload step. -/
theorem forward_world0_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let b ← (PRGScheme.prgIdealExperiment
          (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b =
              true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        A)}[forwardBad nike cipher macS kdfS streamS geom hvalid hmactag h16 D]).toReal
      + keyAdvantage cipher macS kdfS streamS geom (forwardAdv nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) A)
      + ((Pr{let b ← (Primitives.MAC.forgeExp macS
            (macForge nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                    macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
                    streamS geom hvalid hmactag h16 names)) _
              (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).draw A (forwardMsg
                  nike cipher macS kdfS streamS geom
                  hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
                  h16 names))
              (forwardViewT nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[b =
                  true]).toReal
        + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ (fwd0 nike cipher macS kdfS
                streamS geom hvalid hmactag h16 names).draw
            A)}[¬ (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x).size =
                (2 + nike.publicKeySize + geom.routingInfoLength)]).toReal)
      + ((Pr{let z ← (payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[¬
          payGood nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) z.2]).toReal
        + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
              (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names) A).adv
                  true)}[b = true]).toReal
            - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
              (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names) A).adv
                  false)}[b = true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
              (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b
                  = true]).toReal
            - (Pr{let b ← (PRGScheme.prgIdealExperiment
              (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b
                  = true]).toReal|) := by
  have h1 := play_false_sub_keyGame_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h2 : |(Pr{let x ← (keyGame cipher macS kdfS streamS geom
          (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) A) true)}[x =
              true]).toReal
      - (Pr{let x ← (keyGame cipher macS kdfS streamS geom
          (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) A) false)}[x =
              true]).toReal|
      = keyAdvantage cipher macS kdfS streamS geom (forwardAdv nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) A) := rfl
  have h3 := forward_ideal_sub_only_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A
  have h4 := forward_only_sub_stream_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      A
  have t1 := abs_sub_le
    (Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
    (Pr{let x ← (keyGame cipher macS kdfS streamS geom
      (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A) true)}[x =
          true]).toReal
    (Pr{let b ← (PRGScheme.prgIdealExperiment (forwardStreamAdv nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        A))}[b = true]).toReal
  have t2 := abs_sub_le
    (Pr{let x ← (keyGame cipher macS kdfS streamS geom
      (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A) true)}[x =
          true]).toReal
    (Pr{let x ← (keyGame cipher macS kdfS streamS geom
      (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A) false)}[x =
          true]).toReal
    (Pr{let b ← (PRGScheme.prgIdealExperiment (forwardStreamAdv nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        A))}[b = true]).toReal
  have t3 := abs_sub_le
    (Pr{let x ← (keyGame cipher macS kdfS streamS geom
      (forwardAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A) false)}[x =
          true]).toReal
    (Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names)) _
      (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).draw (forwardView nike
          cipher macS kdfS streamS geom hvalid hmactag
          h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)) A
      (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names)))}[b = true]).toReal
    (Pr{let b ← (PRGScheme.prgIdealExperiment (forwardStreamAdv nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        A))}[b = true]).toReal
  linarith

/-! ## World 1: the replacement onion -/

/-- What the challenger draws in world 1: the randomness of the adversary's own onion, and the
replacement's message, receiver and randomness. -/
def shortDraw : ProbComp (RSOR.Randomness nike geom × Msg geom × Name
    × RSOR.Randomness nike geom) := do
  let r ← $ᵗ (RSOR.Randomness nike geom)
  let m ← $ᵗ (Msg geom)
  let n ← $ᵗ Name
  let r' ← $ᵗ (RSOR.Randomness nike geom)
  return (r, m, n, r')

/-- World 1: the replacement that ends at the honest relay, and the relay patched around the
replacement's layer there. The keys replaced are those of the forward path up to the relay. -/
def fwd1 (names : Role → Name) : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag h16
    names where
  Oth := RSOR.Randomness nike geom × Msg geom × Name × RSOR.Randomness nike geom
  draw := shortDraw nike geom
  req ch o := ch.c.short o.2.1 o.2.2.1
  rnd o := o.2.2.2
  patch ch o mine := ch.c.patch o.1 mine
  hops ch := RSOR.path nike (ch.c.req.fwd.take (ch.c.pos + 1)) []
  size_eq ch o := (RSOR.path_size nike _ _).trans (RSOR.path_size nike _ _).symm
  pos_lt ch := lt_of_lt_of_eq
    (show (ch.c.pos : ℕ) < (List.take ((ch.c.pos : ℕ) + 1) ch.c.req.fwd.hops).length by
      rw [List.length_take]
      exact lt_min (Nat.lt_succ_self _) ch.c.pos.isLt)
    (RSOR.path_size nike (ch.c.req.fwd.take (ch.c.pos + 1)) []).symm

end Forward

end Cryptlib.Protocols.Sphinx.NIKESphinx
