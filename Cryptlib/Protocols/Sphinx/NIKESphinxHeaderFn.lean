/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxRSOR
import Cryptlib.Protocols.Sphinx.KEMSphinxHeaderFn

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.KEMSphinx (padAt)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Util.Bytes (ofVector)

/-! # A NIKE Sphinx packet from each hop's group element and keys

`newNIKEPacket` derives every hop's keys from the sender's secret. A security proof replaces one
hop's keys, and with them its blinding factor and so the group elements of the hops after it.
`nikePktFn` is the packet as a function of what each hop is given: its group element, its header
keystream, its tagging function and its payload encryption. -/

/-- The group element each hop receives: the sender's public key, blinded by the factors of the
hops in front. -/
def groupElem (nike : NIKE) (c : nike.PrivateKey) (keys : Array HopKeys) : ℕ → ByteArray
  | 0 => ofVector (nike.encodePublicKey (nike.derivePublicKey c))
  | i + 1 => nikeBlind nike (groupElem nike c keys i) (keys[i]!).blindingFactor

open Cryptlib.Primitives.KDF (KDF) in
/-- **The hops' keys with hop `j`'s replaced by `t`**: the keys of the first `n` hops as the
sender derives them, except that hop `j` has the keys `t`, and so the hops after it are blinded
by `t`'s factor. -/
def hopKeysWith (nike : NIKE) (kdfS : KDF) (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ)
    (t : HopKeys) : ℕ → List HopKeys
  | 0 => []
  | n + 1 =>
    let ks := hopKeysWith nike kdfS c hops j t n
    ks ++ [if n = j then t else deriveHopKeys kdfS
      ((ks.map (RSOR.factor nike)).foldl (fun ss f => RSOR.dh nike f ss)
        (RSOR.dh nike c hops[n]!.publicKey))]

open Cryptlib.Primitives.KDF (KDF) in
/-- With hop `j`'s own keys, they are the sender's keys. -/
theorem hopKeysWith_hopKey (nike : NIKE) (kdfS : KDF) (c : nike.PrivateKey)
    (hops : Array PathHop) (j n : ℕ) :
    hopKeysWith nike kdfS c hops j (RSOR.hopKey nike kdfS c hops j) n
      = RSOR.hopKeys nike kdfS c hops n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hopKeysWith, ih, RSOR.hopKeys_succ]
    by_cases h : n = j
    · subst h
      simp only [ite_true]
    · simp only [h, ite_false]
      rfl

theorem toArray_getElem!_of_getElem? {α : Type} [Inhabited α] (l : List α) (j : ℕ) (t : α)
    (h : l[j]? = some t) : l.toArray[j]! = t := by
  simp [getElem!_def, h]

open Cryptlib.Primitives.KDF (KDF) in
theorem hopKeysWith_length (nike : NIKE) (kdfS : KDF) (c : nike.PrivateKey)
    (hops : Array PathHop) (j : ℕ) (t : HopKeys) (n : ℕ) :
    (hopKeysWith nike kdfS c hops j t n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hopKeysWith, List.length_append, ih]; rfl

open Cryptlib.Primitives.KDF (KDF) in
/-- The replaced hop has the replacement. -/
theorem hopKeysWith_getElem (nike : NIKE) (kdfS : KDF) (c : nike.PrivateKey)
    (hops : Array PathHop) (j : ℕ) (t : HopKeys) (n : ℕ) (hj : j < n) :
    (hopKeysWith nike kdfS c hops j t n)[j]? = some t := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [hopKeysWith]
    by_cases h : j < n
    · rw [List.getElem?_append_left (by rw [hopKeysWith_length]; exact h)]
      exact ih h
    · obtain rfl : j = n := by omega
      rw [List.getElem?_append_right (by rw [hopKeysWith_length]), hopKeysWith_length]
      simp

open Cryptlib.Primitives.KDF (KDF) in
/-- The hops in front of the replaced one have the sender's keys. -/
theorem hopKeysWith_take (nike : NIKE) (kdfS : KDF) (c : nike.PrivateKey)
    (hops : Array PathHop) (j : ℕ) (t : HopKeys) (n : ℕ) (hj : j ≤ n) :
    (hopKeysWith nike kdfS c hops j t n).take j = RSOR.hopKeys nike kdfS c hops j := by
  have hle : ∀ m, m ≤ j → hopKeysWith nike kdfS c hops j t m = RSOR.hopKeys nike kdfS c hops m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [hopKeysWith, ih (by omega), RSOR.hopKeys_succ]
      simp only [show m ≠ j by omega, ite_false]
      rfl
  induction n, hj using Nat.le_induction with
  | base =>
    rw [hle j le_rfl]
    exact List.take_of_length_le (by rw [← hle j le_rfl, hopKeysWith_length])
  | succ n hn ih =>
    rw [hopKeysWith, List.take_append_of_le_length (by rw [hopKeysWith_length]; exact hn)]
    exact ih

/-- A group element reads the keys in front of it only. -/
theorem groupElem_congr (nike : NIKE) (c : nike.PrivateKey) (K K' : Array HopKeys) (i : ℕ)
    (h : ∀ n < i, K[n]! = K'[n]!) : groupElem nike c K i = groupElem nike c K' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show nikeBlind nike (groupElem nike c K i) _ = nikeBlind nike (groupElem nike c K' i) _
    rw [ih fun n hn => h n (by omega), h i (by omega)]

open Cryptlib.Primitives.KDF (KDF) in
/-- The element that reaches the replaced hop does not depend on the replacement. -/
theorem groupElem_hopKeysWith (nike : NIKE) (kdfS : KDF) (c : nike.PrivateKey)
    (hops : Array PathHop) (j : ℕ) (t : HopKeys) (n : ℕ) (hj : j ≤ n) :
    groupElem nike c (hopKeysWith nike kdfS c hops j t n).toArray j
      = groupElem nike c (RSOR.hopKeys nike kdfS c hops j).toArray j := by
  refine groupElem_congr nike c _ _ j fun i hi => ?_
  rw [← hopKeysWith_take nike kdfS c hops j t n hj]
  simp [hi]

open Cryptlib.Primitives.KDF (KDF) in
/-- Two replacements with the same blinding factor give the same keys off the replaced hop. -/
theorem hopKeysWith_congr (nike : NIKE) (kdfS : KDF) (c : nike.PrivateKey)
    (hops : Array PathHop) (j : ℕ) (t t' : HopKeys)
    (ht : RSOR.factor nike t = RSOR.factor nike t') (n : ℕ) :
    (hopKeysWith nike kdfS c hops j t n).map (RSOR.factor nike)
        = (hopKeysWith nike kdfS c hops j t' n).map (RSOR.factor nike) ∧
      ∀ i, i ≠ j → (hopKeysWith nike kdfS c hops j t n)[i]?
        = (hopKeysWith nike kdfS c hops j t' n)[i]? := by
  induction n with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hopKeysWith, hopKeysWith, List.map_append, List.map_append, ih1]
      congr 1
      by_cases hn : n = j
      · simp only [hn, ite_true, List.map_cons, List.map_nil, ht]
      · simp only [hn, ite_false]
    · rw [hopKeysWith, hopKeysWith, ih1]
      by_cases hin : i < n
      · rw [List.getElem?_append_left (by rw [hopKeysWith_length]; exact hin),
          List.getElem?_append_left (by rw [hopKeysWith_length]; exact hin)]
        exact ih2 i hi
      · rw [List.getElem?_append_right (by rw [hopKeysWith_length]; omega),
          List.getElem?_append_right (by rw [hopKeysWith_length]; omega), hopKeysWith_length,
          hopKeysWith_length]
        by_cases hin' : i = n
        · subst hin'
          simp only [hi, ite_false]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- The group elements from the first: each blinded by the factor of the hop before. -/
def blindElem (nike : NIKE) (a : ByteArray) (keys : Array HopKeys) : ℕ → ByteArray
  | 0 => a
  | i + 1 => nikeBlind nike (blindElem nike a keys i) (keys[i]!).blindingFactor

/-- The elements from the first read the hops' blinding factors only. -/
theorem blindElem_congr (nike : NIKE) (a : ByteArray) (K K' : Array HopKeys)
    (h : ∀ n : ℕ, (K[n]!).blindingFactor = (K'[n]!).blindingFactor) (i : ℕ) :
    blindElem nike a K i = blindElem nike a K' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show nikeBlind nike (blindElem nike a K i) _ = nikeBlind nike (blindElem nike a K' i) _
    rw [ih, h i]

theorem groupElem_eq_blindElem (nike : NIKE) (c : nike.PrivateKey) (keys : Array HopKeys) (i : ℕ) :
    groupElem nike c keys i = blindElem nike (groupElem nike c keys 0) keys i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show nikeBlind nike (groupElem nike c keys i) _ = nikeBlind nike _ _
    rw [ih]

section HeaderFn

variable (geom : Geometry)

/-- A hop's routing fragment: its commands, the next hop's name and tag before the end of the
path, padded to a hop's length. -/
def nikeFragment (path : Array PathHop) (mac : ByteArray) (i : ℕ) : Except String ByteArray := do
  let frag ← commandsToBytes
    (if i == path.size - 1 then geom.perHopRoutingInfoLength
      else geom.perHopRoutingInfoLength - geom.nextNodeHopLength) (path[i]!).commands
  pure (zeroPadTo geom.perHopRoutingInfoLength
    (if i == path.size - 1 then frag
      else frag ++ (RoutingCommand.nextNodeHop (path[i + 1]!).id (toVec32 mac)).toBytes))

/-- The routing information and tag of the header's layers, built from the last hop back:
after `j` steps, those of the layer for hop `path.size - j`. Each hop enters through its group
element `ge`, its header keystream `ks` and its tagging function `tag`. -/
def nikeHdrTrace (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) : ℕ → Option (ByteArray × ByteArray)
  | 0 => some (if geom.nrHops > path.size then filler else ByteArray.empty, ByteArray.empty)
  | j + 1 =>
    match nikeHdrTrace ks tag ge filler path j with
    | none => none
    | some s =>
      match nikeFragment geom path s.2 (path.size - 1 - j) with
      | .error _ => none
      | .ok frag =>
        some (xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)),
          tag (path.size - 1 - j) (v0AD ++ ge (path.size - 1 - j)
            ++ xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
              (geom.routingInfoLength + geom.perHopRoutingInfoLength
                - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength))
            ++ (if path.size - 1 - j > 0 then padAt geom ks (path.size - 1 - j - 1)
              else ByteArray.empty)))

/-- **The packet, from each hop's group element, keystream, tagging function and payload
encryption.** -/
def nikePktFn (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (payload : ByteArray) : Option ByteArray :=
  if payload.size = geom.forwardPayloadLength then
    (nikeHdrTrace geom ks tag ge filler path path.size).map fun s =>
      v0AD ++ ge 0 ++ s.1 ++ s.2
        ++ (List.range' 0 path.size).foldl (fun b iRev => enc (path.size - 1 - iRev) b)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)
  else none

/-- `nikeHdrTrace` reads the keystreams, tagging functions and group elements of the path's hops
only. -/
theorem nikeHdrTrace_congr (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop)
    (h : ∀ i, i < path.size → ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i) (j : ℕ)
    (hj : j ≤ path.size) :
    nikeHdrTrace geom ks tag ge filler path j = nikeHdrTrace geom ks' tag' ge' filler path j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [nikeHdrTrace, nikeHdrTrace, ih (by omega)]
    simp only [(h (path.size - 1 - j) (by omega)).1, (h (path.size - 1 - j) (by omega)).2.1,
      (h (path.size - 1 - j) (by omega)).2.2,
      KEMSphinx.padAt_congr geom ks ks' (path.size - 1 - j - 1) fun m _ => (h m (by omega)).1]

/-- `nikePktFn` reads what it is given for the path's hops only. -/
theorem nikePktFn_congr (ks ks' : ℕ → ByteArray) (tag tag' enc enc' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (payload : ByteArray)
    (hp : 0 < path.size)
    (h : ∀ i, i < path.size → ks i = ks' i ∧ tag i = tag' i ∧ enc i = enc' i ∧ ge i = ge' i) :
    nikePktFn geom ks tag enc ge filler path payload
      = nikePktFn geom ks' tag' enc' ge' filler path payload := by
  have hf : (List.range' 0 path.size).foldl (fun b iRev => enc (path.size - 1 - iRev) b)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)
      = (List.range' 0 path.size).foldl (fun b iRev => enc' (path.size - 1 - iRev) b)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload) :=
    List.foldl_ext _ _ _ fun b iRev hi => by
      have hlt : iRev < path.size := by simpa using hi
      rw [(h (path.size - 1 - iRev) (by omega)).2.2.1]
  unfold nikePktFn
  rw [nikeHdrTrace_congr geom ks ks' tag tag' ge ge' filler path
    (fun i hi => ⟨(h i hi).1, (h i hi).2.1, (h i hi).2.2.2⟩) _ le_rfl, hf, (h 0 hp).2.2.2]

/-- The first `m` steps of `nikeHdrTrace` read the tagging functions of the last `m` hops
only. -/
theorem nikeHdrTrace_congr_tag (ks : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (m : ℕ)
    (hm : m ≤ path.size) (h : ∀ i, path.size - m ≤ i → i < path.size → tag i = tag' i) :
    nikeHdrTrace geom ks tag ge filler path m = nikeHdrTrace geom ks tag' ge filler path m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nikeHdrTrace, nikeHdrTrace, ih (by omega) fun i hi hlt => h i (by omega) hlt,
      h (path.size - 1 - m) (by omega) (by omega)]

/-- The bytes hop `i`'s tag covers: its version bytes, group element, routing information and
padding. Empty when the header does not build that far. -/
def hdrMsg (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ) : ByteArray :=
  match nikeHdrTrace geom ks tag ge filler path (path.size - 1 - i) with
  | none => .empty
  | some s =>
    match nikeFragment geom path s.2 i with
    | .error _ => .empty
    | .ok frag =>
      v0AD ++ ge i ++ xorBytes (frag ++ s.1) ((ks i).extract 0
          (geom.routingInfoLength + geom.perHopRoutingInfoLength
            - (i + 1) * geom.perHopRoutingInfoLength))
        ++ (if i > 0 then padAt geom ks (i - 1) else ByteArray.empty)

/-- **The header uses a hop's tagging function once**, on `hdrMsg`: with hop `i`'s function
replaced by the constant that returns its tag of those bytes, the header is the same. The bytes
do not depend on hop `i`'s tagging function. -/
theorem nikeHdrTrace_tagAt (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ) (hi : i < path.size)
    (f : ByteArray → ByteArray) (m : ℕ) (hm : m ≤ path.size) :
    nikeHdrTrace geom ks (Function.update tag i f) ge filler path m
      = nikeHdrTrace geom ks (Function.update tag i fun _ =>
          f (hdrMsg geom ks tag ge filler path i)) ge filler path m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nikeHdrTrace, nikeHdrTrace, ih (by omega)]
    by_cases hmi : path.size - 1 - m = i
    · have hpre : nikeHdrTrace geom ks (Function.update tag i fun _ =>
            f (hdrMsg geom ks tag ge filler path i)) ge filler path m
          = nikeHdrTrace geom ks tag ge filler path (path.size - 1 - i) := by
        have hmm : m = path.size - 1 - i := by omega
        rw [← hmm]
        exact nikeHdrTrace_congr_tag geom ks _ _ ge filler path m (by omega) fun n hn _ =>
          Function.update_of_ne (by omega) _ _
      rw [hmi, hpre]
      unfold hdrMsg
      cases nikeHdrTrace geom ks tag ge filler path (path.size - 1 - i) with
      | none => rfl
      | some s =>
        dsimp only
        cases nikeFragment geom path s.2 i with
        | error e => rfl
        | ok frag =>
          dsimp only
          rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hmi, Function.update_of_ne hmi]

/-- The packet uses a hop's tagging function once, on `hdrMsg`. -/
theorem nikePktFn_tagAt (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (payload : ByteArray)
    (i : ℕ) (hi : i < path.size) (f : ByteArray → ByteArray) :
    nikePktFn geom ks (Function.update tag i f) enc ge filler path payload
      = nikePktFn geom ks (Function.update tag i fun _ =>
          f (hdrMsg geom ks tag ge filler path i)) enc ge filler path payload := by
  unfold nikePktFn
  rw [nikeHdrTrace_tagAt geom ks tag ge filler path i hi f _ le_rfl]

/-- The payload after the first `m` encryptions: those of the last `m` hops, innermost first. -/
def encTrace (enc : ℕ → ByteArray → ByteArray) (n : ℕ) (init : ByteArray) (m : ℕ) : ByteArray :=
  (List.range' 0 m).foldl (fun b iRev => enc (n - 1 - iRev) b) init

omit geom in
theorem encTrace_succ (enc : ℕ → ByteArray → ByteArray) (n : ℕ) (init : ByteArray) (m : ℕ) :
    encTrace enc n init (m + 1) = enc (n - 1 - m) (encTrace enc n init m) := by
  unfold encTrace
  rw [List.range'_1_concat, List.foldl_append]
  simp

omit geom in
/-- **A payload is encrypted by a hop once**, on the block the hops after it left: with hop
`j`'s encryption replaced by the constant that returns its encryption of that block, the
payload is the same. The block does not depend on hop `j`'s encryption. -/
theorem encTrace_encAt (enc : ℕ → ByteArray → ByteArray) (n : ℕ) (init : ByteArray) (j : ℕ)
    (hj : j < n) (f : ByteArray → ByteArray) (m : ℕ) (hm : m ≤ n) :
    encTrace (Function.update enc j f) n init m
      = encTrace (Function.update enc j fun _ => f (encTrace enc n init (n - 1 - j))) n init m ∧
      (m ≤ n - 1 - j → encTrace (Function.update enc j f) n init m = encTrace enc n init m) := by
  induction m with
  | zero => exact ⟨rfl, fun _ => rfl⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [encTrace_succ, encTrace_succ, encTrace_succ]
    by_cases hmj : n - 1 - m = j
    · refine ⟨?_, fun h => absurd h (by omega)⟩
      rw [hmj, Function.update_self, Function.update_self, ih2 (by omega)]
      congr 2
      omega
    · rw [Function.update_of_ne hmj, Function.update_of_ne hmj, ih1]
      exact ⟨rfl, fun h => by rw [← ih1, ih2 (by omega)]⟩

/-- The packet uses a hop's payload encryption once, on the block the hops after it left. -/
theorem nikePktFn_encAt (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (payload : ByteArray)
    (j : ℕ) (hj : j < path.size) (f : ByteArray → ByteArray) :
    nikePktFn geom ks tag (Function.update enc j f) ge filler path payload
      = nikePktFn geom ks tag (Function.update enc j fun _ =>
          f (encTrace enc path.size
            ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)
            (path.size - 1 - j))) ge filler path payload := by
  have h := (encTrace_encAt enc path.size
    ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload) j hj f path.size
    le_rfl).1
  unfold encTrace at h
  unfold nikePktFn
  rw [h]
  rfl

end HeaderFn

section Built

open Cryptlib.Protocols.Sphinx.KEMSphinx (keysKs keysTag)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (telescopeElem telescopeSecret)

variable (nike : NIKE) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)

set_option maxHeartbeats 2000000 in
/-- **The header `createHeader` builds is `nikeHdrTrace`'s**, on the group elements and keys of
its blinding chain. -/
theorem createHeader_hdrTrace (clientPrivateKey filler : ByteArray) (path : Array PathHop)
    (hdr : ByteArray) (sprpKeys : Array SPRPKey)
    (h : createHeader nike macS kdfS streamS geom clientPrivateKey filler path
      = .ok (hdr, sprpKeys))
    (targetSk : ℕ → nike.PrivateKey)
    (htarget : ∀ i (_hi : i < path.size), (path[i]!).publicKey
      = ofVector (nike.encodePublicKey (nike.derivePublicKey (targetSk i)))) :
    ∃ (clientSk : nike.PrivateKey) (f : ℕ → nike.PrivateKey) (groupElements : Array ByteArray)
      (keys : Array HopKeys) (s : ByteArray × ByteArray),
      groupElements.size = path.size ∧ keys.size = path.size ∧
      nikeSelfPublicKeyBytes nike clientPrivateKey
        = ofVector (nike.encodePublicKey (nike.derivePublicKey clientSk)) ∧
      (∀ i (_hi : i < path.size),
        groupElements[i]! = ofVector (nike.encodePublicKey (telescopeElem nike clientSk f i).1) ∧
        keys[i]! = deriveHopKeys kdfS
          (ofVector (nike.encodeSharedSecret (telescopeSecret nike clientSk (targetSk i) f i).1)) ∧
        nike.decodePrivateKey (toVecN nike.privateKeySize (keys[i]!).blindingFactor)
          = some (f i)) ∧
      nikeHdrTrace geom (keysKs geom streamS keys) (keysTag macS keys) (fun i => groupElements[i]!)
          filler path path.size
        = some s ∧
      hdr = v0AD ++ groupElements[0]! ++ s.1 ++ s.2 ∧
      sprpKeys = Array.ofFn (fun i : Fin path.size =>
        { key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV }) := by
  obtain ⟨-, -, -, clientSk, f, groupElements, keys, riKeyStream, riPadding, s, hgs, hks, -, -,
    hself, hchain, hcont, hs0, hstep, hhdr, hsprp⟩ :=
    createHeader_unfold nike macS kdfS streamS geom clientPrivateKey filler path hdr sprpKeys h
      targetSk htarget
  have hpad : ∀ i, i < path.size → riPadding[i]! = padAt geom (keysKs geom streamS keys) i := by
    intro i
    induction i with
    | zero =>
      intro hi
      have := (hcont 0 hi).2
      simp only [gt_iff_lt, lt_self_iff_false, ↓reduceIte] at this
      rw [this]
      rfl
    | succ i ih =>
      intro hi
      have := (hcont (i + 1) hi).2
      simp only [gt_iff_lt, Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel] at this
      rw [this, ih (by omega)]
      rfl
  have htr : ∀ j, j ≤ path.size →
      nikeHdrTrace geom (keysKs geom streamS keys) (keysTag macS keys) (fun i => groupElements[i]!)
          filler path j
        = some (s j) := by
    intro j
    induction j with
    | zero => intro _; rw [hs0]; rfl
    | succ j ih =>
      intro hj
      obtain ⟨frag, hfrag, h1, h2⟩ := hstep j (by omega)
      rw [nikeHdrTrace, ih (by omega)]
      dsimp only
      have hF : nikeFragment geom path (s j).2 (path.size - 1 - j)
          = .ok (zeroPadTo geom.perHopRoutingInfoLength
            (if (path.size - 1 - j) == path.size - 1 then frag
              else frag ++ (RoutingCommand.nextNodeHop (path[path.size - 1 - j + 1]!).id
                (toVec32 (s j).2)).toBytes)) := by
        unfold nikeFragment
        rw [hfrag]
        rfl
      rw [hF]
      dsimp only
      rw [(hcont (path.size - 1 - j) (by omega)).1] at h1
      have h1' : (s (j + 1)).1 = xorBytes (zeroPadTo geom.perHopRoutingInfoLength
            (if (path.size - 1 - j) == path.size - 1 then frag
              else frag ++ (RoutingCommand.nextNodeHop (path[path.size - 1 - j + 1]!).id
                (toVec32 (s j).2)).toBytes) ++ (s j).1)
          ((keysKs geom streamS keys (path.size - 1 - j)).extract 0
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)) := h1
      rw [← h1']
      congr 1
      refine Prod.ext rfl ?_
      rw [h2]
      by_cases hp : path.size - 1 - j > 0
      · simp only [hp, ↓reduceIte]
        rw [hpad _ (by omega)]
        rfl
      · simp only [hp, ↓reduceIte]
        rfl
  exact ⟨clientSk, f, groupElements, keys, s path.size, hgs, hks, hself, hchain, htr _ le_rfl,
    hhdr, hsprp⟩

open Cryptlib.Protocols.Sphinx.KEMSphinx (keysEnc) in
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher) in
set_option maxHeartbeats 2000000 in
/-- **A packet `newNIKEPacket` builds is `nikePktFn`'s**, on the group elements and keys of its
blinding chain: it uses a hop's keys through the hop's header keystream, its MAC and one
encryption of the payload, and through the blinding of the elements after it. -/
theorem newNIKEPacket_pktFn (cipher : WideBlockCipher) (clientPrivateKey filler : ByteArray)
    (path : Array PathHop) (payload pkt : ByteArray)
    (h : newNIKEPacket nike cipher macS kdfS streamS geom clientPrivateKey filler path payload
      = .ok pkt)
    (targetSk : ℕ → nike.PrivateKey)
    (htarget : ∀ i (_hi : i < path.size), (path[i]!).publicKey
      = ofVector (nike.encodePublicKey (nike.derivePublicKey (targetSk i)))) :
    ∃ (clientSk : nike.PrivateKey) (f : ℕ → nike.PrivateKey) (groupElements : Array ByteArray)
      (keys : Array HopKeys),
      groupElements.size = path.size ∧ keys.size = path.size ∧
      nikeSelfPublicKeyBytes nike clientPrivateKey
        = ofVector (nike.encodePublicKey (nike.derivePublicKey clientSk)) ∧
      (∀ i (_hi : i < path.size),
        groupElements[i]! = ofVector (nike.encodePublicKey (telescopeElem nike clientSk f i).1) ∧
        keys[i]! = deriveHopKeys kdfS
          (ofVector (nike.encodeSharedSecret (telescopeSecret nike clientSk (targetSk i) f i).1)) ∧
        nike.decodePrivateKey (toVecN nike.privateKeySize (keys[i]!).blindingFactor)
          = some (f i)) ∧
      nikePktFn geom (keysKs geom streamS keys) (keysTag macS keys) (keysEnc cipher keys) (fun i =>
          groupElements[i]!) filler
        path payload = some pkt := by
  have hp : payload.size = geom.forwardPayloadLength :=
    (newNIKEPacket_unfold nike cipher macS kdfS streamS geom _ _ _ _ _ h).1
  unfold newNIKEPacket at h
  dsimp only at h
  simp only [hp, ne_eq, not_true_eq_false, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, pure_bind] at h
  cases hc : createHeader nike macS kdfS streamS geom clientPrivateKey filler path with
  | error e =>
    rw [hc] at h
    cases h
  | ok x =>
    obtain ⟨hdr, sprp⟩ := x
    rw [hc] at h
    obtain ⟨clientSk, f, ge, keys, s, hgs, hks, hself, hchain, htr, rfl, rfl⟩ :=
      createHeader_hdrTrace nike macS kdfS streamS geom clientPrivateKey filler path hdr sprp hc
        targetSk htarget
    refine ⟨clientSk, f, ge, keys, hgs, hks, hself, hchain, ?_⟩
    unfold nikePktFn
    simp only [hp, ↓reduceIte, htr, Option.map_some]
    injection h with h
    subst h
    congr 2
    rw [Array.size_ofFn]
    refine List.foldl_ext _ _ _ fun b iRev hi => ?_
    have hlt : iRev < path.size := by simpa using hi
    have hi' : path.size - 1 - iRev < path.size := by omega
    simp only [keysEnc]
    rw [getElem!_pos (Array.ofFn _) _ (by simpa using hi')]
    simp only [Array.getElem_ofFn]

end Built

end Cryptlib.Protocols.Sphinx.NIKESphinx
