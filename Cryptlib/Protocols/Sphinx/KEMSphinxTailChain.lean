/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTailOracle

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

/-! # The honest relay at any position

`newKEMPacket_unwrapKEM_tail` handles one hop. Applied once for each hop up to and including the
honest relay, it shows that what the honest relay forwards is a fresh packet on the rest of the
path whose filler is the original filler followed by one block for each hop that has processed
the packet. Each of those blocks is masked by a different block of the honest relay's header
keystream: together, the last blocks of that keystream. -/

section Bytes

/-- A string of zero bytes. -/
def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

@[simp] theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := Array.size_replicate

theorem xorBytes_zeroBytes (a : ByteArray) (n : Nat) : xorBytes a (zeroBytes n) = a := by
  apply ByteArray.ext_getElem
  · simp
  · intro i h1 h2
    rw [xorBytes_getElem a _ i h2]
    split
    · simp [zeroBytes, ByteArray.getElem_eq_getElem_data]
    · simp

theorem zeroBytes_xorBytes (a : ByteArray) : xorBytes (zeroBytes a.size) a = a := by
  rw [xorBytes_comm_of_size_eq _ _ (by simp), xorBytes_zeroBytes]

/-- Adjacent slices join. -/
theorem extract_adjacent (b : ByteArray) (p q r : Nat) (hpq : p ≤ q) (hqr : q ≤ r)
    (hr : r ≤ b.size) : b.extract p q ++ b.extract q r = b.extract p r := by
  apply ByteArray.ext_getElem
  · simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  · intro i h1 h2
    simp only [ByteArray.size_append, ByteArray.size_extract] at h1
    by_cases hi : i < q - p
    · rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_extract]; omega),
        ByteArray.getElem_extract, ByteArray.getElem_extract]
    · rw [ByteArray.getElem_append_right (by simp only [ByteArray.size_extract]; omega),
        ByteArray.getElem_extract, ByteArray.getElem_extract]
      congr 1
      simp only [ByteArray.size_extract]
      omega

/-- `xorBytes` of two concatenations whose parts line up. -/
theorem xorBytes_append (a b c d : ByteArray) (hac : a.size = c.size) :
    xorBytes (a ++ b) (c ++ d) = xorBytes a c ++ xorBytes b d := by
  apply ByteArray.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < a.size + b.size := by simpa using h1
    rw [xorBytes_getElem (a ++ b) (c ++ d) i (by simpa using hi)]
    by_cases hia : i < a.size
    · rw [ByteArray.getElem_append_left hia, dif_pos (by simp; omega),
        ByteArray.getElem_append_left (by omega : i < c.size),
        ByteArray.getElem_append_left (by simpa using hia : i < (xorBytes a c).size),
        xorBytes_getElem a c i hia, dif_pos (by omega)]
    · rw [ByteArray.getElem_append_right (by omega : a.size ≤ i),
        ByteArray.getElem_append_right (by simp; omega : (xorBytes a c).size ≤ i),
        xorBytes_getElem b d _ (by simp; omega)]
      simp only [size_xorBytes]
      by_cases hid : i - a.size < d.size
      · rw [dif_pos (by simp; omega), dif_pos hid, ByteArray.getElem_append_right (by omega)]
        congr 2
        omega
      · rw [dif_neg (by simp; omega), dif_neg hid]

end Bytes

section Pads

variable (geom : Geometry)

/-- The length of a header keystream. -/
abbrev ksLen : Nat := geom.routingInfoLength + geom.perHopRoutingInfoLength

/-- Block `i` from the end of a header keystream. -/
def ksBlock (ks : ByteArray) (i : Nat) : ByteArray :=
  ks.extract (ksLen geom - (i + 1) * geom.perHopRoutingInfoLength)
    (ksLen geom - i * geom.perHopRoutingInfoLength)

theorem ksBlock_size (ks : ByteArray) (hks : ks.size = ksLen geom) (i : Nat)
    (h : (i + 1) * geom.perHopRoutingInfoLength ≤ ksLen geom) :
    (ksBlock geom ks i).size = geom.perHopRoutingInfoLength := by
  have hsm : (i + 1) * geom.perHopRoutingInfoLength
      = i * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  unfold ksBlock
  rw [ByteArray.size_extract, hks]
  omega

theorem zeroBytes_extract (n p q : Nat) : (zeroBytes n).extract p q = zeroBytes (min q n - p) := by
  apply ByteArray.ext_getElem
  · simp [ByteArray.size_extract]
  · intro i h1 h2
    rw [ByteArray.getElem_extract]
    simp [zeroBytes, ByteArray.getElem_eq_getElem_data]

/-- The XOR over hops `0` to `i` of block `k` of hop `k`'s keystream. -/
def padS (ksF : Nat → ByteArray) : Nat → ByteArray
  | 0 => ksBlock geom (ksF 0) 0
  | i + 1 => xorBytes (ksBlock geom (ksF (i + 1)) (i + 1)) (padS ksF i)

theorem padS_size (ksF : Nat → ByteArray) (hks : ∀ k, (ksF k).size = ksLen geom)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops) (i : Nat)
    (hi : i ≤ geom.nrHops) : (padS geom ksF i).size = geom.perHopRoutingInfoLength := by
  cases i with
  | zero => exact ksBlock_size geom _ (hks 0) 0 (block_le geom hrouting 0 hi)
  | succ i =>
    show (xorBytes _ _).size = _
    rw [size_xorBytes]
    exact ksBlock_size geom _ (hks _) _ (block_le geom hrouting _ hi)

theorem padS_congr (ksF ksF' : Nat → ByteArray) (i : Nat) (h : ∀ k, k ≤ i → ksF k = ksF' k) :
    padS geom ksF i = padS geom ksF' i := by
  induction i with
  | zero => show ksBlock geom (ksF 0) 0 = ksBlock geom (ksF' 0) 0; rw [h 0 (Nat.le_refl 0)]
  | succ i ih =>
    show xorBytes (ksBlock geom (ksF (i + 1)) (i + 1)) (padS geom ksF i)
      = xorBytes (ksBlock geom (ksF' (i + 1)) (i + 1)) (padS geom ksF' i)
    rw [h (i + 1) (Nat.le_refl _), ih fun k hk => h k (by omega)]

theorem update_size (ksF : Nat → ByteArray) (L : Nat) (hks : ∀ k, (ksF k).size = L) (h : Nat)
    (v : ByteArray) (hv : v.size = L) (k : Nat) : (Function.update ksF h v k).size = L := by
  rw [Function.update_apply]
  split
  · exact hv
  · exact hks k

/-- One hop's keystream enters `padS` through one block, XORed in. -/
theorem padS_update (ksF : Nat → ByteArray) (hks : ∀ k, (ksF k).size = ksLen geom)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (h i : Nat) (hhi : h ≤ i) (hi : i ≤ geom.nrHops) (u : ByteArray) (hu : u.size = ksLen geom) :
    padS geom (Function.update ksF h u) i
      = xorBytes (ksBlock geom u h)
          (padS geom (Function.update ksF h (zeroBytes (ksLen geom))) i) := by
  have hbu : (ksBlock geom u h).size = geom.perHopRoutingInfoLength :=
    ksBlock_size geom u hu h (block_le geom hrouting h (by omega))
  induction i with
  | zero =>
    obtain rfl : h = 0 := by omega
    show ksBlock geom (Function.update ksF 0 u 0) 0
      = xorBytes (ksBlock geom u 0)
          (ksBlock geom (Function.update ksF 0 (zeroBytes (ksLen geom)) 0) 0)
    rw [Function.update_self, Function.update_self]
    unfold ksBlock
    rw [zeroBytes_extract, xorBytes_zeroBytes]
  | succ i ih =>
    show xorBytes (ksBlock geom (Function.update ksF h u (i + 1)) (i + 1))
        (padS geom (Function.update ksF h u) i)
      = xorBytes (ksBlock geom u h)
          (xorBytes (ksBlock geom (Function.update ksF h (zeroBytes (ksLen geom)) (i + 1)) (i + 1))
            (padS geom (Function.update ksF h (zeroBytes (ksLen geom))) i))
    by_cases hh : h = i + 1
    · subst hh
      rw [Function.update_self, Function.update_self,
        padS_congr geom (Function.update ksF (i + 1) u) ksF i fun k hk =>
          Function.update_of_ne (by omega) _ _,
        padS_congr geom (Function.update ksF (i + 1) (zeroBytes (ksLen geom))) ksF i fun k hk =>
          Function.update_of_ne (by omega) _ _]
      have hz : ksBlock geom (zeroBytes (ksLen geom)) (i + 1)
          = zeroBytes (padS geom ksF i).size := by
        have h1 := ksBlock_size geom (zeroBytes (ksLen geom)) (by simp) (i + 1)
          (block_le geom hrouting (i + 1) hi)
        unfold ksBlock at h1 ⊢
        rw [zeroBytes_extract] at h1 ⊢
        rw [zeroBytes_size] at h1
        rw [h1, padS_size geom ksF hks hrouting i (by omega)]
      rw [hz, zeroBytes_xorBytes]
    · have hne : (i + 1) ≠ h := fun e => hh e.symm
      rw [Function.update_of_ne hne, Function.update_of_ne hne, ih (by omega) (by omega)]
      exact xorBytes_left_comm _ _ _
        (by rw [hbu, ksBlock_size geom _ (hks _) _ (block_le geom hrouting _ hi)])
        (by rw [hbu, padS_size geom _ (update_size ksF _ hks h _ (by simp)) hrouting i
          (by omega)])

theorem update_shift (ksF : Nat → ByteArray) (h t : Nat) (hth : t ≤ h) (u : ByteArray) :
    (fun m => Function.update ksF h u (t + m))
      = Function.update (fun m => ksF (t + m)) (h - t) u := by
  funext m
  by_cases hm : m = h - t
  · rw [Function.update_apply, Function.update_apply, if_pos (by omega), if_pos hm]
  · rw [Function.update_apply, Function.update_apply, if_neg (by omega), if_neg hm]

/-- The blocks that `k` successive hops, starting with hop `t`, append to the filler. -/
def padsS (ksF : Nat → ByteArray) (n : Nat) : Nat → Nat → ByteArray
  | 0, _ => ByteArray.empty
  | k + 1, t => padS geom (fun m => ksF (t + m)) (n - 1 - t) ++ padsS ksF n k (t + 1)

/-- **The last of `k` hops enters the blocks they append through the last `k` blocks of its
keystream, XORed in.** -/
theorem padsS_update (ksF : Nat → ByteArray) (hks : ∀ k, (ksF k).size = ksLen geom)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (n : Nat) (hn : n ≤ geom.nrHops) (h : Nat) (hhn : h < n) (u : ByteArray)
    (hu : u.size = ksLen geom) (k t : Nat) (hk : h + 1 = t + (k + 1)) :
    padsS geom (Function.update ksF h u) n (k + 1) t
      = xorBytes (u.extract (ksLen geom - (k + 1) * geom.perHopRoutingInfoLength) (ksLen geom))
          (padsS geom (Function.update ksF h (zeroBytes (ksLen geom))) n (k + 1) t) := by
  induction k generalizing t with
  | zero =>
    obtain rfl : h = t := by omega
    show padS geom (fun m => Function.update ksF h u (h + m)) (n - 1 - h) ++ ByteArray.empty
      = xorBytes _ (padS geom (fun m => Function.update ksF h (zeroBytes (ksLen geom)) (h + m))
          (n - 1 - h) ++ ByteArray.empty)
    rw [ByteArray.append_empty, ByteArray.append_empty, update_shift ksF h h (Nat.le_refl _),
      update_shift ksF h h (Nat.le_refl _), Nat.sub_self,
      padS_update geom (fun m => ksF (h + m)) (fun k => hks _) hrouting 0 (n - 1 - h)
        (Nat.zero_le _) (by omega) u hu]
    unfold ksBlock
    simp only [Nat.zero_add, Nat.zero_mul, Nat.sub_zero]
  | succ k ih =>
    show padS geom (fun m => Function.update ksF h u (t + m)) (n - 1 - t)
        ++ padsS geom (Function.update ksF h u) n (k + 1) (t + 1)
      = xorBytes _ (padS geom (fun m => Function.update ksF h (zeroBytes (ksLen geom)) (t + m))
          (n - 1 - t) ++ padsS geom (Function.update ksF h (zeroBytes (ksLen geom))) n (k + 1)
            (t + 1))
    have hsm : (k + 1 + 1) * geom.perHopRoutingInfoLength
        = (k + 1) * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength :=
      Nat.succ_mul _ _
    have hle : (k + 1 + 1) * geom.perHopRoutingInfoLength ≤ ksLen geom :=
      block_le geom hrouting (k + 1) (by omega)
    rw [ih (t + 1) (by omega), update_shift ksF h t (by omega), update_shift ksF h t (by omega),
      padS_update geom (fun m => ksF (t + m)) (fun k => hks _) hrouting (h - t) (n - 1 - t)
        (by omega) (by omega) u hu,
      ← xorBytes_append _ _ _ _ (by
        rw [ksBlock_size geom u hu _ (block_le geom hrouting _ (by omega)),
          padS_size geom _ (update_size _ _ (fun k => hks _) _ _ (by simp)) hrouting _
            (by omega)])]
    congr 1
    have hht : h - t = k + 1 := by omega
    unfold ksBlock
    rw [hht]
    exact extract_adjacent u _ _ _ (by omega) (by omega) (by omega)

end Pads

section ChainForward

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- Hop `m`'s header keystream on a path. -/
def ksReal (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (m : Nat) : ByteArray :=
  headerKeystream streamS geom (kemHopKeys kem kdfS path seeds m)

theorem ksReal_size (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (m : Nat) :
    (ksReal kem kdfS streamS geom path seeds m).size = ksLen geom :=
  streamS.keystream_size _ _ _

theorem getElem!_extract_one {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    (a.extract 1 a.size)[i]! = a[i + 1]! := by
  by_cases h : i + 1 < a.size
  · rw [getElem!_extract_from a 1 i (by omega), Nat.add_comm]
  · rw [getElem!_neg (a.extract 1 a.size) i (by simp; omega), getElem!_neg a (i + 1) h]

theorem extract_one_extract {α : Type} (a : Array α) (k : Nat) :
    (a.extract 1 a.size).extract k (a.extract 1 a.size).size = a.extract (k + 1) a.size := by
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp only [Array.getElem_extract]
    congr 1
    omega

theorem ksReal_rest (path : Array PathHop) (seeds : Array (Vector UInt8 32)) :
    ksReal kem kdfS streamS geom (path.extract 1 path.size) (seeds.extract 1 seeds.size)
      = fun m => ksReal kem kdfS streamS geom path seeds (m + 1) := by
  funext m
  unfold ksReal kemHopKeys
  rw [getElem!_extract_one, getElem!_extract_one]

theorem tailPad_eq_padS (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (i : Nat) :
    tailPad kem kdfS streamS geom path seeds i
      = padS geom (ksReal kem kdfS streamS geom path seeds) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show xorBytes (tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds (i + 1)) (i + 1))
        (tailPad kem kdfS streamS geom path seeds i) = _
    rw [ih]
    rfl

theorem padsS_shift (ksF : Nat → ByteArray) (n k t : Nat) :
    padsS geom (fun m => ksF (m + 1)) (n - 1) k t = padsS geom ksF n k (t + 1) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    show padS geom (fun m => ksF (t + m + 1)) (n - 1 - 1 - t)
        ++ padsS geom (fun m => ksF (m + 1)) (n - 1) k (t + 1)
      = padS geom (fun m => ksF (t + 1 + m)) (n - 1 - (t + 1))
        ++ padsS geom ksF n k (t + 1 + 1)
    have e1 : (fun m => ksF (t + m + 1)) = fun m => ksF (t + 1 + m) :=
      funext fun m => by congr 1; omega
    have e2 : n - 1 - 1 - t = n - 1 - (t + 1) := by omega
    rw [ih, e1, e2]

/-- Have each private key in turn process the packet, and return what the last one forwards. -/
def chainForward (sks : List ByteArray) (pkt : ByteArray) : Option ByteArray :=
  match sks with
  | [] => some pkt
  | sk :: rest =>
    match unwrapKEM kem cipher macS kdfS streamS geom sk pkt with
    | .ok (_, _, _, some fwd) => chainForward rest (ofVector fwd)
    | _ => none

set_option maxHeartbeats 1000000 in
/-- **After any number of hops, the forwarded packet is a fresh packet on the rest of the
path.** When the first `sks.length` hops of the path process in turn a packet `newKEMPacket`
built, what the last of them forwards is the packet `newKEMPacket` builds on the remaining path,
from the remaining seeds, with the original filler followed by one block for each hop. -/
theorem chainForward_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) (payload : ByteArray) :
    ∀ (sks : List ByteArray) (path : Array PathHop) (seeds : Array (Vector UInt8 32))
      (filler pkt : ByteArray),
      sks.length + 1 ≤ path.size →
      filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength →
      (∀ i, i < sks.length → kemSelfPublicKeyBytes kem sks[i]! = (path[i]!).publicKey) →
      (∀ j, j < path.size → kem.Reliable (kem.stateFromSeed seeds[j]!)) →
      (∀ i, i < sks.length → ∀ c ∈ (path[i]!).commands,
        c ≠ RoutingCommand.null ∧ ∀ id m, c ≠ RoutingCommand.nextNodeHop id m) →
      newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload = Except.ok pkt →
      chainForward kem cipher macS kdfS streamS geom sks pkt
        = (newKEMPacket kem cipher macS kdfS streamS geom (seeds.extract sks.length seeds.size)
            (filler ++ padsS geom (ksReal kem kdfS streamS geom path seeds) path.size
              sks.length 0)
            (path.extract sks.length path.size) payload).toOption := by
  intro sks
  induction sks with
  | nil =>
    intro path seeds filler pkt _ _ _ _ _ hnk
    show some pkt = _
    have e1 : seeds.extract 0 seeds.size = seeds := by simp
    have e2 : path.extract 0 path.size = path := by simp
    show some pkt = (newKEMPacket kem cipher macS kdfS streamS geom (seeds.extract 0 seeds.size)
      (filler ++ ByteArray.empty) (path.extract 0 path.size) payload).toOption
    rw [e1, e2, ByteArray.append_empty, hnk]
    rfl
  | cons sk rest ih =>
    intro path seeds filler pkt hlen hfs hpp hrel hcmd hnk
    have hlen' : rest.length + 2 ≤ path.size := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨-, hdr, sprpKeys, t, hcreate, -, -, -⟩ :=
      newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ payload pkt hnk
    obtain ⟨-, hple, hesize, -⟩ :=
      createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ hdr sprpKeys hcreate
    obtain ⟨-, -, hrouting, -, -, -⟩ := id hvalid
    obtain ⟨tag, cmds, fwd, hunwrap, htail⟩ := newKEMPacket_unwrapKEM_tail kem cipher macS kdfS streamS geom hvalid hmactag
      h16 seeds filler path payload pkt sk (by omega)
      (by simpa using hpp 0 (by simp)) hrel
      (fun c hc => (hcmd 0 (by simp) c hc).1) (fun c hc => (hcmd 0 (by simp) c hc).2) hnk
    have hfill : tailFiller kem kdfS streamS geom path seeds filler
        = filler ++ padS geom (ksReal kem kdfS streamS geom path seeds) (path.size - 1) := by
      unfold tailFiller
      rw [tailPad_eq_padS]
      congr 1
      split
      · rfl
      · next hc =>
        refine (eq_empty_of_size_zero _ ?_).symm
        rw [hfs, Nat.sub_eq_zero_of_le (by omega), Nat.zero_mul]
    have hps : (path.extract 1 path.size).size = path.size - 1 := by simp
    have hih := ih (path.extract 1 path.size) (seeds.extract 1 seeds.size)
      (tailFiller kem kdfS streamS geom path seeds filler) (ofVector fwd)
      (by rw [hps]; omega)
      (by
        rw [hfill, ByteArray.size_append, hfs, hps,
          padS_size geom _ (ksReal_size kem kdfS streamS geom path seeds) hrouting _ (by omega)]
        have h1 : geom.nrHops - (path.size - 1) = (geom.nrHops - path.size) + 1 := by omega
        rw [h1, Nat.succ_mul])
      (fun i hi => by
        have := hpp (i + 1) (by simpa using hi)
        rw [getElem!_extract_one]
        simpa using this)
      (fun j hj => by
        rw [getElem!_extract_one]
        exact hrel (j + 1) (by rw [hps] at hj; omega))
      (fun i hi => by
        rw [getElem!_extract_one]
        exact hcmd (i + 1) (by simpa using hi))
      htail
    have hcf : chainForward kem cipher macS kdfS streamS geom (sk :: rest) pkt
        = chainForward kem cipher macS kdfS streamS geom rest (ofVector fwd) := by
      show (match unwrapKEM kem cipher macS kdfS streamS geom sk pkt with
        | .ok (_, _, _, some fwd) => chainForward kem cipher macS kdfS streamS geom rest (ofVector fwd)
        | _ => none) = _
      rw [hunwrap]
    rw [hcf, hih, extract_one_extract, extract_one_extract, hfill, hps, ksReal_rest, padsS_shift,
      ByteArray.append_assoc]
    show _ = (newKEMPacket kem cipher macS kdfS streamS geom (seeds.extract (rest.length + 1) seeds.size)
      (filler ++ (padS geom (fun m => ksReal kem kdfS streamS geom path seeds (0 + m))
          (path.size - 1 - 0)
        ++ padsS geom (ksReal kem kdfS streamS geom path seeds) path.size rest.length (0 + 1)))
      (path.extract (rest.length + 1) path.size) payload).toOption
    simp only [Nat.zero_add, Nat.sub_zero]

end ChainForward

end Cryptlib.Protocols.Sphinx.KEMSphinx
