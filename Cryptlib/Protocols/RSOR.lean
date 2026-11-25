/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.CryptoFoundations.KeyEncapMech

/-! # Repliable service onion routing

The scheme and the onion properties of Philip Scherer, Christiane Weis and Thorsten Strufe,
*Provable Security for the Onion Routing and Mix Network Packet Format Sphinx*, PoPETs 2024,
<https://arxiv.org/abs/2312.08028>. A bare `Definition n` or `§n.m` in this file refers to that
paper.

`Scheme` is Definition 1 with RSOR-Correctness (§A.1) as its laws. The three games are
`forwardUnlinkable` (TLU→, Definition 2), `backwardUnlinkable` (SLU←, §A.2) and
`tailIndistinguishable` (STI↔, §A.3).

Three things differ from the paper. Its challenger checks the adversary's paths; here a path
that fails the check is not a `Route`. Its challenger also rejects a relay named on both paths
with two keys; here the adversary may do that. Its reply oracle answers an onion any number of
times, except the replacement of TLU→, which it answers once; a second reply would tell the
two worlds apart. Here every onion is answered once, as the protocol of §3.1.3 does. -/

namespace Cryptlib.Protocols.RSOR

open OracleComp OracleSpec ENNReal

/-- A relay as a sender names it. -/
structure Hop (Name Key : Type) where
  name : Name
  key : Key

/-- An acyclic path of at most `N` relays (Assumptions 1 and 2). -/
structure Route (N : ℕ) (Name Key : Type) where
  hops : List (Hop Name Key)
  length_le : hops.length ≤ N
  nodup : (hops.map (·.name)).Nodup

namespace Route

variable {N : ℕ} {Name Key : Type}

def nil : Route N Name Key := ⟨[], N.zero_le, List.nodup_nil⟩

def take (R : Route N Name Key) (k : ℕ) : Route N Name Key :=
  ⟨R.hops.take k, (List.take_sublist k _).length_le.trans R.length_le,
    R.nodup.sublist ((List.take_sublist k _).map _)⟩

def drop (R : Route N Name Key) (k : ℕ) : Route N Name Key :=
  ⟨R.hops.drop k, (List.drop_sublist k _).length_le.trans R.length_le,
    R.nodup.sublist ((List.drop_sublist k _).map _)⟩

theorem take_ne (R : Route N Name Key) {k : ℕ} (h : k < R.hops.length) :
    (R.take (k + 1)).hops ≠ [] :=
  List.ne_nil_of_length_pos (by simp [take]; omega)

theorem drop_ne (R : Route N Name Key) {k : ℕ} (h : k < R.hops.length) :
    (R.drop k).hops ≠ [] :=
  List.ne_nil_of_length_pos (by simp [drop]; omega)

end Route

/-- What a sender asks of `FormOnion`. The forward path is never empty (Assumption 8); an empty
backward path asks for an onion that cannot be replied to. -/
structure Request (N : ℕ) (Name Key Msg Receiver : Type) where
  msg : Msg
  receiver : Receiver
  fwd : Route N Name Key
  back : Route N Name Key
  fwd_ne : fwd.hops ≠ []

namespace Request

variable {N : ℕ} {Name Key Msg Receiver : Type} (q : Request N Name Key Msg Receiver)

/-- The forward position of the first relay. -/
def first : Fin q.fwd.hops.length := ⟨0, List.length_pos_iff.2 q.fwd_ne⟩

/-- The forward position of the exit relay. -/
def last : Fin q.fwd.hops.length :=
  ⟨q.fwd.hops.length - 1, Nat.sub_one_lt (Nat.ne_of_gt q.first.pos)⟩

end Request

/-- What a relay learns from an onion: where to send the next layer, the message for a receiver
outside the network, or a reply, still sealed, for the sender it serves. -/
inductive Step (Name Onion Msg Receiver Payload : Type)
  | forward (next : Name) (onion : Onion)
  | deliver (msg : Msg) (receiver : Receiver)
  | reply (payload : Payload)

/-- A repliable service onion routing scheme (Definition 1), with its correctness (§A.1).

`form q r i` is the layer the relay at forward position `i` receives, and `formBack q r m i` the
layer of the reply carrying `m` that the relay at backward position `i` receives. The paper has
one `FormOnion` for both.

The paper's sender opens a reply with its relay key. A Sphinx sender opens it with keys it kept
when it made the request, so here the last relay of the backward path hands over a sealed
payload and `recover` opens it with the randomness the sender built the request from. -/
structure Scheme where
  Name : Type
  Key : Type
  Secret : Type
  Randomness : Type
  Msg : Type
  Receiver : Type
  Header : Type
  Payload : Type
  [decHeader : DecidableEq Header]
  [decPayload : DecidableEq Payload]
  [sampleRandomness : SampleableType Randomness]
  [sampleMsg : SampleableType Msg]
  [sampleReceiver : SampleableType Receiver]
  [samplePayload : SampleableType Payload]
  maxHops : ℕ
  keygen : Name → ProbComp (Key × Secret)
  form : (q : Request maxHops Name Key Msg Receiver) → Randomness → Fin q.fwd.hops.length →
    Header × Payload
  formBack : (q : Request maxHops Name Key Msg Receiver) → Randomness → Msg →
    Fin q.back.hops.length → Header × Payload
  proc : Secret → Name → Header × Payload →
    Option (Step Name (Header × Payload) Msg Receiver Payload)
  reply : Secret → Name → Msg → Header × Payload → Option (Name × (Header × Payload))
  recover : Request maxHops Name Key Msg Receiver → Randomness → Payload → Option Msg
  /-- The randomness for which no relay on the paths fails to process its layer. Everything, unless
  the scheme rests on a primitive that can fail, as a lattice KEM can. -/
  reliable : Request maxHops Name Key Msg Receiver → Randomness → Prop := fun _ _ => True
  /-- A relay on the forward path gets the next layer, and the exit relay the message. -/
  proc_form : ∀ q r (i : Fin q.fwd.hops.length) sk, reliable q r →
    (q.fwd.hops[i].key, sk) ∈ support (keygen q.fwd.hops[i].name) →
    proc sk q.fwd.hops[i].name (form q r i) = some
      (if h : i + 1 < q.fwd.hops.length
        then .forward q.fwd.hops[i.val + 1].name (form q r ⟨i + 1, h⟩)
        else .deliver q.msg q.receiver)
  /-- The exit relay's reply is the first layer of the reply onion. -/
  reply_form : ∀ q r m (i : Fin q.fwd.hops.length) (j : Fin q.back.hops.length) sk,
    reliable q r → i + 1 = q.fwd.hops.length → j.val = 0 →
    (q.fwd.hops[i].key, sk) ∈ support (keygen q.fwd.hops[i].name) →
    reply sk q.fwd.hops[i].name m (form q r i) = some (q.back.hops[j].name, formBack q r m j)
  /-- A relay on the backward path gets the next layer. -/
  proc_formBack : ∀ q r m (i : Fin q.back.hops.length) (h : i.val + 1 < q.back.hops.length) sk,
    reliable q r → (q.back.hops[i].key, sk) ∈ support (keygen q.back.hops[i].name) →
    proc sk q.back.hops[i].name (formBack q r m i)
      = some (.forward q.back.hops[i.val + 1].name (formBack q r m ⟨i.val + 1, h⟩))
  /-- The last relay of the backward path gets a payload that the sender opens to the reply. -/
  recover_formBack : ∀ q r m (i : Fin q.back.hops.length) sk, reliable q r →
    i.val + 1 = q.back.hops.length →
    (q.back.hops[i].key, sk) ∈ support (keygen q.back.hops[i].name) →
    ∃ p, proc sk q.back.hops[i].name (formBack q r m i) = some (.reply p) ∧ recover q r p = some m

namespace Scheme

attribute [instance] decHeader decPayload sampleRandomness sampleMsg sampleReceiver samplePayload

variable (S : Scheme)

/-- An onion layer: a header and a payload (Assumption 5). -/
abbrev Onion := S.Header × S.Payload

abbrev Request := RSOR.Request S.maxHops S.Name S.Key S.Msg S.Receiver

abbrev Step := RSOR.Step S.Name S.Onion S.Msg S.Receiver S.Payload

end Scheme

/-! ## The games -/

/-- The honest relays of the games: a relay on the forward path, a relay on the backward path,
and the last relay of the backward path, which serves the sender. -/
inductive Role
  | relay
  | back
  | sender
  deriving DecidableEq

variable (S : Scheme)

/-- The honest relays as the adversary sees them. -/
abbrev Honest := Role → Hop S.Name S.Key

/-- The adversary's oracles: have an honest relay process an onion, or reply to one. -/
abbrev oracleSpec :=
  unifSpec + (Role × S.Onion →ₒ Option S.Step) +
    (Role × S.Msg × S.Onion →ₒ Option (S.Name × S.Onion))

/-- What the honest relays remember: the headers they have processed (Assumption 3) and the
onions they may still reply to. -/
structure Log where
  seen : List (Role × S.Header) := []
  held : List (Role × S.Onion) := []

/-- What the challenger answers in place of an honest relay's own answer. -/
structure Patch where
  proc : Role → S.Onion → Option S.Step → ProbComp (Option S.Step) := fun _ _ out => pure out
  reply : Role → S.Msg → S.Onion → Option (S.Name × S.Onion) → Option (S.Name × S.Onion) :=
    fun _ _ _ out => out

variable {S}

/-- An honest relay processes a header once (Assumption 3). -/
def process (hon : Honest S) (sk : Role → S.Secret) (patch : Patch S) :
    QueryImpl (Role × S.Onion →ₒ Option S.Step) (StateT (Log S) ProbComp) := fun (h, o) => do
  let log ← get
  if (h, o.1) ∈ log.seen then return none
  set ({ seen := (h, o.1) :: log.seen, held := (h, o) :: log.held } : Log S)
  patch.proc h o (S.proc (sk h) (hon h).name o)

/-- An honest relay replies once to an onion it has processed. -/
def answer (hon : Honest S) (sk : Role → S.Secret) (patch : Patch S) :
    QueryImpl (Role × S.Msg × S.Onion →ₒ Option (S.Name × S.Onion)) (StateT (Log S) ProbComp) :=
  fun (h, m, o) => do
    let log ← get
    if (h, o) ∈ log.held then
      set { log with held := log.held.erase (h, o) }
      return patch.reply h m o (S.reply (sk h) (hon h).name m o)
    else return none

/-- The honest relays, running the scheme except where `patch` says otherwise. -/
def oracle (hon : Honest S) (sk : Role → S.Secret) (patch : Patch S) :
    QueryImpl (oracleSpec S) (StateT (Log S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Log S) ProbComp)
    + process hon sk patch + answer hon sk patch

/-- What the challenger shows the adversary in one of its two worlds. -/
structure World (S : Scheme) where
  onion : S.Onion
  patch : Patch S := {}

/-- An onion property: what the adversary must submit, and the two worlds it must tell apart. -/
structure Property (S : Scheme) where
  Challenge : Honest S → Type
  world : {hon : Honest S} → Challenge hon → Bool → ProbComp (World S)

namespace Property

variable (P : Property S)

/-- The adversary has the honest relays' oracles before and after the challenge. -/
structure Adversary where
  State : Type
  choose : (hon : Honest S) → OracleComp (oracleSpec S) (P.Challenge hon × State)
  guess : State → S.Onion → OracleComp (oracleSpec S) Bool

variable {P}

/-- The game: the adversary wins if it says which world it was shown. -/
def game (names : Role → S.Name) (A : P.Adversary) : ProbComp Bool := do
  let kr ← S.keygen (names .relay)
  let kb ← S.keygen (names .back)
  let ks ← S.keygen (names .sender)
  let key : Role → S.Key × S.Secret := fun | .relay => kr | .back => kb | .sender => ks
  let hon : Honest S := fun h => ⟨names h, (key h).1⟩
  let sk := fun h => (key h).2
  let ((c, st), log) ← (simulateQ (oracle hon sk {}) (A.choose hon)).run {}
  let b ← $ᵗ Bool
  let w ← P.world c b
  let b' ← (simulateQ (oracle hon sk w.patch) (A.guess st w.onion)).run' log
  return b == b'

noncomputable def advantage (names : Role → S.Name) (A : P.Adversary) : ℝ≥0∞ :=
  𝒟[game names A].boolBias

end Property

/-! ## Tagging-forward layer unlinkability -/

/-- A request whose forward path has the honest relay at `pos` and whose replies come back to
the honest sender. -/
structure ForwardChallenge (hon : Honest S) where
  req : S.Request
  pos : Fin req.fwd.hops.length
  relay : req.fwd.hops[pos] = hon .relay
  sender : req.back.hops.getLast? = some (hon .sender)

/-- TLU→ (Definition 2). The adversary is shown the first layer of its onion, or of an onion
that ends at the honest relay and carries a random message. In the second world the honest relay
answers the replacement with what the original would have produced, and when its payload was
changed on the way, with a random payload: the tag travels on. As the exit relay it replies to
the unchanged replacement with the original's reply. The replacement ends at the honest relay
and has no backward path, so the relay's own answers to it would differ from its answers to the
original: it would reject a changed payload where it should pass it on, and fail to reply. -/
def forwardUnlinkable : Property S where
  Challenge := ForwardChallenge
  world c b := do
    let r ← $ᵗ S.Randomness
    if b then
      let q : S.Request :=
        { msg := ← $ᵗ S.Msg, receiver := ← $ᵗ S.Receiver, fwd := c.req.fwd.take (c.pos + 1),
          back := .nil, fwd_ne := c.req.fwd.take_ne c.pos.isLt }
      let r' ← $ᵗ S.Randomness
      let mine := S.form q r' ⟨c.pos, by simp [q, Route.take]⟩
      let home : Fin c.req.back.hops.length :=
        ⟨0, List.length_pos_iff.2 fun h => by simpa [h] using c.sender⟩
      return {
        onion := S.form q r' q.first
        patch :=
          { proc := fun h o out =>
              if h = .relay ∧ o.1 = mine.1 then
                if hn : c.pos + 1 < c.req.fwd.hops.length then
                  let next := S.form c.req r ⟨c.pos + 1, hn⟩
                  let name := c.req.fwd.hops[c.pos.val + 1].name
                  if o.2 = mine.2 then pure (some (.forward name next))
                  else do return some (.forward name (next.1, ← $ᵗ S.Payload))
                else pure (out.map fun _ => .deliver c.req.msg c.req.receiver)
              else pure out
            reply := fun h m o out =>
              if h = .relay ∧ o = mine ∧ c.pos + 1 = c.req.fwd.hops.length then
                some (c.req.back.hops[home].name, S.formBack c.req r m home)
              else out } }
    else return { onion := S.form c.req r c.req.first }

/-! ## Backward layer unlinkability -/

/-- A request whose replies come back to the honest sender through the honest relay. The relay
is the one before backward position `pos`: the exit relay when `pos` is zero. -/
structure BackwardChallenge (hon : Honest S) where
  req : S.Request
  pos : Fin req.back.hops.length
  relay : (match pos.val with
    | 0 => req.fwd.hops.getLast?
    | k + 1 => req.back.hops[k]?) = some (hon .relay)
  sender : req.back.hops.getLast? = some (hon .sender)

/-- SLU← (§A.2). The adversary is shown the first layer of its onion. When the reply reaches
the honest relay, the relay sends on the reply's next layer, or the first layer of a forward
onion along the rest of the backward path with a random message. The sender answers neither. -/
def backwardUnlinkable : Property S where
  Challenge := BackwardChallenge
  world c b := do
    let r ← $ᵗ S.Randomness
    let onion := S.form c.req r c.req.first
    let last : Fin c.req.back.hops.length :=
      ⟨c.req.back.hops.length - 1, by have := c.pos.isLt; omega⟩
    if b then
      let q : S.Request :=
        { msg := ← $ᵗ S.Msg, receiver := ← $ᵗ S.Receiver, fwd := c.req.back.drop c.pos,
          back := .nil, fwd_ne := c.req.back.drop_ne c.pos.isLt }
      let r' ← $ᵗ S.Randomness
      let swap : S.Name × S.Onion := (c.req.back.hops[c.pos].name, S.form q r' q.first)
      let swapAt : Option S.Header := match hk : c.pos.val with
        | 0 => none
        | k + 1 => some (S.formBack c.req r c.req.msg ⟨k, by have := c.pos.isLt; omega⟩).1
      return {
        onion
        patch :=
          { proc := fun h o out =>
              if h = .sender ∧ o.1 = (S.form q r' q.last).1 then pure none
              else if h = .relay ∧ swapAt = some o.1 then
                pure (out.map fun _ => .forward swap.1 swap.2)
              else pure out
            reply := fun h _ o out =>
              if h = .relay ∧ c.pos.val = 0 ∧ o.1 = (S.form c.req r c.req.last).1 then
                out.map fun _ => swap
              else out } }
    else return {
      onion
      patch :=
        { proc := fun h o out =>
            if h = .sender ∧ o.1 = (S.formBack c.req r c.req.msg last).1 then pure none
            else pure out } }

/-! ## Tail indistinguishability -/

/-- A request, the forward position `pos` of the layer the adversary is shown, and the honest
relay at backward position `back`. The relay before `pos` is honest, or `pos` is zero and the
layer is the sender's own. -/
structure TailChallenge (hon : Honest S) where
  req : S.Request
  pos : Fin req.fwd.hops.length
  back : Fin req.back.hops.length
  relay : ∀ k, k + 1 = pos.val →
    req.fwd.hops[k]? = some (hon .relay) ∨ req.fwd.hops[k]? = some (hon .back)
  backRelay : req.back.hops[back] = hon .back

/-- The layer of `q` at forward position `i`, with the honest backward relay answering nothing
to the reply layer at backward position `k`. -/
def tailWorld (q : S.Request) (r : S.Randomness) (i : Fin q.fwd.hops.length)
    (k : Fin q.back.hops.length) : World S where
  onion := S.form q r i
  patch :=
    { proc := fun h o out =>
        if h = .back ∧ o.1 = (S.formBack q r q.msg k).1 then pure none else pure out }

/-- STI↔ (§A.3). The adversary is shown the layer of its onion that leaves an honest relay, or
the first layer of an onion with the same message over the rest of the forward path and the
backward path up to its honest relay. -/
def tailIndistinguishable : Property S where
  Challenge := TailChallenge
  world c b := do
    let r ← $ᵗ S.Randomness
    if b then
      let q : S.Request :=
        { c.req with fwd := c.req.fwd.drop c.pos, back := c.req.back.take (c.back + 1),
                     fwd_ne := c.req.fwd.drop_ne c.pos.isLt }
      return tailWorld q r q.first ⟨c.back, by simp [q, Route.take]⟩
    else return tailWorld c.req r c.pos c.back

end Cryptlib.Protocols.RSOR
