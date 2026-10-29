module

public import Veil

/-!
Adaptive Pigeonhole placement over a Reticulum mesh, K = 2, for any number of nodes, boxes and
payloads. Follows `adaptive.qnt`, with every topology change, crash, restart, stale view, retry,
handoff and rehome allowed at any time, and with signed entries that may also arrive from
anywhere (`Inject`). The healed-network `syncRound` is not modelled.
-/

veil module Adaptive

type node
type box
type payload
type zone

/-! ## Theory -/

-- Replicas; every other node is a client.
immutable relation replica : node → Bool
-- `before b u v`: `u` comes before `v` in box `b`'s preference order.
immutable relation before : box → node → node → Bool
-- Clients store boxes too, as a last resort (`POOL = "any"`).
immutable individual anyPool : Bool
-- A write lands on the first two reachable nodes (`PLACE = "adaptive"`), not only on reachable owners.
immutable individual adaptive : Bool
-- Holders copy entries onto the first two nodes they can reach (`REHOME`).
immutable individual rehome : Bool
-- Not the protocol: a hinted holder drops its copy once it has sent it to an owner, without
-- waiting for the owner to hold it.
immutable individual dropUnacked : Bool
-- The nodes each client starts out not knowing a path to.
immutable relation initBlind : node → node → Bool

/-! ## State -/

-- The network.
function zoneOf : node → zone
relation up : node → Bool
relation blind : node → node → Bool

-- What each node holds for each box: nothing, the box, or its tombstone, hinted or not.
relation held : node → box → Bool
relation tomb : node → box → Bool
relation hinted : node → box → Bool
-- `payR n b p`: the box `n` holds for `b` carries payload `p`.
relation payR : node → box → payload → Bool

-- The writers.
relation written : box → Bool
function wpay : box → payload
relation signed : box → payload → Bool
relation acked : box → Bool
relation deleted : box → Bool
relation pendBox : box → Bool
relation pendTomb : box → Bool

-- History: `n` has held a tombstone for `b`, or has dropped a copy of `b`.
relation everTomb : node → box → Bool
relation dropped : node → box → Bool

-- The nodes an entry is being merged into, and the payload it carries.
relation tgt : node → Bool
relation fresh : node → Bool
relation inPay : payload → Bool

#gen_state

-- Each box's preference order has a first replica, as any finite order has.
assumption [ranking_has_first] ∀ b, ∃ n, replica n ∧ ∀ u, replica u → ¬ before b u n

/-! ## Ranking, reachability and placement -/

-- The owners: the first two replicas in the box's ranking.
ghost relation owner (n : node) (b : box) :=
  replica n ∧ ¬ ∃ u v, u ≠ v ∧ replica u ∧ replica v ∧ before b u n ∧ before b v n

ghost relation pool (n : node) := replica n ∨ anyPool
ghost relation linked (a : node) (m : node) := zoneOf a = zoneOf m ∧ up a ∧ up m
ghost relation reach (a : node) (m : node) := pool m ∧ linked a m
ghost relation view (c : node) (m : node) := reach c m ∧ ¬ blind c m

-- `t` is among the first two nodes of `b`'s preference order in the client's view.
ghost relation firstView (b : box) (c : node) (t : node) :=
  view c t ∧ ¬ ∃ u v, u ≠ v ∧ view c u ∧ view c v ∧ before b u t ∧ before b v t

-- `t` is among the first two nodes of `b`'s preference order that `r` can reach.
ghost relation home (b : box) (r : node) (t : node) :=
  reach r t ∧ ¬ ∃ u v, u ≠ v ∧ reach r u ∧ reach r v ∧ before b u t ∧ before b v t

-- A ranking as the protocol builds one: a strict total order on nodes, replicas first. The proofs
-- do not need it; the traces below ask for it.
ghost relation ranked :=
  (∀ b u, ¬ before b u u) ∧ (∀ b u v w, before b u v ∧ before b v w → before b u w) ∧
  (∀ b u v, u ≠ v → before b u v ∨ before b v u) ∧ (∀ b u v, replica u ∧ ¬ replica v → before b u v)

after_init {
  zoneOf := *
  up N := true
  blind N M := initBlind N M ∧ ¬ replica N
  held N B := false
  tomb N B := false
  hinted N B := false
  written B := false
  signed B P := false
  acked B := false
  deleted B := false
  pendBox B := false
  pendTomb B := false
  everTomb N B := false
  dropped N B := false
  tgt N := false
  fresh N := false
  inPay P := false
  payR N B P := false
}

/-! ## Storing an entry -/

-- Merge the box (`k` false, payload in `inPay`) or its tombstone (`k` true) into every node in
-- `tgt`, hinted on non-owners. `fresh` marks the nodes whose entry is replaced. A tombstone wins over a box; a copy that is not hinted replaces a
-- hinted one; otherwise the entry already held stays.
procedure merge (b : box) (k : Bool) {
  fresh N := decide $ tgt N ∧ (¬ held N b ∨ (¬ tomb N b ∧ (k ∨ (hinted N b ∧ owner N b))))
  payR N b P := decide $ (fresh N ∧ ¬ k ∧ inPay P) ∨ (¬ fresh N ∧ payR N b P)
  hinted N b := decide $ (fresh N ∧ ¬ owner N b) ∨ (¬ fresh N ∧ hinted N b)
  tomb N b := decide $ tomb N b ∨ (tgt N ∧ k)
  everTomb N b := decide $ everTomb N b ∨ (tgt N ∧ k)
  held N b := decide $ held N b ∨ tgt N
  fresh N := false
  tgt N := false
  inPay P := false
}

procedure drop (n : node) (b : box) {
  held n b := false
  tomb n b := false
  hinted n b := false
  payR n b P := false
  dropped n b := true
}

set_option synthInstance.maxHeartbeats 400000

/-! ## Clients -/

-- Where a client's write or delete of `b` lands.
procedure aim (c : node) (b : box) {
  if adaptive then
    tgt N := decide $ firstView b c N
  else
    tgt N := decide $ owner N b ∧ view c N
}

action Write (c : node) (b : box) (p : payload) {
  require ¬ replica c
  require up c
  require ¬ written b
  aim c b
  require ∃ t, tgt t
  written b := true
  wpay b := p
  signed b p := true
  inPay P := decide $ P = p
  merge b false
  acked b := true
}

-- A write that reaches no node stays pending.
action WritePending (c : node) (b : box) (p : payload) {
  require ¬ replica c
  require up c
  require ¬ written b
  aim c b
  require ¬ ∃ t, tgt t
  written b := true
  wpay b := p
  signed b p := true
  pendBox b := true
}

action Delete (c : node) (b : box) {
  require ¬ replica c
  require up c
  require written b
  require ¬ deleted b
  aim c b
  require ∃ t, tgt t
  deleted b := true
  merge b true
}

action DeletePending (c : node) (b : box) {
  require ¬ replica c
  require up c
  require written b
  require ¬ deleted b
  aim c b
  require ¬ ∃ t, tgt t
  deleted b := true
  pendTomb b := true
}

action RetryBox (c : node) (b : box) {
  require ¬ replica c
  require up c
  require pendBox b
  aim c b
  require ∃ t, tgt t
  inPay P := decide $ P = wpay b
  merge b false
  pendBox b := false
  acked b := true
}

action RetryTomb (c : node) (b : box) {
  require ¬ replica c
  require up c
  require pendTomb b
  aim c b
  require ∃ t, tgt t
  merge b true
  pendTomb b := false
}

/-! ## Storage nodes -/

-- A holder pushes its entry to an owner that lacks it. A hinted holder drops its copy once
-- every owner holds that same entry.
action Handoff (r : node) (b : box) (o : node) {
  require held r b
  require owner o b
  require r ≠ o
  require linked r o
  require ¬ held o b ∨ (tomb r b ∧ ¬ tomb o b)
  if ¬ held o b then
    payR o b P := payR r b P
  hinted o b := false
  tomb o b := tomb r b
  everTomb o b := decide $ everTomb o b ∨ tomb r b
  held o b := true
  if hinted r b ∧ ∀ x, owner x b → held x b ∧ ((tomb x b ∧ tomb r b) ∨ (¬ tomb x b ∧ ¬ tomb r b)) then
    drop r b
}

-- Not the protocol: the push is lost on the way, and the holder drops its copy anyway.
action HandoffLost (r : node) (b : box) (o : node) {
  require dropUnacked
  require held r b
  require hinted r b
  require owner o b
  require r ≠ o
  require linked r o
  require ¬ held o b
  drop r b
}

-- A holder copies its entry onto the first two nodes it can reach that lack it.
action Rehome (r : node) (b : box) {
  require rehome
  require up r
  require held r b
  require ∃ t, home b r t ∧ ¬ held t b
  tgt N := decide $ home b r N ∧ ¬ held N b
  inPay P := payR r b P
  merge b (tomb r b)
}

-- A signed entry reaches a node from anywhere: a relay, a replay, another holder. The node
-- checks the BACAP signature, so it stores only what the box's writer signed.
action Inject (n : node) (b : box) (k : Bool) (p : payload) {
  require pool n
  require (k ∧ deleted b) ∨ (¬ k ∧ signed b p)
  if ¬ held n b then
    if ¬ k then
      payR n b P := decide $ P = p
    held n b := true
    tomb n b := k
    everTomb n b := everTomb n b || k
    hinted n b := decide $ ¬ owner n b
  else
    if ¬ tomb n b ∧ k then
      tomb n b := true
      everTomb n b := true
      hinted n b := decide $ ¬ owner n b
    else
      if ¬ tomb n b ∧ hinted n b ∧ owner n b then
        payR n b P := decide $ P = p
        hinted n b := false
}

/-! ## Environment -/

action Partition (n : node) (z : zone) {
  zoneOf n := z
}

action Crash (n : node) {
  require up n
  up n := false
}

action Restart (n : node) {
  require ¬ up n
  up n := true
}

action Stale (c : node) (n : node) {
  require ¬ replica c
  blind c N := decide $ N = n
}

action Refresh (c : node) {
  require ¬ replica c
  blind c N := false
}

/-! ## Properties -/

-- An acked box that is not deleted is held by some node or still pending.
safety [acked_not_lost] ¬ dropUnacked → (acked B ∧ ¬ deleted B → (∃ n, held n B) ∨ pendBox B)

-- A node that has held a tombstone for `b` holds it still, unless it dropped a hinted copy.
safety [no_resurrection] everTomb N B ∧ ¬ dropped N B → held N B ∧ tomb N B
-- Owners never drop, so an owner that has held a tombstone never holds the box again.
safety [owner_no_resurrection] everTomb N B ∧ owner N B → held N B ∧ tomb N B

-- A box held anywhere carries the payload its writer wrote, and its writer signed only that.
safety [authentic] held N B ∧ ¬ tomb N B → written B ∧ (payR N B P ↔ P = wpay B)
safety [write_once] signed B P → written B ∧ P = wpay B

-- Hinted copies sit only on non-owners, and every copy on a non-owner is hinted.
safety [hinted_off_owners] held N B ∧ hinted N B → ¬ owner N B
safety [off_owners_hinted] held N B ∧ ¬ owner N B → hinted N B

-- Auxiliary invariants, to make the above inductive.
invariant [tgt_empty] ¬ tgt N
invariant [fresh_empty] ¬ fresh N
invariant [in_pay_empty] ¬ inPay P
invariant [tomb_held] tomb N B → held N B
invariant [hinted_held] hinted N B → held N B
invariant [tomb_deleted] tomb N B → deleted B
invariant [ever_tomb_deleted] everTomb N B → deleted B
invariant [owner_kept] owner N B → ¬ dropped N B
invariant [held_written] held N B → written B
invariant [deleted_written] deleted B → written B
invariant [acked_written] acked B → written B
invariant [pend_box_written] pendBox B → written B
invariant [pend_tomb_deleted] pendTomb B → deleted B

set_option veil.smt.trust false

#gen_spec

-- Declare the verification conditions as theorems, so their axioms can be checked below.
#gen_theorems

#check_invariants

-- 3 replicas and a client that stores too, ranked by node number.
#model_check { node := Fin 4, box := Fin 1, payload := Fin 2, zone := Fin 2 }
  { replica := fun n => n.val < 3, before := fun _ u v => u < v, anyPool := true,
    adaptive := true, rehome := true, dropUnacked := false, initBlind := fun _ _ => false }

-- The assumptions are satisfiable.
sat trace { }

-- A hinted holder that drops a box it has only sent loses it, if the push never arrives.
sat trace [drop_unacked_loses] {
  Write
  Partition
  HandoffLost
  assert (ranked ∧ dropUnacked ∧ ∃ b, acked b ∧ ¬ deleted b ∧ (∀ n, ¬ held n b) ∧ ¬ pendBox b)
}

-- A non-owner that dropped its hinted tombstone, because every owner held it, takes the box
-- again when a copy of it arrives. Here the tombstone and the box reach it by `Inject`.
sat trace [hinted_holder_resurrects] {
  WritePending
  DeletePending
  Inject
  Handoff
  Inject
  assert (ranked ∧ ∃ n b, everTomb n b ∧ held n b ∧ ¬ tomb n b)
}

end Adaptive

-- Every verification condition rests on Lean's own axioms only.
open Lean in
run_cmd do
  let env ← getEnv
  let own := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  for (name, info) in env.constants.map₂.toList do
    unless (`Adaptive).isPrefixOf name && info matches .thmInfo _ do continue
    n := n + 1
    for ax in ← collectAxioms name do
      unless own.contains ax do
        throwError "{name} depends on {ax}"
  if n == 0 then throwError "no Adaptive theorems"
  logInfo m!"{n} Adaptive theorems rest on Lean's own axioms only"
