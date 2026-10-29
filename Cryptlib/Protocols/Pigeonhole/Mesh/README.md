# Pigeonhole over a Reticulum mesh

A protocol model of adaptive Pigeonhole storage over a Reticulum mesh, following the website's
`content/en/docs/specs/pigeonhole_replica_reticulum_protocols.md` and the Quint model
`adaptive.qnt`. Quint checks the whole design at small sizes, with liveness and the comparison
between design choices. The Veil model here proves its safety properties for any number of
nodes, replicas, boxes and payloads.

## The protocol

A box is write-once: its ID is a blinded Ed25519 key, and it holds one payload signed under it,
or the tombstone that replaces it. K = 2. A box's rendezvous ranking puts the replicas in an
order, and its two owners are the first two replicas in it. Its preference order is the owners,
then the other replicas, then, if clients store too, the clients.

A write or delete lands on the first two nodes of the box's preference order that the writer can
reach. A node that is not an owner stores the entry marked hinted. A writer that can reach no
node keeps the operation pending and retries it. Any holder pushes its entry to an owner that
lacks it when the two are linked, and a hinted holder drops its copy once every owner holds that
same entry. A holder may also copy its entry onto the first two nodes it can reach (rehome).
When two copies meet, a tombstone wins over a box, and a copy that is not hinted replaces a
hinted one.

The network partitions arbitrarily, nodes crash and restart with their stores intact, and a
client may not know a path to a node it could reach.

## What is proved (Veil)

`veil/MeshVeil/Adaptive.lean` restates `adaptive.qnt` in [Veil](https://github.com/verse-lab/veil),
with nodes, boxes, payloads and zones as uninterpreted types. `#check_invariants` proves that
these hold in every reachable state, with thirteen auxiliary invariants:

| Name | Says |
|---|---|
| `acked_not_lost` | A box whose write was acknowledged and which is not deleted is held by some node, or still pending |
| `no_resurrection` | A node that has held a tombstone for a box holds it still, unless it dropped a hinted copy of that box |
| `owner_no_resurrection` | An owner that has held a tombstone for a box holds that tombstone for ever, so never the box again |
| `authentic` | A box held anywhere carries exactly the payload its writer wrote |
| `write_once` | A box's writer signed one payload for it |
| `hinted_off_owners` | A hinted copy is never on an owner, so owners never hold hinted entries |
| `off_owners_hinted` | Every copy on a node that is not an owner is hinted |

cvc5 finds each proof, and Lean checks it (`veil.smt.trust false`); the file then checks that
every theorem rests on Lean's own axioms only.

The ranking is an uninterpreted relation `before b u v`, and an owner of `b` is a replica with
fewer than two replicas before it. One assumption is made of it: each box's ranking has a first
replica, as any finite order on a nonempty set of replicas has (`ranking_has_first`). Without
it a box could have no owner, and a hinted holder could drop its copy with no owner holding it.
Nothing else about the ranking is used, so the proofs hold however the rendezvous hash orders the
nodes.

The model allows more than `adaptive.qnt`: every action is enabled at any time, a stale view
may hide any node from any client, and a signed box or tombstone may reach any storing node from
anywhere, such as a relay or a replay (`Inject`). The node checks the BACAP signature, so it
stores only what the box's writer signed. Both placement rules (`PLACE`, as `adaptive`), both
pools (`POOL`, as `anyPool`) and rehoming (`REHOME`, as `rehome`) are covered.

The same file model-checks 4 nodes (3 replicas and a client that also stores), one box, 2
payloads and 2 zones (`#model_check`), and finds two runs with the solver:

- `drop_unacked_loses`: were a hinted holder to drop its copy once it has sent it to an owner,
  rather than once the owner holds it, a push lost on the way loses an acknowledged box.
  `dropUnacked` turns this on; `acked_not_lost` is proved with it off.
- `hinted_holder_resurrects`: a node that dropped its hinted tombstone, because every owner held
  it, takes the box again when a copy of the box reaches it. So `no_resurrection` cannot drop
  its condition: only owners, which never drop, keep a tombstone for ever, and a reader that
  asks such a node sees the deleted box. In the trace both the tombstone and the box arrive by
  `Inject`; a retried write or a rehome from a stale holder stores the box the same way.

```
make veil-mesh   # or: cd veil && lake build
```

`veil/` is its own Lake project, on Veil's toolchain (Lean 4.32.0, no Mathlib), so it does not
import Cryptlib. A first build fetches and compiles Veil, lean-smt and cvc5, and needs `npm`.

## What is not shown

- **Liveness and convergence.** That a pending operation lands, that every box reaches its
  owners once the network heals, and that reads after healing are right, stay with Quint and TLC.
  The healed-network round `syncRound` is not modelled.
- **Reads.** Which nodes a reader asks, and what it finds, are Quint's `LocalAvailability` and
  `ComponentAvailability`; the Veil model has no reads.
- **Cryptography.** That only the writer can sign for a box is assumed of BACAP: the model's
  nodes accept only what the writer signed.
- **Garbage collection.** Tombstones are kept for ever, as in `adaptive.qnt`.
- **Counting.** That a write lands on at most two nodes follows from the ranking being an order,
  which the proofs do not assume and do not need.
