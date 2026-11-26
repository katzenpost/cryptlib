# Notes on the Sphinx formalization

Things about `Cryptlib/Protocols/Sphinx` that are easy to miss when reading the code.

## What is assumed

`make axioms` (`lake lint`, the program `Cryptlib/check_axioms.lean`) fails if a theorem rests
on anything but Lean's three axioms and the two we declare on purpose: that the field prime of
Curve25519 is prime (`X25519.p_prime`) and that the order of its prime subgroup is prime
(`Ed25519Blinded.ell_prime`).

There is a third axiom in the library, `aez_roundTrip`: AEZ decryption inverts AEZ encryption.
We wrote AEZ in Lean and check it against test vectors, but we have not proved its round trip,
so we assume it. It is used in one place, to make AEZ a `WideBlockCipher`. No theorem rests on
it, because the Sphinx theorems are stated for any `WideBlockCipher`. It only matters when you
pick AEZ as the cipher.

## Two payload ciphers

`WideBlockCipher` is the type of a payload cipher. Its fields include the laws: encryption and
decryption keep the length, and decryption inverts encryption on blocks of at least 16 bytes.
A value of the type carries proofs of them.

- `AEZ.aez` is the cipher Katzenpost uses. Its round trip is the axiom above.
- `Lioness.lioness s h` is Lioness over any stream cipher `s` and keyed hash `h`. Its round trip
  is proved (`Lioness.decrypt_encrypt`), with no axiom. `Lioness.chacha20Blake2b` is the
  instance the Rust crate `rust-lioness` uses.
- `Lioness.sphinx` is Lioness sized for Sphinx. Sphinx gives the cipher a 48-byte key and a
  16-byte IV; Lioness wants 128 and 48. We stretch them with HKDF-SHA256-Expand. That step is
  our choice and is not part of any deployed format.

The self-test builds, routes and answers packets with both ciphers.

## Exact laws and computational security

A law that holds for every input is a field of a type. Security that holds only against
bounded adversaries is a game and a theorem about it, never a field.

`Protocols.RSOR.Scheme` is repliable onion routing after Scherer, Weis and Strufe (PoPETs
2024). Its fields include the correctness laws, so a scheme is correct by construction.
`KEMSphinx.RSOR.scheme` and the NIKE Sphinx scheme in `NIKESphinxRSOR.lean` are values of it.

A relay's key in the KEM scheme is a public key that has a private key
(`KEMSphinx.RSOR.Key`). Without that the correctness laws are false for junk keys.

The laws hold for the draws that are `reliable`: the KEM round trips and the packet can be
built. The bounds pay for the other draws as an explicit probability.

## The games differ from the paper in one place

The three properties are `forwardUnlinkable` (TLU→), `backwardUnlinkable` (SLU←) and
`tailIndistinguishable` (STI↔) in `Protocols/RSOR.lean`.

In TLU→ the second world shows a replacement onion that ends at the honest relay. Read
literally, the paper's Definition 2 lets the adversary win at once: the relay would reject a
changed payload where the original passes it on, and would fail to reply as the exit. The
paper's proof has the relay answer the replacement as it would the original. Our game says
that: a `Patch` overrides the relay's own answer. We found this by playing honest runs of both
worlds in the self-test before proving anything.

## The relay keeps answering the challenge ciphertext

The relay remembers whole headers, not KEM ciphertexts. A packet with the challenge ciphertext
and a different header is processed again. So the KEM game we reduce to has a decapsulation
oracle that refuses the challenge ciphertext (`kemExpK`), and the relay goes on answering such
packets with the game's keys (`keyedChain_le`).

## What is proved

- RSOR-Correctness, for KEM Sphinx and NIKE Sphinx.
- For KEM Sphinx and TLU→: `forwardUnlinkable_le_keyedIdeal`. The advantage is at most the
  chance of a bad draw in either world, the KEM and KDF advantages of named adversaries, and
  the distance between the two worlds once the honest relay's keys are uniform.

- The MAC step, for any keyed game (`keyedIdeal_sub_tagged_le`). If the view uses the honest
  relay's MAC key for one tag, the relay may answer the challenge ciphertext under the challenge
  header only, at the cost of a forgery against the MAC (`MAC.forgeExp`) and the bad draws.
- For KEM Sphinx and TLU→ with that step applied to both worlds:
  `forwardUnlinkable_le_tagged`. The advantage is at most the bad draws, the KEM and KDF
  advantages, a MAC forgery in either world, and the distance between the two worlds once the
  relay's keys are uniform and it answers the challenge ciphertext under the challenge header
  only.

- The payload cipher step, for each world of TLU→ (`forward_payload_le`, `short_payload_le`).
  Once the relay answers one header only, it decrypts one block per header: its log admits a
  header once (`viaDec_decOnce`). So the world is the game for a payload key used for one block
  (`WideBlockCipher.oneQueryExp`, through `PayloadGame.exp_eq`), and the cipher can be replaced
  by the ideal one at the cost of that game's advantage and the bad draws. In the ideal world
  the encrypted block is uniform, and the relay decrypts it to the sender's block and any other
  block to one uniform block.
- All of the above in one statement: `forwardUnlinkable_le_uniform`. The TLU→ advantage against
  KEM Sphinx is at most the bad draws, the KEM and KDF advantages, a MAC forgery, the one-block
  cipher advantage and the keystream generator's advantage, each in either world, and the
  distance between the two worlds played from a uniform keystream.
- The same again for the layer the adversary's original onion has at the honest relay, in
  world 1 (`short_next_le`). There the relay answers the replacement with the original's next
  layer, which depends on the keys of the original's own layer at the relay through one
  keystream (`next_setSeed`). Those keys are replaced as the first were: world 1 is a keyed game
  around that layer's ciphertext (`shortIdeal_sub_nextReal_le`), no tag under its MAC key is
  shown so the relay may reject the ciphertext (`nextIdeal_sub_reject_le`), and the keystream
  becomes uniform (`nextReject_eq_prg`).
- All of that in one statement: `forwardUnlinkable_le_next`. What is left is the distance between
  world 0 from a uniform keystream and world 1 with both keystreams uniform.

The cipher game gives the adversary a decryption oracle that answers for one block, the first
it is asked about. The relay asks it twice about the same block when it replies to an onion it
has processed, which is why the oracle remembers its block instead of answering once.

- The stream cipher step, for each world (`forward_stream_le`, `short_stream_le`). After the
  payload step the relay uses its header encryption key and IV for one keystream only, so the
  world is the real experiment of the keystream generator `keystreamPRG`
  (`forwardPayload_exp_false_eq_prg`), and the keystream can be replaced by uniform bytes at
  the cost of that generator's advantage. Each world is then a game played from a uniform
  keystream, a uniform encrypted block and the relay's MAC key.

For this step a draw is good only if the sender's block at the relay has a payload's length.
That it always has, when the onion can be built, is not proved yet.

The last comparison is in progress (`KEMSphinxTLUFinal.lean`, `KEMSphinxPad.lean`). Proved so
far:

- Rejecting the original's ciphertext, which the adversary is never shown, costs the chance
  that it sends that ciphertext (`next_hidden_le`). That chance is left as a probability
  (`nextHidden`): the KEM type has no statement yet that a ciphertext is hard to guess.
- World 1 after its draws is a relay that answers one header (`nextOwn_run`), as world 0 is.
- The payload the challenger draws when it answers a changed onion may be drawn before the game,
  because a relay processes a header once (`oracle_draw`, `patchWith_draw`).
- What the relay does with its own header for any keystream: before the end of the path it
  forwards the next layer's header with the payload it is given (`stepOf_relayFront`), at the
  end it delivers when the payload begins with the zero tag (`stepOf_relayFrontLast`).
- The relay's header on a path that goes on is its header on a path that ends at it, once the
  head of its keystream is shifted (`relayFront_eq_last`). The next layer built with other hops
  in front is the same layer once the tail of the keystream is shifted (`layerPast_shift`).
  The layers in front read only the hops in front (`wrapUp_congr`).

Not proved yet: the equality of the two games from these pieces, up to the chance that a
uniform block passes the payload's tag check; a bound on the bad draws;
SLU← and STI↔ for KEM Sphinx; all three for NIKE Sphinx.

## How the bounds are built

The structural lemmas are stated for packets built from any keys (`newKEMPacketFrom`), not only
from keys the KDF derives. A packet with uniform keys at one hop is covered by taking the KDF
that returns those keys whatever its input (`keysKDF`). So the lemmas about real packets are
corollaries, and the same lemmas serve the games after the keys are replaced.

A step that changes how the relay answers is one use of `Util.UntilBad`: two oracles without
state that agree except on bad queries differ by at most the chance of a bad query, counted on
the second oracle with a record of its queries. A reduction answers as the second oracle does
and hands the record to its own challenger.

## Checks

`make test` runs every suite, including the Katzenpost vectors and honest runs of the three
games in both worlds. `make axioms` is the axiom check above. A security bound has no
executable test; its check is the honest run of its game and a comparison with the paper.
