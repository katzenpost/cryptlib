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

- After their draws the two worlds are the same game, in both positions of the relay
  (`nextDrawn_eq_forward`, `nextDrawn_eq_last`). World 0 is played with the original's
  randomness except for the seeds of the hops in front, which are the replacement's
  (`mixSeeds`), and with the relay's keystream shifted (`shiftStream`, `lastShift`). The
  conditions are that the next layer builds, the original's request is reliable at the exit,
  and the ideal cipher's second block does not begin with the zero tag. A sender's payload has
  one length whatever the request (`body_size`), so its length is not a condition.

- The relabelled draws are uniform (`evalDistEq_mixSeeds`, `evalDistEq_headTail`,
  `evalDistEq_shiftStream`, `evalDistEq_lastShift`), so the two games differ by at most the
  chance of a draw of world 1 that is not good (`final_fixed_le`, `next_final_le`).

**The TLU→ bound** is `forwardUnlinkable_le` in `KEMSphinxTLUFinal.lean`. The advantage is at
most the sum of:

- the chance of a draw on which a layer does not build or a KEM round trip fails, for each
  world and each replacement of keys;
- the cost of replacing the relay's keys, for each world and for the original's hidden layer
  (`keyedCost`: KEM and KDF);
- a forgery against the MAC, for each of the three;
- the one-block advantage against the payload cipher, for each world;
- the keystream generator's advantage, for each of the three keystreams;
- the chance that the adversary sends the hidden ciphertext (`nextHidden`);
- the chance of a draw of world 1 that is not good for the last comparison (`finalGood`): the
  original's next layer does not build, the original's request is not reliable at the exit, or
  the ideal cipher's second block begins with the zero tag.

No term is a distance between two games. The last two groups and the first are probabilities
of events on draws, not yet bounded by numbers:

- that a KEM ciphertext is hard to guess is not a law of the KEM type yet, so `nextHidden`
  has no bound;
- the chance that a layer does not build is not reduced to the KEM here yet; a first layer
  always builds (`layer_zero_builds`), so this is about seeds that are not reliable.

The zero-tag event is bounded: a draw of world 1 is not good with at most the chance that a
layer cannot be built, plus one in the number of payload tags (`prEvent_not_finalGood_le`,
from `prEvent_zeroPrefix`).

Not proved yet: those two; all three for NIKE Sphinx. SLU← and STI↔ for KEM Sphinx are below,
each with its own explicit events.

### SLU← (in progress)

The self-test found the game distinguishable as first stated. In world 0 the adversary could
ask the honest sender to reply to the reply's last layer. The scheme's reply rule read any
decrypted payload whose first byte is 1 as carrying a SURB, on a reply packet too, where the
payload is not checked. The sender answered in 9 of 3000 runs, about 1 in 256, and never in
world 1. The rule now replies only to a packet the relay delivers (`RSOR.delivers`,
`RSOR.replyOf`): one that names a recipient and carries no reply block. The self-test asks the
sender in both worlds (`runBackwardSenderReply`); neither answers. NIKE Sphinx has the same
rule; with the old one its sender answered 10 of 3000 runs (`runSenderReply`).

A reply's layers are the layers of a packet over the backward path, with only the payload
swapped for the reply's (`formBack_fst`), and the reply block in the sender's payload is the
header of the first of them (`surb_fst`). So the lemmas about keyed layers proved for TLU→
apply to replies as they stand.

The machinery that puts one honest relay behind an oracle takes the relay's role as a
parameter, and `KEMSphinxProp.lean` writes any property's game as a keyed game for any of the
three roles. SLU← needs it for the sender as well as the relay.

Proved so far, in `KEMSphinxSLU.lean`: both worlds as their draws with the relay's seed drawn
on its own (`backward_play_false_evalDistEq`, `backward_play_true_evalDistEq`); both worlds
around the relay's ciphertext, at the exit and on the backward path (`backView0`,
`backView1`); and the first reduction, `backwardUnlinkable_le_keyedIdeal`: the advantage is at
most the chance of a bad draw in each world, the KEM and KDF terms for each world, and the
distance between the two keyed games with uniform keys at the relay.

World 1 reads the adversary's onion through three things only: its first layer, the header of
the reply's layer at the relay, and the header of its last forward layer (`world1With`,
`world1_eq`, for any scheme).

The MAC step is proved for both worlds (`backward0_keyedIdeal_sub_tagged_le`,
`backward1_keyedIdeal_sub_tagged_le`): the relay may answer its ciphertext under its own header
only, at the cost of a forgery. The bytes its MAC covers are the same in both worlds (`backM0`),
since both show the adversary's own onion. The closed form of a keyed layer that this needs is
stated for any route (`routeK_parts`), so one lemma serves the forward path and the reply.

A header does not use the payload cipher (`pktFn_header`, `layerF_header`). On the backward
path the relay's payload key never encrypts anything the adversary sees: the sender builds the
reply header over a dummy payload and drops that payload. So the keyed view builds the reply
header with the identity in place of the cipher, and does not depend on the relay's payload key
at all.

The payload cipher step is proved for both worlds (`backward0_payload_le`,
`backward1_payload_le`). At the exit the sender's block is the body of the last forward layer,
as in TLU→. On the backward path there is no sender's block; the relay only decrypts.

The machinery that puts a relay behind an oracle, and the payload cipher and keystream steps,
are stated once for any property and any of the three roles (`KEMSphinxProp.lean`,
`propPayloadGame`, `propStreamAdv`). TLU→ uses the same ones.

The keystream step is proved for both worlds (`backward0_stream_le`, `backward1_stream_le`),
and the steps so far are put together in `backwardUnlinkable_le_uniform`: the advantage is at
most the bad draws, the KEM and KDF terms, a MAC forgery, the one-block cipher advantage and
the keystream generator's advantage, each for both worlds, and the distance between the two
worlds played from a uniform keystream at the relay.

All of this is stated for `backwardWith W`: SLU← with any onion `W` sent on by the relay in
world 1 (`BackSwap`, `world1Of`). The relay's keys do not enter that onion, so the steps above
do not look at it. SLU← itself is `backwardWith freshSwap` (`backwardUnlinkable_eq_with`).

The plan for the rest uses a world in between, world 1′: the relay sends on an onion that is
built like a reply layer, a header over the rest of the backward path with a uniform payload.

- Worlds 1 and 1′ differ in the onion sent on only. Its last layer is the sender's, so this is
  the same chain as above around the sender's ciphertext.
- Worlds 0 and 1′, with the relay's keys used up, should be the same game after relabelling
  the relay's keystream, as in the last comparison of TLU→. At the exit this also needs the
  cipher under the reply's payload key.

Proved so far for the first: the triangle inequality through world 1′
(`backwardWith_advantage_le`), and in `KEMSphinxSLUSender.lean` the whole chain around the
sender's ciphertext for both onions (`swapPair_le_uniform`): the advantage in telling them
apart is at most the bad draws, the KEM and KDF terms, a MAC forgery, the one-block cipher
advantage and the keystream generator's advantage, each for both onions, and the distance
between the two games played from a uniform keystream at the sender. World 1′ is `replySwap`.

That last distance is bounded too (`swap_uniform_le`): the two games played from a uniform
keystream at the sender are the same run, draw for draw, off an explicit event
(`swapFinalGood`). The pieces:

- With the head of the sender's keystream shifted, the fresh onion's last header bytes are the
  reply header's (`lastShift_spec_of_size`, `lastLayer_swap`). The two end in different
  commands, a recipient and a reply.
- The layers in front split into a header that reads the header only and a payload under the
  hops' payload keys (`wrapUp_append`, `KEMSphinxWrap.lean`). So the fresh onion's block, under
  the hops in front, is the uniform payload of world 1′ (`evalDistEq_payUp`).
- The sender replies to neither under the header it refuses (`lastLayer_noreply`): a reply
  packet is not read for a SURB, and the fresh onion's block carries none.

The event asks that the hops in front have ciphertexts of a ciphertext's length, that the
fresh onion's payload has a payload's length, and that the block given for a changed payload
does not begin with the zero tag.

Not proved yet: the second point, worlds 0 and 1′; and bounds on the explicit events. What the
second point needs, as far as worked out:

- At the exit the relay answers the SURB in its payload. The reply's header is a fresh reply
  header by renaming the challenger's randomness. Its payload is the answer under the reply's
  payload key, which is uniform and used once: one more cipher step.
- On the backward path the relay sends on the reply's next layer. The relay's header in the
  two worlds agrees after shifting the head of its keystream by the difference of two routing
  informations of a hop in the middle of a path (TLU→ had a hop at the end of one). The next
  layer is a first layer over the rest of the path once the tail of the keystream stands for
  that layer's padding.
- On the backward path in world 0 the relay hands on what the ideal cipher's decryption gives.
  That is a uniform block when the block the cipher would decrypt to is uniform
  (`evalDistEq_ite_fresh`), so world 0 has to draw that block; then `oracle_draw` moves the
  draw to the front.

Proved so far for the second point, on the backward path (`KEMSphinxSLURelay.lean`):

- World 0's randomness is a mix of world 1′'s two draws (`backMix`): the seeds up to the relay
  from the first, the later seeds and the first bytes of the padding from the second
  (`joinDraw`). With the keystream shifted (`backShift`), the relay has the header it has in
  world 1′, and the layers after it are the layers over the rest of the path
  (`backShift_spec`).
- The mix and the shifted keystream are uniform (`evalDistEq_backShift`). The tail of the
  shifted keystream is a region of the second draw's padding, which nothing else reads
  (`evalDistEq_headRegion`).
- A relay processes a header once, so the ideal cipher's one answer under its header is a
  fresh block (`withDec_fresh`).

- World 1′'s patched relay is world 0's relay handing on one fresh block
  (`headerRelays_back_eq`), so at the relabelled draws the two games are the same
  (`backRun_evalDistEq`).
- For fixed keys and challenge the two games differ by at most the chance that the reply's
  next layer or the first layer over the rest of the path cannot be built (`back_fixed_le`,
  `backGoodF`).

At the exit the relay builds the reply from the SURB in its payload: the reply's payload is one
encryption of the adversary's message under the SURB's payload key. The adversary picks that
message during the game, so this step rests on a second cipher assumption, `oneEncExp`: one
encryption asked during the game, under a uniform key and IV, against a uniform block. David
agreed to this assumption on 2026-11-26. The adversary of `oneEncExp` first prepares the game it
will play, without the key, and then asks its one encryption.

Proved for the exit, for fixed keys and challenge:

- A relay that asks an oracle only for its reply under one header asks once (`viaEnc_once`);
  the relays' log holds no onion twice (`propDraw_log_nodup`).
- Under its own header the exit relay delivers the sender's message and replies with one
  encryption (`exitRelay`, `replyOf_body_enc`), so it is a relay asking for one encryption
  (`headerRelays_exit`). Nothing else in world 0's game reads the SURB's payload key
  (`exitRun0_eq`; `world0_patch` for the header the sender refuses).
- World 0 is the encrypt-once game with the cipher, up to the draws that are not good
  (`exit_real_le`, `exit_real_evalDistEq`). Good (`exitGood`): the onion and the reply can be
  built, the sender's payload has a payload's length, and the block for a changed payload has
  no zero tag.
- The world where an onion is sent on is the encrypt-once game with a uniform block, up to the
  draws that are not good or for which the onion sent on cannot be built (`exitRun1_eq`,
  `exit_ideal_le`).

The bound over the whole game (`backUniform_le`): after the first phase the challenge says
whether the relay is the exit or on the backward path. The encrypt-once adversary (`exitAdv`)
plays the exit game through its oracle in the first case and world 0 in the second. A hybrid
that plays the sent-on world at the exit and world 0 elsewhere is compared with world 0 by the
exit bounds and with the sent-on world by `back_fixed_le`. The lemma for a common prefix uses
the prefix's support (`abs_prEvent_bind_sub_le_support`), because the log is well-formed only
for draws the game can make.

The statement for SLU← is `backwardUnlinkable_le`, for `backwardWith freshSwap`, which is
`backwardUnlinkable` (`backwardUnlinkable_eq_with`). Its right side has three groups of terms:

- telling the fresh forward onion from an onion built like a reply layer, at the sender
  (`swapPair_le`);
- replacing the honest relay's keys (`backwardUnlinkable_le_uniform`): bad draws, the cost of
  the keys (KEM and KDF), a MAC forgery, the one-block cipher advantage and the keystream
  generator's advantage, each for both worlds;
- the two worlds from a uniform keystream (`backUniform_le`): the advantage against one
  encryption, and three events of draws that are not good.

Not proved yet: bounds on the explicit events (bad draws, draws that are not good). Each is a
statement about the KEM not failing, a layer being built, or a uniform block having a zero tag.

The events of the SLU← bound are being reduced to the KEM in `KEMSphinxSLUEvents.lean`. So
far: a bad draw of world 0 has a seed that is not reliable (`prEvent_backBad0_le`), and a bad
draw of world 1 has one on the path the honest relay's layer is on (`prEvent_backBad1_le`).
The same for the sender's two keyed games: a bad draw has a seed that is not reliable, the
sender's or one on the rest of the backward path (`prEvent_swapFreshBad_le`,
`prEvent_swapReplyBad_le`).
Their draws that are not good reduce the same way (`prEvent_not_swapFreshGood_le`,
`prEvent_not_swapFreshGoodP_le`, `prEvent_not_swapReplyGood_le`; `swapSeedsGood` names the
seeds that must be reliable).
A draw of the sender's last comparison is not good with the chance of one payload tag
(`prEvent_not_swapFinalGood_le`): a hop of a route has a ciphertext of the right length
whatever its seed (`kemHopCt_route_size`), so only the zero-tag event is left.
The relay's draws that are not good, in both worlds and for the payload step, have a seed
that is not reliable among the relay's and those of the hops in front of it (`relaySeedsGood`,
`backGoodAt_of_reliable`, `prEvent_not_backGood0_le` and the three like it).
The backward-path term of the last comparison is zero: there the draws are always good,
because the two layers they ask for always build (`backGoodF_holds`,
`prEvent_not_backGoodF_eq_zero`).
A forward layer builds when the sender's payload has the forward payload's length; the lemmas
take that as a fact about the geometry (`hsurb`: room for a reply block). The other event terms
of `backwardUnlinkable_le` are not reduced yet.

## STI↔ for KEM Sphinx

World 0 shows the layer of the adversary's onion at forward position `pos`; world 1 shows the
first layer of an onion with the same message over the rest of the forward path and the
backward path up to its honest relay. Two honest relays hide the difference.

- The relay before `pos`. Its layer is not shown, so its ciphertext is hidden, and its keys
  reach the shown layer through the tail of its keystream only. With that keystream uniform
  the shown layer is a first layer over the rest of the path: the same facts as for the
  backward path of SLU← (`layerPast_drop`, `fillerAtF_target`), for the forward path.
- The honest relay on the backward path. The SURB in the payload carries the reply's first
  header, built over the whole backward path in world 0 and over the path cut at the honest
  relay in world 1. The two headers differ in what that relay reads, and it answers nothing to
  the reply's layer in either world. This is the keyed game at that relay, as in TLU→.

In Lean so far (`KEMSphinxSTI.lean`, `KEMSphinxTLUNext.lean`):

- The triangle through a world in the middle (`tailPair_advantage_le`), and that
  world for KEM Sphinx (`tailMid`, `tailMidWorld`): the first layer over the rest of the forward
  path with a forward draw of its own, around the adversary's payload.
- For any keyed game that reads the node's keys through their header keystream only, and never
  shows a tag under its MAC key: the node may reject the challenge ciphertext for a MAC forgery
  (`keyedIdeal_sub_reject_le`), then the keystream step (`keyedReject_eq_prg`), together
  `keyedReal_sub_uniform_le`. The TLU→ lemmas for the original's hidden layer are corollaries.

The first half is `tailFirstHalf_le`: world 0 and the middle world are told apart with at most
`tailHalfCost`. The challenge lets the relay before the shown layer be either honest role
(`.relay` or `.back`), and the keyed game fixes the role before the adversary chooses. So the
step is done once per role, through a hybrid (`tailHyb`) that shows the middle world when that
relay has a role already handled and world 0 otherwise. One step (`tailStep_le`):

- Each hybrid world is the keyed game with the real keys, off the bad draws
  (`tail_sub_keyedReal_le`; the bad draws are `hybBad`: the relay's key pair is not a key pair,
  or the encapsulation to it fails or cannot be undone).
- `keyedReal_sub_uniform_le` takes each side to a uniform keystream.
- From a uniform keystream the hybrid world is the next one (`evalDistEq_tailViewU`), by the
  relabelling of the forward path (`fwdShift_spec`, `evalDistEq_fwdShift`).

`tailStepCost` is one side of a step: the bad draws, the replacement of the relay's keys (KEM
and KDF), a MAC forgery, and the keystream generator's advantage. `tailHalfCost` is four of
them. The chance of a bad draw is `seedFailure`, the chance that a uniform seed is not reliable
for the KEM (`prEvent_hybBad_eq`): a quantity on the KEM alone, zero for a KEM that is perfectly
correct. An encapsulation to a relay's key does not fail (`kemEncap_key`), by the KEM type's law
`encap_derived`, which every KEM here proves without an axiom.

The second half is `tailSecondHalf_le`: the middle world and world 1 are told apart with at most
`tailBackCost`. Both worlds have one shape (`backWorld`): the first layer of a request, with
the honest backward relay answering nothing to the reply's layer at its position. The request
of the middle world has the whole backward path (`midReq`), that of world 1 the path cut at the
relay (`cutReq`). For either request:

- The world is the keyed game at the honest backward relay with the real keys, off the bad
  draws (`back_sub_keyedReal_le`, `backBadK`).
- The keys are replaced by uniform ones (`keyedChain_le`), and the relay answers its ciphertext
  under the reply layer's own header only, for a MAC forgery and the draws that are not good
  (`back_keyedIdeal_sub_tagged_le`, `backGoodK`).
- The payload cipher and keystream steps take the game to a uniform keystream
  (`back_tagged_sub_stream_le`, `backStream_ideal_evalDistEq`, `backUGame`).

From a uniform keystream the two games are the same game (`backUGame_cut`). With the seeds in
front of the relay swapped and the keystream shifted (`shiftStream_path`, as in TLU→), the
world and the relays of the whole path are those of the cut path (`tailBackViewU_shift`,
`tailBack_relays_shift`). The relay's answer under its own header does not matter: the patch
hides what it forwards, and it replies to neither header, one being of a hop in the middle of a
path and the other ending a reply's path. The comparison needs the reply's next layer to be
built, and it always is: a layer past a keyed hop builds for any draw and keystream
(`layerPast_builds`). When the honest relay is the last backward hop the two requests are
the same (`cutReq_eq_midReq`).

`backSideCost` is one side: the bad draws, the replacement of the relay's keys, a MAC forgery,
the one-block advantage against the payload cipher, the keystream generator's advantage, and
the draws that are not good (twice). `tailBackCost` is two sides.

The statement is `tailIndistinguishable_le`: the advantage in STI↔ is at most `tailBackCost`
plus `tailHalfCost`. Its events, as far as they are reduced to the KEM:

- the first half's bad draws are exactly a seed that is not reliable (`seedFailure`,
  `prEvent_hybBad_eq`);
- a draw of the second half that is not good has a seed that is not reliable, the honest
  backward relay's or one of a hop in front of it (`prEvent_not_backGoodK_le`);
- a bad draw of the second half has a seed on the backward path that is not reliable
  (`prEvent_backBadK_le`): with reliable seeds every layer builds (`builds_of_reliable`,
  `Builds.layer`);

The first layer over a route always builds (`layer_zero_builds`, in `KEMSphinxBuilds.lean`): a
packet fails to build on a wrong size, a failed encapsulation, or commands that do not fit a
hop, and a route of the scheme has none of these. So "a layer does not build" is not an event
of its own for a first layer; what is left is seeds that are not reliable.

## NIKE Sphinx: what is proved, and the plan for the RSOR properties

Proved before this work, from the original Sphinx paper (Danezis, Goldberg): correctness of
wrapping and unwrapping (`NIKESphinxTheorems.lean`), integrity (§4.2, `Integrity.lean`),
wrap-resistance (§4.3, `WrapResistance.lean`) and indistinguishability (§4.4,
`Indistinguishability.lean`), each with the limits its file states.

From the RSOR paper (Scherer, Weis, Strufe), RSOR-Correctness is proved: NIKE Sphinx is a value
of `Protocols.RSOR.Scheme` (`NIKESphinxRSOR.scheme`). TLU→, SLU← and STI↔ are not proved yet.

The KEM Sphinx proofs do not carry over. There each hop has its own seed, and a proof replaces
one hop's keys in a game around that hop's ciphertext. NIKE Sphinx has one secret per path,
blinded hop by hop: the group element a relay receives is the sender's element raised to the
blinding factors of the hops in front, and each blinding factor is derived from that hop's
shared secret. So the layers after an honest relay depend on the sender's secret and on the
honest relay's own blinding factor.

The paper proves Sphinx secure in two steps (its §4.3 and §4.4):

1. The "Sphinx RO-KEM" satisfies a game it calls Sphinx-KEM-IND-CCA, under Gap Diffie–Hellman
   with random oracles. In that game the adversary names the other relays' keys and the honest
   relay's position. The challenger, which holds the sender's secret, hands out the first group
   element and every hop's keys and blinding factor. At the honest relay's hop the keys and the
   blinding factor are the real ones or uniform ones, and the later hops are derived from
   whichever was used. The adversary has the honest relay's decapsulation oracle.
2. TLU→, SLU← and STI↔ follow from that game with a MAC, a PRG and a PRP.

We have no random oracles: hop keys come from a KDF. So step 1 cannot be proved here as the
paper proves it. The plan is to state the game of step 1 for our NIKE and KDF and take its
advantage as the term the theorems carry, as KEM Sphinx carries the KEM and KDF terms. Gap
Diffie–Hellman is then the assumption behind that term, by the paper's Theorem 3.

In Lean so far (`NIKESphinxHeaderFn.lean`): a packet as a function of each hop's group element,
header keystream, tagging function and payload encryption (`nikePktFn`, `groupElem`). A packet
`newNIKEPacket` builds is that function's, on the group elements and keys of its blinding chain
(`createHeader_hdrTrace`, `newNIKEPacket_pktFn`); the self-test compares the two on random
inputs (`runPacketFn`).
`hopKeysWith` is the hops' keys with one hop's replaced and the later hops derived from the
replacement; with the hop's own keys it is the sender's keys (`hopKeysWith_hopKey`). The
self-test builds a packet from replaced keys and checks that the relays in front still forward
it and the relay at the replaced hop rejects it (`runReplacedKeys`).

The game is `keyGame` (`NIKESphinxGame.lean`), and `keyAdvantage` is the term the properties
will carry. The adversary, with the honest relay's oracle, chooses a path and the relay's place
on it; the challenger puts the relay's key there, draws the sender's secret, and hands over the
sender's group element and every hop's keys. In one world the keys are the sender's. In the
other the relay's four keys and the seed of its blinding factor are uniform, and the hops after
it are derived from that factor. The relay answers the element that reaches its place with the
keys handed over for it (`procImplK`), where the paper's relay refuses that element; the
adversary holds those keys, so it could answer itself. That the two forms are equivalent is not
proved in Lean, and neither is the paper's Theorem 3 (Gap Diffie-Hellman with random oracles
gives the game): our keys come from a KDF, not a random oracle.

A relay's processing now has a form that takes the hop's keys from a function of the group
element (`unwrapNIKEWith`, `procWith`); the relay is that form on the keys it derives
(`unwrapNIKE_eq_unwrapNIKEWith`, `unwrap_eq_procWith`). The self-test checks that a relay
handed the replaced keys for the arriving element accepts the layer, and does not use them for
another element.

The game's real world is the honest relay: for the element that reaches its place, a relay
derives the keys the sender derived for that place (`groupElem_eq`, `relayKeys_groupElem`), so
handed the sender's keys it answers as it does with its own key (`keysExcept_hopKeys`,
`procImplK_hopKeys`). Every blinding factor decodes, by a law of the NIKE type. An adversary
that names a place off the path loses in both worlds.

A sender's packet is `nikePktFn` on the sender's hop keys and the elements they blind
(`layer_zero_pktFn`), and `nikePktFn` reads what it is given for the path's hops only
(`nikePktFn_congr`). So the onion of the RSOR games is one function of the hop keys, and the
game's two worlds differ in the keys alone. This is not yet used: the reduction of TLU→ to the
game is the next step.

The reduction, for any property and any of the three honest roles (`NIKESphinxProp.lean`): the
relay whose keys the game replaces answers through an oracle (`viaOracle`, `viaOracle_honest`),
and an adversary of the property gives an adversary on the key game (`propAdvOf`), which draws
the other two honest relays' keys and builds the world it shows from the first group element
and the hops' keys. Played by that adversary, the key game's real world is the property's game
against the honest relays on the world built from the sender's own keys
(`keyGame_true_propAdvOf`). What is left for TLU→ is to give the worlds of that game as such
views, and then the steps on the replaced keys: MAC, keystream, payload cipher.

For TLU→ so far (`NIKESphinxTLU.lean`): the first layer of a request's onion as a view of the
forward path's first group element and its hops' keys (`onionOfKeys`), which on the sender's
own keys is the sender's onion when that onion builds (`onionOfKeys_real`). A game of a
property may be played with the honest relay's key pair drawn first (`play_evalDistEq_honAt`).
World 0 of TLU→ is the key game's real world for this view, played by `forwardAdv`, except on
draws for which the adversary's onion cannot be built (`play_false_sub_keyGame_le`, the event
`forwardBad`). The key game's other world is written out as its draws and the adversary's
second phase against a relay that answers the element of its place with the replacement
(`propIdealOf`, `keyGame_false_evalDistEq`, `viaOracle_relayImpl`). So world 0 played with the
honest relay's keys replaced differs from world 0 by at most `keyAdvantage` for `forwardAdv`
and the chance of that event (`play_false_sub_ideal_le`). The event is not bounded yet;
whether a NIKE Sphinx packet builds should depend on the path and the geometry alone.

The steps on the replaced keys are stated for a relay whatever its packet format, so that NIKE
Sphinx and KEM Sphinx can share them. The first is the MAC step (`RelayMac.lean`,
`gameAll_sub_gameOnly_le`): a relay that answers challenge packets with keys the game holds may
answer them under the challenge header only, at the cost of a forgery against the MAC. The
format enters through two facts: what the relay accepts verifies, and under the challenge
header it uses the MAC key for that header's tag only. The NIKE relay has both facts
(`procWith_forgery`, `procWith_const` in `NIKESphinxGame.lean`), and the key game's other
world, played by `propAdvOf`, is the step's first game: the relay answers a packet with the
element of its place by the replaced keys and any other with its own key
(`keyGame_false_evalDistEq_gameAll`). Applied to it, the step says: if the world shown uses the
honest relay's MAC key for one tag only, the relay may answer the element of its place under
the challenge header only, at the cost of a forgery against the MAC and the chance of a draw
that is not good (`keyGame_false_sub_gameOnly_le`). A property has to say how its view is built
from the one tag. For that: a header uses a hop's tagging function once, on the bytes `hdrMsg`,
which do not depend on that function (`nikeHdrTrace_tagAt`, `nikePktFn_tagAt`), and two
replacements with the same blinding factor give the same keys off the replaced hop
(`hopKeysWith_congr`). So the onion uses the replaced hop's MAC key for one tag only
(`onionOfKeys_tag`), and the MAC step holds for world 0 of TLU→ (`forward_ideal_sub_only_le`):
with the honest relay's keys replaced, the relay may answer the element of the adversary's
onion under that onion's header only, at the cost of a forgery against the MAC and the chance
that the bytes its tag covers do not have a header's length. That chance is not bounded yet; it
should be zero when the onion builds. KEM Sphinx still has its own copy of the step
(`KEMSphinxKeyedMac`).

The second shared step is the payload cipher's (`Protocols/RSORPayload.lean`, `PayloadGame`,
`PayloadGame.exp_eq`): a game in which an honest relay decrypts under one header only is the
one-query game of the payload cipher, for any scheme of the RSOR games. It rests on
`viaDec_decOnce`, which was already stated for any scheme. Not yet used: world 0 of NIKE
Sphinx after its MAC step has still to be written as such a game, and KEM Sphinx has its own
copy (`KEMSphinxPayload`). For that, the NIKE relay's unwrap takes the payload decryption as a
function (`unwrapNIKEDec`); the form with a cipher is defined from it, so the body exists once.
A packet uses a hop's payload encryption once, on the block the hops after it left
(`encTrace_encAt`, `nikePktFn_encAt`), as it uses the hop's tag once.
A relay decrypts one block, the packet's payload (`unwrapNIKEDec_congr`, `procD_congr`), and a
relay with a cipher is the relay that decrypts by the cipher (`procWith_eq_procD`).
A relay that answers one element under one header only decrypts, under that header, the
onion's payload with its payload key, and under any other refuses the element
(`onlyAnsH_join`, `procWith_join`).
The honest relays' oracle, with one relay answering one header, is the one-decryption oracle of
the payload game (`oracle_onlyAnsH`, for any answer under that header). The onion uses the relay's payload key for one encryption,
of `onionBlock` (`onionOfTag_enc`), and reads that key nowhere else (`onion_payloadKey`); a
relay handed its payload's decryption does not read it either (`procD_payloadKey`). The second
phase against a relay that answers one header is the second phase against the one-decryption
oracle (`relayImpl_onlyAnsH_run`, `relayImpl_onlyAns_run`), and the hops' keys with and without the relay's payload key
agree off the relay (`payKeys`). World 0 after its MAC step has a payload game, `forwardPay`,
and draw by draw it is that game with the cipher (`forwardPay_run`), on draws where the bytes
under the relay's tag have a header's length and carry the relay's element, and the block the
relay encrypts has a payload's length (`payGood`). With the draws reordered so the payload key
and IV come first, this gives the payload step for world 0 (`forward_only_sub_ideal_le`): world
0 after its MAC step differs from its payload game with an ideal cipher by the one-query
advantage of `forwardPay`'s adversary against the payload cipher, and the chance of a draw
that is not good. The honest relays' logs after the first phase are well-formed
(`propDraw_log_wf`), which the cipher game needs.

For the keystream step: a relay uses its header key and IV for one keystream, so with that
keystream handed to it the relay does what it does with the stream cipher
(`unwrapNIKEDec_stream`, `constStream`, `procD_stream`), and the onion reads the relay's
header key and IV through its keystream only (`onion_streamKey`). So the payload game of world
0 with the ideal cipher is the real experiment of the keystream generator `keystreamPRG` for
the adversary `forwardStreamAdv`, which plays world 0 from the keystream it is given
(`strRun_eq`, `payExp_false_evalDistEq_prg`).

**World 0 of TLU→ for NIKE Sphinx, so far.** Each line is a proved bound:

- world 0 to the key game's real world: the chance the onion does not build
  (`play_false_sub_keyGame_le`);
- real keys to replaced keys: `keyAdvantage` of `forwardAdv` (`play_false_sub_ideal_le`);
- any header to the challenge header only: a forgery against the MAC, and the chance that the
  tagged bytes do not have a header's length (`forward_ideal_sub_only_le`);
- from there to world 0 played from a uniform header keystream, an ideal payload cipher and one
  header: the cipher's one-query advantage, the keystream generator's advantage, and the chance
  of a draw that is not good (`forward_only_sub_stream_le`).

Added up, this is `forward_world0_le`. The events are not bounded: they should all be zero
when the request's onion builds and its body has a payload's length.

**The steps after the key replacement are stated for any world** (`FwdWorld`: the request
shown, its randomness, the relay's patch and the path whose keys are replaced). World 0 is
`fwd0`, the adversary's own request and no patch. World 1 is `fwd1`: the replacement that ends
at the honest relay, and the relay patched around the replacement's layer there. The chain
above holds for either (`forward_chain_le`), so world 1 has its first chain down to its draws
too (`play_true_evalDistEq`, `play_true_sub_keyGame_le` with the event `shortBad`,
`forward_world1_le`).

**World 1's hidden layer.** In world 1 the relay answers the replacement with what the
original would have produced, so the patch still holds the original's next layer and reply,
built from the original's own keys. The KEM proof calls this the hidden layer. It takes four
steps (`NIKESphinxTLUNext.lean`):

1. World 1 after its first chain is the key game's real world for an adversary on the original
   onion, `nextAdv`, which builds the original's next layer from the keys the game hands it.
   Proved (`prgIdeal_fwd1_sub_keyGame_le`), off the draws where the bytes under the relay's tag
   do not carry the replacement's element or the original onion cannot be built (`nextBad`).
   Its parts: the adversary's second phase on a draw (`nextPost_real`), the patch built from
   the handed keys on the original's own keys (`patchWith_real`), and the two games over the
   same draws (`keyGame_true_nextAdv`, `prgIdeal_fwd1_evalDistEq`).
2. Replace the relay's keys for the original. This costs `keyAdvantage` of `nextAdv`, by
   definition.
3. The relay refuses the original's element, which the adversary is never shown. Proved
   (`keyGame_false_nextAdv_sub_le`): it costs the chance that the adversary sends a packet
   carrying that element. The bound is stated for any relay (`Relay.gameHand_sub_le` in
   `RelayMac.lean`), and the key game's other world for `nextAdv` is such a relay game
   (`keyGame_false_nextAdv`, `nextGame`). The chance is carried, not bounded.
4. Replace the keystream through which the next layer reads the replaced header key and IV.
   Proved (`nextGame_none_evalDistEq_prgReal`): the game after step 3 is the real experiment
   of the keystream generator for an adversary, `nextStreamAdv`, that builds the original's
   next layer from the keystream it is given. No event is carried: a header built from any
   hops' keys has a header's length (`nikeHdrTrace_size`, `keysHdr_size`). Going to uniform
   bytes then costs that generator's advantage, by definition. The next layer still reads the
   replaced MAC key and blinding seed, as two more uniform draws.
   It rests on (`NIKESphinxPeel.lean`): a relay's `peel` on a header and a payload is the
   header from its keystream and blinding factor, and the payload decrypted (`peel_append`,
   `peelHdr`); so a layer of a packet is its header peeled and the block the hops after it
   left, each hop's decryption undoing its encryption (`peels_append`). Hence the layer after
   a hop reads that hop's header key and IV through its keystream only and does not read its
   payload key (`onionOfKeys_succ`, `nextOfStream`, `nextOfStream_congr`).

**The last comparison of the two worlds is not proved.** After the steps above, world 0 is
played from a uniform keystream for the relay's hop of the original onion, and world 1 from
one for the replacement and one for the original's next layer. The plan, and what is proved
for it:

1. A peeled header in closed form, for any keys. Proved (`NIKESphinxPeel.lean`): one peel
   undoes the sender's step for that hop (`peelHdr_step`, from `cascading_xor_step`); the
   padding after a hop is the tail of its keystream with the padding in front folded in
   (`padAt_step`, `padAt_size`); a hop before the last names the next hop and its tag
   (`nikeFragment_parse`). So peeling the header of a layer gives the header of the next
   (`layerHdr`, `peelHdr_layerHdr`, `hdrPeels_layerHdr`), and the original's next layer is the
   header of layer `j + 1` of the header function with the relay's keystream put in, with the
   block the later hops left (`nextOfStream_layerHdr`). Of the hops in front it reads their
   padding only.
2. The relay's answer in world 0 in the same closed form. Proved for it: what a relay
   forwards, explicitly (`procD_forward`, `procD_forward_append`), and so a relay given a
   layer before the last forwards the next layer's header and the payload decrypted
   (`procD_layerHdr`), from the bytes under a layer's tag (`hdrMsg_struct`, `peel_bytes`,
   `peel_cmdBuf`). Not proved: world 0's game written with it.
3. The padding of the hops in front is absorbed by the tail of the uniform keystream, and the
   relay's header on a path that goes on becomes its header on a path that ends at it by
   xoring a fixed mask into the keystream's head. Not proved. The byte lemmas for this exist
   in `KEMSphinxPad.lean` and `KEMSphinxTLUFinal.lean` and do not depend on the KEM; they are
   to be shared, not copied.
4. The later hops' keys and elements come from the sender's secret and the replaced blinding
   factor, in both worlds, but world 1 uses an independent secret for the original. That the
   two are distributed alike is a property of the NIKE (blinding by a uniform factor), to be
   stated as a game whose advantage the bound carries. Not stated yet.

SLU← and STI↔ are not started for NIKE Sphinx.

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
