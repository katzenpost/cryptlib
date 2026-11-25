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

Not proved yet: the bound on that last distance by the MAC, the stream cipher and the payload
cipher; SLU← and STI↔ for KEM Sphinx; all three for NIKE Sphinx. The games for a MAC used once
(`MAC.forgeExp`) and a payload key used for one block (`WideBlockCipher.oneQueryExp`) are
stated for that work and not yet used.

## Checks

`make test` runs every suite, including the Katzenpost vectors and honest runs of the three
games in both worlds. `make axioms` is the axiom check above. A security bound has no
executable test; its check is the honest run of its game and a comparison with the paper.
