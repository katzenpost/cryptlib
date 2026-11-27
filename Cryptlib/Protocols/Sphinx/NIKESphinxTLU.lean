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
open Cryptlib.Protocols.Sphinx.KEMSphinx (keysKs keysTag keysEnc)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split)
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
def onionOfKeys (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (ks : List HopKeys) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
      (RSOR.path nike q.fwd [.recipient q.receiver])
      (RSOR.body nike macS kdfS streamS geom q r) with
  | some pkt => split geom pkt
  | none => default

variable {nike geom} in
/-- The randomness with the forward path's secret replaced. -/
def setKey (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) :
    RSOR.Randomness nike geom :=
  ((d, r.1.2), r.2)

/-- **On the sender's own keys it is the sender's onion**, when that onion builds. -/
theorem onionOfKeys_real (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (d : Vector UInt8 nike.privateKeySize) (pkt : ByteArray)
    (h : RSOR.layer nike cipher macS kdfS streamS geom
      (RSOR.path nike q.fwd [.recipient q.receiver]) (setKey r d).1
      (RSOR.body nike macS kdfS streamS geom q (setKey r d)) 0 = .ok pkt) :
    onionOfKeys nike cipher macS kdfS streamS geom q r
        (groupElem nike ((nike.decodePrivateKey d).getD default)
          (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
            (RSOR.path nike q.fwd [.recipient q.receiver])
            (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray 0)
        (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
          (RSOR.path nike q.fwd [.recipient q.receiver])
          (RSOR.path nike q.fwd [.recipient q.receiver]).size)
      = RSOR.form nike cipher macS kdfS streamS geom q (setKey r d) q.first := by
  have hf : RSOR.form nike cipher macS kdfS streamS geom q (setKey r d) q.first
      = split geom pkt := by
    unfold RSOR.form
    rw [show ((q.first : Fin q.fwd.hops.length) : ℕ) = 0 from rfl, h]
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

end Onion

end Cryptlib.Protocols.Sphinx.NIKESphinx
