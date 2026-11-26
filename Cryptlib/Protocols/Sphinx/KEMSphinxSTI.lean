/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLURelay

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
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # STI↔ for KEM Sphinx

World 0 of STI↔ shows a layer of the adversary's onion from a forward position on; world 1
shows the first layer of an onion over the rest of the forward path. A layer from a position on
is a layer over the rest of the path, with the filler there as the rest's padding. -/

section RestOfForward

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

omit cipher macS in
/-- The fillers from position `j` on are the fillers built on the rest of the path from the
filler at `j`. -/
theorem fillerAt_drop (hops : Array PathHop) (seeds : Array (Vector UInt8 32))
    (filler : ByteArray) (j i : ℕ) :
    RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i)
      = RSOR.fillerAt kem kdfS streamS geom (hops.extract j hops.size)
        (seeds.extract j seeds.size) (RSOR.fillerAt kem kdfS streamS geom hops seeds filler j)
        i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i + 1) = _
    simp only [RSOR.fillerAt]
    rw [ih, extract_tail_tail hops j i, extract_tail_tail seeds j i]

/-- **A layer from a position on is a layer over the rest of the path**, when the seeds from
there on are the rest's seeds and the filler there is the rest's padding. -/
theorem layer_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (d d' : RSOR.Draw geom) (payload : ByteArray) (j i : ℕ)
    (hj : j ≤ R.hops.length)
    (hseeds : (d.1.toArray.extract 0 (RSOR.path kem R last).size).extract j
        (d.1.toArray.extract 0 (RSOR.path kem R last).size).size
      = d'.1.toArray.extract 0 (RSOR.path kem (R.drop j) last).size)
    (hfill : RSOR.fillerAt kem kdfS streamS geom (RSOR.path kem R last)
        (d.1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector d.2).extract 0
          ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j
      = (ofVector d'.2).extract 0
        ((geom.nrHops - (RSOR.path kem (R.drop j) last).size)
          * geom.perHopRoutingInfoLength)) :
    RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload (j + i)
      = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop j) last) d' payload
        i := by
  unfold RSOR.layer
  dsimp only
  rw [fillerAt_drop, hfill,
    extract_tail_tail (d.1.toArray.extract 0 (RSOR.path kem R last).size) j i,
    extract_tail_tail (RSOR.path kem R last) j i, hseeds,
    path_extract_drop kem geom R last j hj]

end RestOfForward

end Cryptlib.Protocols.Sphinx.KEMSphinx
