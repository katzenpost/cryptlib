/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxProp
import Cryptlib.Protocols.Sphinx.KEMSphinxTLU

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

/-! # Backward layer unlinkability (SLU←) for KEM Sphinx

A reply's layers are the layers of a packet over the backward path, with the payload as the
relays before left it (`RSOR.formBack`). So the honest relay's layer of a reply is keyed by one
seed of the backward path's draw, as its layer of a forward onion is keyed by one seed of the
forward path's. -/

section Backward

open Cryptlib.Protocols.RSOR (Role)

variable (geom : Geometry)

/-- The challenger's randomness with the seed for backward position `j` replaced. -/
def setSeedBack (r : RSOR.Randomness geom) (j : Nat) (s : Vector UInt8 32) :
    RSOR.Randomness geom :=
  (r.1, (r.2.1.1.setIfInBounds j s, r.2.1.2), r.2.2)

/-- Drawing the challenger's randomness and a seed, and putting the seed at backward position
`j`, is drawing the randomness. -/
theorem evalDistEq_setSeedBack {δ : Type} (j : ℕ) (hj : j < geom.nrHops)
    (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (setSeedBack geom r j s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  have hg : Function.Bijective (Function.uncurry
      fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) =>
        (setSeedBack geom r j s, r.2.1.1[j])) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun p => (setSeedBack geom p.1 j p.2, p.1.2.1.1[j]), ?_, ?_⟩ <;>
    · rintro ⟨r, s⟩
      simp [setSeedBack, Function.uncurry, setIfInBounds_getElem_self _ _ hj]
  have hp := evalDistEq_pair_of_bijective
    (g := fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) => (r, s))
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => h, fun p => ⟨p, rfl⟩⟩ (fun p => K p.1)
  exact ((evalDistEq_pair_of_bijective hg
    (fun p : RSOR.Randomness geom × Vector UInt8 32 => K p.1)).trans hp.symm).trans
    (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r))

end Backward

end Cryptlib.Protocols.Sphinx.KEMSphinx
