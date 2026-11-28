/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.OracleComp.Constructions.SampleableType
import Cryptlib.Primitives.MAC.MAC
import Cryptlib.Util.Bytes

/-! # Forging a MAC tag

The game for a MAC under a uniform 32-byte key used once: the adversary is given the tag of one
message of its choice and then names messages and tags. It wins if one of them is a different
message with its right tag. Unforgeability is the assumption that its chance is small; it is
computational, so it is a game here and not a law of `MAC`. -/

namespace Cryptlib.Primitives.MAC

open OracleComp
open Cryptlib.Util.Bytes (ofVector)

/-- An adversary against a MAC used once. -/
structure ForgeAdversary (macS : MAC) where
  St : Type
  /-- The message whose tag the adversary is given. -/
  choose : ProbComp (ByteArray × St)
  /-- Its attempts, given the tag. -/
  forge : St → Vector UInt8 macS.tagSize → ProbComp (List (ByteArray × Vector UInt8 macS.tagSize))

/-- The experiment for `ForgeAdversary`: whether an attempt is a forgery. -/
def forgeExp (macS : MAC) (B : ForgeAdversary macS) : ProbComp Bool := do
  let k ← $ᵗ (Vector UInt8 32)
  let ms ← B.choose
  let attempts ← B.forge ms.2 (macS.mac (ofVector k) ms.1)
  return attempts.any fun a => decide (a.1 ≠ ms.1) && macS.mac (ofVector k) a.1 == a.2

end Cryptlib.Primitives.MAC
