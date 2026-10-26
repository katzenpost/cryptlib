/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Lean.Data.Json
import Cryptlib.Primitives.Sign.MLDSA.MLDSA
import Cryptlib.Util.HexBytes

/-! # ML-DSA-65 known-answer tests: NIST ACVP vectors

Vectors in `testdata/mldsa65_{keygen,siggen,sigver}.json`, extracted by
`scripts/extract_acvp_mldsa.py`; then sign/verify round trips through `mldsa65Signature`. -/

open Lean
open MLDSA MLDSA.Concrete
open Cryptlib.Primitives.Sign.FIPS204
open Cryptlib.Primitives.Sign.Sign
open Cryptlib.Util.HexBytes
open Cryptlib.Util.Bytes (ofVector toVecN)

def field (j : Json) (k : String) : Except String ByteArray := do
  let s ← (← j.getObjVal? k).getStr?
  match hexStringToByteArray s with
  | some b => pure b
  | none   => throw s!"field {k}: not valid hex: {s}"

def str (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?

def loadPrimitive (path prim : String) : IO (Array Json) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let p ← IO.ofExcept (j.getObjVal? "primitive" >>= Json.getStr?)
  if p ≠ prim then throw (IO.userError s!"unexpected primitive in {path}: {p}")
  IO.ofExcept (j.getObjVal? "vectors" >>= Json.getArr?)

abbrev P : Params := MLDSA.mldsa65

def report (r : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  IO.println s!"  {if ok then "ok  " else "FAIL"}  {name}"
  unless ok do r.modify (· + 1)

/-- `M'` for a vector: the message itself (internal), or `0 ‖ |ctx| ‖ ctx ‖ M` (external). -/
def messageOf (j : Json) : Except String (List Byte) := do
  let msg ← field j "message_hex"
  match ← str j "mode" with
  | "external" =>
    let ctx ← field j "context_hex"
    pure (0 :: ctx.size.toUInt8 :: (ctx.toList ++ msg.toList))
  | _ => pure msg.toList

def runKeyGen (r : IO.Ref Nat) : IO Unit := do
  let arr ← loadPrimitive "testdata/mldsa65_keygen.json" "mldsa65_keygen"
  IO.println s!"ML-DSA-65 KeyGen (NIST ACVP, {arr.size} vectors)"
  for j in arr do
    let (name, seed, pk, sk) ← IO.ofExcept (do
      pure (← str j "name", ← field j "seed_hex", ← field j "pk_hex", ← field j "sk_hex"))
    let (gpk, gsk) := keys P (toVecN 32 seed)
    report r name (pkBytes P gpk == pk &&
      skEncode P gsk.rho gsk.key gsk.tr gsk.s1 gsk.s2 gsk.t0 == sk)

def runSigGen (r : IO.Ref Nat) : IO Unit := do
  let arr ← loadPrimitive "testdata/mldsa65_siggen.json" "mldsa65_siggen"
  IO.println s!"ML-DSA-65 SigGen (NIST ACVP, {arr.size} vectors)"
  for j in arr do
    let (name, mode, skB, rndB, want) ← IO.ofExcept (do
      pure (← str j "name", ← str j "mode", ← field j "sk_hex", ← field j "rnd_hex",
        ← field j "signature_hex"))
    let (rho, key, tr, s1, s2, t0) := skDecode P skB
    let sk : SecretKey P := ⟨rho, key, tr, s1, s2, t0⟩
    let mu ← IO.ofExcept (if mode == "mu" then do pure (toVecN 64 (← field j "mu_hex")) else do
      pure ((prims P).hashMessage tr (← messageOf j)))
    let rhoDP := (prims P).hashPrivateSeed key (toVecN 32 rndB) mu
    let got := (fipsSignLoop P (prims P) sk ((prims P).expandA rho) mu rhoDP maxAttempts).map
      (sigBytes P)
    report r name (got == some want)

def runSigVer (r : IO.Ref Nat) : IO Unit := do
  let arr ← loadPrimitive "testdata/mldsa65_sigver.json" "mldsa65_sigver"
  IO.println s!"ML-DSA-65 SigVer (NIST ACVP, {arr.size} vectors)"
  for j in arr do
    let (name, pkB, sigB, msg) ← IO.ofExcept (do
      pure (← str j "name", ← field j "pk_hex", ← field j "signature_hex", ← messageOf j))
    let want ← IO.ofExcept (do (← j.getObjVal? "want_pass").getBool?)
    let (rho, t1) := pkDecode P pkB
    let got := match sigDecode P sigB with
      | some (c, z, h) => fipsVerify P (prims P) ⟨rho, t1⟩ msg ⟨c, z, h⟩
      | none => false
    report r name (got == want)

def runSignature (r : IO.Ref Nat) : IO Unit := do
  IO.println "ML-DSA-65 as a Signature"
  let S := mldsa65Signature
  for i in [0:3] do
    let seed : Vector UInt8 32 := Vector.ofFn fun k => (k.val * 7 + i).toUInt8
    let m : ByteArray := s!"message {i}".toUTF8
    let t0 ← IO.monoMsNow
    let pk := S.pub seed
    match S.sign seed m ((i, Vector.ofFn fun k => k.val.toUInt8) : State) with
    | .error _ _ => report r s!"seed {i}: signs" false
    | .ok σ _ =>
      let t1 ← IO.monoMsNow
      report r s!"seed {i}: verifies ({t1 - t0} ms to sign)" (S.verify pk m σ)
      report r s!"seed {i}: another message does not verify" (!S.verify pk "other".toUTF8 σ)
      let b := S.encodeSig σ
      match S.decodeSig (b.set! 100 (b[100]! ^^^ 1)) with
      | some bad => report r s!"seed {i}: a changed signature does not verify" (!S.verify pk m bad)
      | none => report r s!"seed {i}: a changed signature decodes" false

def main : IO UInt32 := do
  let r ← IO.mkRef 0
  runKeyGen r
  runSigGen r
  runSigVer r
  runSignature r
  let n ← r.get
  IO.println (if n == 0 then "all ML-DSA-65 tests passed" else s!"{n} ML-DSA-65 tests failed")
  pure (if n == 0 then 0 else 1)
