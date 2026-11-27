/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxRSOR
import Cryptlib.Protocols.Sphinx.KEMSphinxHeaderFn

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.KEMSphinx (padAt)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Util.Bytes (ofVector)

/-! # A NIKE Sphinx packet from each hop's group element and keys

`newNIKEPacket` derives every hop's keys from the sender's secret. A security proof replaces one
hop's keys, and with them its blinding factor and so the group elements of the hops after it.
`nikePktFn` is the packet as a function of what each hop is given: its group element, its header
keystream, its tagging function and its payload encryption. -/

/-- The group element each hop receives: the sender's public key, blinded by the factors of the
hops in front. -/
def groupElem (nike : NIKE) (c : nike.PrivateKey) (keys : Array HopKeys) : ℕ → ByteArray
  | 0 => ofVector (nike.encodePublicKey (nike.derivePublicKey c))
  | i + 1 => nikeBlind nike (groupElem nike c keys i) (keys[i]!).blindingFactor

section HeaderFn

variable (geom : Geometry)

/-- A hop's routing fragment: its commands, the next hop's name and tag before the end of the
path, padded to a hop's length. -/
def nikeFragment (path : Array PathHop) (mac : ByteArray) (i : ℕ) : Except String ByteArray := do
  let frag ← commandsToBytes
    (if i == path.size - 1 then geom.perHopRoutingInfoLength
      else geom.perHopRoutingInfoLength - geom.nextNodeHopLength) (path[i]!).commands
  pure (zeroPadTo geom.perHopRoutingInfoLength
    (if i == path.size - 1 then frag
      else frag ++ (RoutingCommand.nextNodeHop (path[i + 1]!).id (toVec32 mac)).toBytes))

/-- The routing information and tag of the header's layers, built from the last hop back:
after `j` steps, those of the layer for hop `path.size - j`. Each hop enters through its group
element `ge`, its header keystream `ks` and its tagging function `tag`. -/
def nikeHdrTrace (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) : ℕ → Option (ByteArray × ByteArray)
  | 0 => some (if geom.nrHops > path.size then filler else ByteArray.empty, ByteArray.empty)
  | j + 1 =>
    match nikeHdrTrace ks tag ge filler path j with
    | none => none
    | some s =>
      match nikeFragment geom path s.2 (path.size - 1 - j) with
      | .error _ => none
      | .ok frag =>
        some (xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
            (geom.routingInfoLength + geom.perHopRoutingInfoLength
              - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength)),
          tag (path.size - 1 - j) (v0AD ++ ge (path.size - 1 - j)
            ++ xorBytes (frag ++ s.1) ((ks (path.size - 1 - j)).extract 0
              (geom.routingInfoLength + geom.perHopRoutingInfoLength
                - (path.size - 1 - j + 1) * geom.perHopRoutingInfoLength))
            ++ (if path.size - 1 - j > 0 then padAt geom ks (path.size - 1 - j - 1)
              else ByteArray.empty)))

/-- **The packet, from each hop's group element, keystream, tagging function and payload
encryption.** -/
def nikePktFn (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (payload : ByteArray) : Option ByteArray :=
  if payload.size = geom.forwardPayloadLength then
    (nikeHdrTrace geom ks tag ge filler path path.size).map fun s =>
      v0AD ++ ge 0 ++ s.1 ++ s.2
        ++ (List.range' 0 path.size).foldl (fun b iRev => enc (path.size - 1 - iRev) b)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)
  else none

end HeaderFn

end Cryptlib.Protocols.Sphinx.NIKESphinx
