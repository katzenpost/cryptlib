import Cryptlib.Primitives.NIKE.X25519LadderCorrect
import Cryptlib.Primitives.NIKE.X25519
import Cryptlib.Primitives.NIKE.NIKE

open Cryptlib.Primitives.NIKE.NIKE

namespace Cryptlib.Primitives.NIKE

/-! # The X25519 schemes

`X25519Scheme` computes in the curve group. `X25519LadderScheme` and `X25519FastScheme` are the
RFC 7748 Montgomery ladder, proved to compute the group's scalar multiplication, and so to inherit
its laws; they differ only in name. -/

def X25519Scheme : NIKE := X25519.Scheme

def X25519LadderScheme : NIKE := X25519_montgomery_ladder.LadderScheme

/-- X25519, as fast as it is proved: the `ZMod p` ladder. -/
def X25519FastScheme : NIKE := X25519_montgomery_ladder.ladderScheme "X25519"

def implementations : List NIKE :=
  [
    X25519Scheme,
    X25519LadderScheme,
    X25519FastScheme
  ]

/-! ## Registry by canonical scheme name -/

/-- A canonical scheme name and its implementation. -/
structure RegistryEntry where
  hpqcName : String
  scheme : NIKE

def x25519LadderEntry : RegistryEntry := { hpqcName := "x25519-ladder", scheme := X25519LadderScheme }

def x25519GroupEntry : RegistryEntry := { hpqcName := "x25519-group", scheme := X25519Scheme }

def x25519FastEntry : RegistryEntry := { hpqcName := "x25519", scheme := X25519FastScheme }

def registry : List RegistryEntry := [x25519FastEntry, x25519LadderEntry, x25519GroupEntry]

/-- Case-insensitive lookup by scheme name. -/
def byName (name : String) : Option NIKE :=
  (registry.find? (·.hpqcName.toLower == name.toLower)).map (·.scheme)

end Cryptlib.Primitives.NIKE
