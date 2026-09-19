/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Raw factor-set extension data

Dummit--Foote, *Abstract Algebra*, Section 17.4 (FC01-C17-U070).

For a coefficient group written additively and a group `G`, the source
constructs the extension carrier `A × G` and gives its twisted multiplication
from a normalized factor set. Sweep III records only that carrier and formula.
Normalization, the cocycle identity, associativity, identity/inverse laws, and
the resulting group-extension structure are result-layer statements.
-/

@[expose] public section

namespace GroupExtension

universe uA uG

/-- The carrier `A × G` of the extension attached to factor-set data. -/
abbrev FactorSetExtensionCarrier (A : Type uA) (G : Type uG) := A × G

/-- The distinguished identity data `(0,1)` on the factor-set extension
carrier. No identity law is asserted here. -/
def factorSetExtensionIdentity (A : Type uA) (G : Type uG)
    [Zero A] [One G] : FactorSetExtensionCarrier A G :=
  (0, 1)

/-- Dummit--Foote's displayed twisted multiplication
`(a,g) * (b,h) = (a + g • b + f(g,h), gh)` (FC01-C17-U070).

The intended `f` is a normalized two-cocycle, but those conditions and all
laws they imply are deliberately not bundled into this data constructor. -/
def factorSetExtensionMul (A : Type uA) (G : Type uG)
    [Add A] [SMul G A] [Mul G] (f : G → G → A)
    (x y : FactorSetExtensionCarrier A G) : FactorSetExtensionCarrier A G :=
  (x.1 + x.2 • y.1 + f x.2 y.2, x.2 * y.2)

end GroupExtension
