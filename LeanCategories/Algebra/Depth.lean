/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.Tactic.ENatToNat

/-!
# Homological depth

Matsumura, *Commutative Ring Theory*, §16, pp. 130--131
(FC13-C06-U018).

These declarations port the definition layer of Mathlib PR #26218 at
`2a84ea75981e352045999fd11bc7ef6b8fab549f`, whose depth API postdates this
repository's Mathlib pin.  Only the Ext-infimum definitions are ported here;
regular-sequence characterizations and other properties remain result work.
-/

@[expose] public section

namespace LeanCategories.Algebra

open CategoryTheory Abelian

universe u v

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The depth between two `R`-modules is the least degree in which `Ext` is nontrivial,
encoded as the supremum of degrees below which every `Ext` group is trivial.

This is the definition later added to Mathlib as `moduleDepth`.

Source: Matsumura, §16, pp. 130--131 (FC13-C06-U018); reference implementation:
Mathlib PR #26218, commit `2a84ea75981e352045999fd11bc7ef6b8fab549f`,
`Mathlib/RingTheory/Depth/Basic.lean`. -/
noncomputable def moduleDepth (N M : ModuleCat.{v} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}

namespace Ideal

/-- Matsumura's depth of an `R`-module `M` with respect to an ideal `I`, defined as
`Ext`-depth from `R/I`.

Source: Matsumura, §16, pp. 130--131 (FC13-C06-U018). -/
noncomputable def depth (I : _root_.Ideal R) (M : ModuleCat.{v} R) : ℕ∞ :=
  moduleDepth (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M

end Ideal

namespace IsLocalRing

/-- The depth of a module over a local ring, namely its depth with respect to the maximal ideal.

Source: Matsumura, §16, pp. 130--131 (FC13-C06-U018). -/
noncomputable def depth [_root_.IsLocalRing R] (M : ModuleCat.{v} R) : ℕ∞ :=
  Ideal.depth (_root_.IsLocalRing.maximalIdeal R) M

end IsLocalRing

section Grade

variable {A : Type u} [CommRing A]

/-- The grade of a module, defined as its `moduleDepth` against the regular module.
Source: Matsumura, section 16 (FC13-C06-U020). -/
noncomputable def moduleGrade (M : ModuleCat.{u} A) : ℕ∞ :=
  moduleDepth M (ModuleCat.of A A)

namespace Ideal

/-- The grade of an ideal is the grade of its quotient module.
Source: Matsumura, section 16 (FC13-C06-U020). -/
noncomputable def grade (J : _root_.Ideal A) : ℕ∞ :=
  moduleGrade (ModuleCat.of A (A ⧸ J))

end Ideal

end Grade

namespace ModuleCat

/-- A module over a local ring is Cohen--Macaulay when it is zero or its support dimension
equals its depth.

Source: Matsumura, section 17 (FC13-C06-U025); reference implementation:
Mathlib PR #26218, `Mathlib/RingTheory/CohenMacaulay/Basic.lean`. -/
class IsCohenMacaulay {A : Type u} [CommRing A] [_root_.IsLocalRing A] [Small.{v} A]
    (M : _root_.ModuleCat.{v} A) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim A M = IsLocalRing.depth M

/-- A big Cohen--Macaulay module is an arbitrary module whose depth is the Krull dimension
of the local ring; no finite-generation hypothesis is imposed.

Source: Matsumura, section 18 (FC13-C06-U062). -/
class IsBigCohenMacaulay {A : Type u} [CommRing A] [_root_.IsLocalRing A] [Small.{v} A]
    (M : _root_.ModuleCat.{v} A) : Prop where
  depth_eq_dim : ringKrullDim A = IsLocalRing.depth M

end ModuleCat

/-- A local ring is Cohen--Macaulay when its Krull dimension equals its depth as a module
over itself.

Source: Matsumura, section 17 (FC13-C06-U025); reference implementation:
Mathlib PR #26218, `Mathlib/RingTheory/CohenMacaulay/Basic.lean`. -/
class IsCohenMacaulayLocalRing (A : Type u) [CommRing A] : Prop extends _root_.IsLocalRing A where
  depth_eq_dim : ringKrullDim A = IsLocalRing.depth (ModuleCat.of A A)

/-- A Noetherian ring is Cohen--Macaulay when every localization at a maximal ideal is a
Cohen--Macaulay local ring.

This is Matsumura's global definition itself.  The stronger all-prime localization formulation
in Mathlib PR #26218 is equivalent only after a localization theorem, so that comparison is not
built into the Sweep-III definition.  Source: Matsumura, section 17 (FC13-C06-U031). -/
class IsCohenMacaulayRing (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop where
  CM_localize : ∀ m : _root_.Ideal A, ∀ (_ : m.IsMaximal),
    IsCohenMacaulayLocalRing (Localization.AtPrime m)

namespace Ideal

/-- An ideal is unmixed when every associated prime of its quotient has the same height as
the ideal.

Source: Matsumura, section 17 (FC13-C06-U030); reference implementation:
Mathlib PR #26957 at `cb58875d409523d7f9fe40519e8aec70c59855a4`,
`Mathlib/RingTheory/CohenMacaulay/Unmixed.lean`. -/
def IsUnmixed {A : Type u} [CommRing A] (I : _root_.Ideal A) : Prop :=
  ∀ {p : _root_.Ideal A}, p ∈ associatedPrimes A (A ⧸ I) → p.height = I.height

end Ideal

/-- A local ring is Gorenstein when the regular module has finite injective dimension.

This chooses the finite-injective-dimension condition among Matsumura Theorem 18.1's equivalent
conditions; their equivalence is result work.  Source: Matsumura, section 18 (FC13-C06-U045);
reference implementation: Mathlib PR #31884 at
`562682e1e4b23bcf3a8f777cfbfa88e54cd4eaa3`, `Mathlib/RingTheory/Gorenstein/Defs.lean`. -/
class IsGorensteinLocalRing (A : Type u) [CommRing A] : Prop extends _root_.IsLocalRing A where
  injdim : injectiveDimension (ModuleCat.of A A) ≠ ⊤

/-- A Noetherian ring is Gorenstein when every localization at a maximal ideal is a Gorenstein
local ring.

This is Matsumura's global definition.  Prime-localization stability is a theorem and is not
built into this predicate.  Source: Matsumura, section 18 (FC13-C06-U048); reference definition
layer: Mathlib PR #31884 at `562682e1e4b23bcf3a8f777cfbfa88e54cd4eaa3`. -/
class IsGorensteinRing (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop where
  Gorenstein_localize : ∀ m : _root_.Ideal A, ∀ (_ : m.IsMaximal),
    IsGorensteinLocalRing (Localization.AtPrime m)

end LeanCategories.Algebra
