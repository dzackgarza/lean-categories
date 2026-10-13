/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Depth
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Serre conditions

Matsumura, *Commutative Ring Theory*, §23, p. 183 (FC13-C08-U024).

This file records only the localization predicates `(R_i)` and `(S_i)`.  Their
interpretations, normality criterion, and flat-family permanence are result work.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

/-- Serre's condition `(R_i)`: every prime of height strictly below `i` has regular local
localization.  `height p < i` is the subtraction-free form of Matsumura's
`height p ≤ i - 1`, and is vacuous for `i = 0`. -/
def SerreR (A : Type u) [CommRing A] [IsNoetherianRing A] (i : ℕ) : Prop :=
  ∀ p : _root_.Ideal A, ∀ (_ : p.IsPrime), p.height < (i : ℕ∞) →
    IsRegularLocalRing (Localization.AtPrime p)

/-- Serre's condition `(S_i)`: at every prime `p`, the depth of the localization is at least
`min(height p, i)`. -/
def SerreS (A : Type u) [CommRing A] [IsNoetherianRing A] (i : ℕ) : Prop :=
  ∀ p : _root_.Ideal A, ∀ (_ : p.IsPrime),
    min p.height (i : ℕ∞) ≤
      IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))

end LeanCategories.Algebra
