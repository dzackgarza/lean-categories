/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.LocalIntersectionMultiplicityData
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Global intersection number of two curve germs

Definition-level realization of Beauville FC12-C01-U003.

For two distinct irreducible curves on a smooth complex surface, Beauville
defines

  `C · C' = ∑_{x ∈ C ∩ C'} m_x(C,C')`.

The source hypotheses imply that the set of intersection points is finite.
Sweep III does not prove that finiteness statement.  Mathlib's `finsum`
provides the canonical sum of a finitely supported family without requiring a
finite-support witness at construction time.  Thus the intersection number is
defined directly as the `finsum` of the already-realized local
multiplicities over the common point set.  The source finiteness theorem later
identifies this total construction with the displayed ordinary finite sum.

The source's equivalent description as the length of the scheme-theoretic
intersection is a comparison result and is deliberately not built into the
definition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The underlying point set of the scheme-theoretic intersection of two
closed subschemes, expressed as the intersection of their point-set ranges. -/
def curveIntersectionPointSetData {C C' S : Scheme.{u}}
    (i : C ⟶ S) (j : C' ⟶ S) : Set S :=
  Set.range i ∩ Set.range j

/-- Exact graph of Beauville's finite local-intersection sum.

`stalkAlgebra` is the ambient complex-algebra structure on the local rings of
the complex surface.  In the source setting it is induced by the structure
morphism to `Spec ℂ`; no arbitrary local equations are supplied. -/
def IsCurveIntersectionNumberData {C C' S : Scheme.{u}}
    (i : C ⟶ S) (j : C' ⟶ S)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (stalkAlgebra : ∀ x : S, Algebra ℂ (S.presheaf.stalk x))
    (n : ℕ) : Prop := by
  classical
  exact ∃ T : Finset S,
    (∀ x : S, x ∈ T ↔ x ∈ curveIntersectionPointSetData i j) ∧
      n = ∑ x ∈ T, by
        letI : Algebra ℂ (S.presheaf.stalk x) := stalkAlgebra x
        exact localIntersectionMultiplicityData i j x

/-- Beauville's global intersection number as the native finite-support sum of
the local multiplicities over the common point set.

Under the source hypotheses the support is finite; proving that fact and
rewriting this `finsum` as an ordinary sum over `C ∩ C'` are result-layer
obligations rather than prerequisites for constructing the value. -/
def curveIntersectionNumberData {C C' S : Scheme.{u}}
    (i : C ⟶ S) (j : C' ⟶ S)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (stalkAlgebra : ∀ x : S, Algebra ℂ (S.presheaf.stalk x)) : ℕ :=
  ∑ᶠ x ∈ curveIntersectionPointSetData i j, by
    letI : Algebra ℂ (S.presheaf.stalk x) := stalkAlgebra x
    exact localIntersectionMultiplicityData i j x

end LeanCategories.Schemes
