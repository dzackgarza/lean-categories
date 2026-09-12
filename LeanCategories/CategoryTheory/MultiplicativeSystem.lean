/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Multiplicative systems in the sense of Weibel

Weibel, *An Introduction to Homological Algebra*, Definition 10.3.4, pp. 379--384
(FC05-C10-U026).

Mathlib splits Weibel's two-sided axioms into a multiplicative morphism property together with left
and right calculi of fractions.  The latter classes contain the corresponding Ore square and
cancellation axioms and each extends multiplicativity.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Weibel's two-sided multiplicative system: a morphism property admitting both the left and right
calculus of fractions.  Mathlib's two calculus classes include identities/composition and exactly
the source Ore and cancellation axioms.

Source: Weibel, Definition 10.3.4, pp. 379--384 (FC05-C10-U026). -/
def IsMultiplicativeSystem (W : MorphismProperty C) : Prop :=
  W.HasLeftCalculusOfFractions ∧ W.HasRightCalculusOfFractions

end LeanCategories.CategoryTheory

namespace LeanCategories.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A set-sized cofinal family of left denominators with target `X`.

The indexing type `ι : Type w` is Weibel's set `S_X`.  For every denominator `s : X₁ ⟶ X`,
`cofinal` chooses a denominator in the family factoring through `s` on the left.

Source: Weibel, Set-Theoretic Considerations 10.3.6, pp. 379--384 (FC05-C10-U029). -/
structure LeftLocalSmallData (W : MorphismProperty C) (X : C) where
  /-- The set-sized indexing type for the chosen cofinal family `S_X`. -/
  ι : Type w
  /-- The source of each chosen denominator. -/
  source : ι → C
  /-- The chosen denominators, all with target `X`. -/
  denominator : ∀ i, source i ⟶ X
  /-- Every chosen arrow is in the multiplicative system. -/
  mem : ∀ i, W (denominator i)
  /-- Every denominator into `X` admits a refinement belonging to the chosen family. -/
  cofinal : ∀ {X₁ : C} (s : X₁ ⟶ X), W s →
    ∃ (i : ι) (u : source i ⟶ X₁), u ≫ s = denominator i

/-- A multiplicative system is locally small on the left when every target admits a set-sized
cofinal family of left denominators.

Source: Weibel, Set-Theoretic Considerations 10.3.6, pp. 379--384 (FC05-C10-U029). -/
def IsLocallySmallOnLeft (W : MorphismProperty C) : Prop :=
  ∀ X : C, Nonempty (LeftLocalSmallData.{u, v, w} W X)

end LeanCategories.CategoryTheory
