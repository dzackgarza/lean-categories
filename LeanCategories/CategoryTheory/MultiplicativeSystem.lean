/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Limits.Types.Colimits

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


namespace LeanCategories.CategoryTheory

open CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]
variable {W : MorphismProperty C} {X : C}

/-- The small category of a chosen cofinal family of left denominators into `X`.

A morphism from `s : X_s ⟶ X` to `t : X_t ⟶ X` is a map `X_t ⟶ X_s` whose composite with `s`
is `t`, exactly as in Weibel's construction preceding the filtered-colimit description of localized
Hom sets.

Source: Weibel, §10.3, pp. 379--384 (FC05-C10-U030). -/
structure LeftDenominator (D : LeftLocalSmallData.{u, v, w} W X) where
  /-- The index of the chosen denominator. -/
  index : D.ι

/-- Morphisms in the chosen denominator category. -/
@[ext]
structure LeftDenominatorHom (D : LeftLocalSmallData.{u, v, w} W X)
    (i j : LeftDenominator D) where
  /-- The refinement map, contravariant on denominator sources. -/
  hom : D.source j.index ⟶ D.source i.index
  /-- The refinement commutes with the maps to `X`. -/
  fac : hom ≫ D.denominator i.index = D.denominator j.index

instance (D : LeftLocalSmallData.{u, v, w} W X) : Category.{v} (LeftDenominator D) where
  Hom := LeftDenominatorHom D
  id i := ⟨𝟙 _, by simp⟩
  comp f g := ⟨g.hom ≫ f.hom, by rw [Category.assoc, f.fac, g.fac]⟩
  assoc _ _ _ := by ext; simp [Category.assoc]
  id_comp _ := by ext; simp
  comp_id _ := by ext; simp

/-- The type-valued diagram `s ↦ Hom_C(source(s), Y)` on the chosen denominator category. -/
def leftDenominatorHomFunctorSmall
    (D : LeftLocalSmallData.{u, v, w} W X) (Y : C) : LeftDenominator D ⥤ Type v where
  obj i := D.source i.index ⟶ Y
  map {i j} f := ↾fun (h : D.source i.index ⟶ Y) => f.hom ≫ h
  map_id i := by
    ext h
    change (𝟙 (D.source i.index)) ≫ h = h
    simp
  map_comp f g := by
    ext h
    change (g.hom ≫ f.hom) ≫ h = g.hom ≫ f.hom ≫ h
    simp [Category.assoc]

/-- Universe-lifted version of `leftDenominatorHomFunctorSmall`, landing in a universe large enough
for the chosen denominator category. -/
def leftDenominatorHomFunctor
    (D : LeftLocalSmallData.{u, v, w} W X) (Y : C) :
    LeftDenominator D ⥤ Type (max v w) :=
  leftDenominatorHomFunctorSmall D Y ⋙ uliftFunctor.{w, v}

/-- The filtered-colimit candidate for the localized Hom set `Hom_S(X,Y)` attached to a chosen
set-sized cofinal family of left denominators.

The source assertion that the denominator category can be taken filtered and that this colimit is
canonically the fraction quotient `Hom_S(X,Y)` is theorem-level material.

Source: Weibel, §10.3, pp. 379--384 (FC05-C10-U030). -/
noncomputable abbrev leftFractionHomColimit
    (D : LeftLocalSmallData.{u, v, w} W X) (Y : C) : Type (max v w) :=
  colimit (leftDenominatorHomFunctor D Y)

end LeanCategories.CategoryTheory
