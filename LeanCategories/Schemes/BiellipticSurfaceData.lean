/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AbelianVariety
public import LeanCategories.Schemes.BirationalSurfaceModels
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Bielliptic-surface quotient data

Definition-level realization of Beauville FC12-C06-U023.

Beauville defines a bielliptic surface as a quotient (E × F) / G for
elliptic curves E,F, with G acting by translations on E and
with F/G isomorphic to P¹.

Sweep III does not construct finite-group quotients. Instead this file states
the source definition as an exact quotient-presentation predicate on an
already supplied smooth projective complex surface. Quotienthood is the
categorical universal property in schemes over Spec ℂ; existence of such
quotients and their geometric properties remain result-layer statements.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open _root_.AlgebraicGeometry
open LeanCategories.AlgebraicGeometry

namespace LeanCategories.Schemes

/-- A smooth projective complex surface as an object over Spec ℂ. -/
abbrev smoothProjectiveSurfaceOverData
    (S : SmoothProjectiveComplexSurface) :
    Over (Spec (.of ℂ)) :=
  Over.mk S.structureMap

/-- The projective line over ℂ, using the existing complex structure map. -/
abbrev complexProjectiveLineOverData : Over (Spec (.of ℂ)) :=
  Over.mk (complexProjectiveSpaceToSpec 1)

/-- Scheme-level elliptic-curve predicate used in Beauville VI.19.

An abelian variety of relative dimension one is an elliptic curve. The
abelian-variety carrier already supplies the proper geometrically integral
group scheme and its distinguished identity point; this predicate records only
the dimension-one condition. -/
def IsEllipticCurveData {K : Type*} [Field K]
    (E : AbelianVariety K) : Prop :=
  SmoothOfRelativeDimension 1 E.toOver.hom

/-- Raw action of a group on an object of a category. The action laws are
kept in IsGroupActionData, not as proof fields. -/
abbrev GroupActionHomData (G : Type*) [Group G]
    {C : Type*} [Category C] (X : C) :=
  G → (X ⟶ X)

/-- Exact group-action laws for raw endomorphism data. -/
def IsGroupActionData
    (G : Type*) [Group G]
    {C : Type*} [Category C] {X : C}
    (ρ : GroupActionHomData G X) : Prop :=
  ρ 1 = 𝟙 X ∧ ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h

/-- Categorical quotient predicate for a group action.

The map q : X → Q is invariant and is universal among invariant maps. No
existence or effectiveness theorem is built into this predicate. -/
def IsGroupQuotientData
    (G : Type*) [Group G]
    {C : Type*} [Category C] {X Q : C}
    (ρ : GroupActionHomData G X) (q : X ⟶ Q) : Prop :=
  IsGroupActionData G ρ ∧
    (∀ g : G, ρ g ≫ q = q) ∧
    ∀ (Z : C) (f : X ⟶ Z),
      (∀ g : G, ρ g ≫ f = f) →
        ∃! u : Q ⟶ Z, q ≫ u = f

/-- A raw action on an abelian variety is by translations when every action
map is right multiplication by a point of the group scheme. -/
def IsTranslationActionData
    (G : Type*) [Group G]
    (E : AbelianVariety ℂ)
    (ρ : GroupActionHomData G E.toOver) : Prop := by
  letI : GrpObj E.toOver := E.grpObj
  exact IsGroupActionData G ρ ∧
    ∀ g : G, ∃ x : 𝟙_ (Over (Spec (.of ℂ))) ⟶ E.toOver,
      ρ g = (GrpObj.mulRight x).hom

/-- Diagonal action on E × F from actions on the two factors. -/
def productActionData
    (G : Type*) [Group G]
    (E F : AbelianVariety ℂ)
    (ρE : GroupActionHomData G E.toOver)
    (ρF : GroupActionHomData G F.toOver) :
    GroupActionHomData G (E.toOver ⊗ F.toOver) :=
  fun g => ρE g ⊗ₘ ρF g

/-- Beauville VI.19: S is bielliptic when it admits a finite-group quotient
presentation (E × F)/G, where both factors are elliptic, the action on E is
by translations, and the quotient F/G is the projective line.

All quotient maps and actions occur under existential quantifiers. In
particular, the definition does not manufacture the stable affine atlas or
quotient scheme whose existence belongs to the theorem layer. -/
def IsBiellipticSurfaceData (S : SmoothProjectiveComplexSurface) : Prop :=
  ∃ (E F : AbelianVariety ℂ),
    IsEllipticCurveData E ∧
      IsEllipticCurveData F ∧
      ∃ (G : Type) (_ : Group G)
        (ρE : GroupActionHomData G E.toOver)
        (ρF : GroupActionHomData G F.toOver)
        (q : E.toOver ⊗ F.toOver ⟶ smoothProjectiveSurfaceOverData S)
        (qF : F.toOver ⟶ complexProjectiveLineOverData),
        IsTranslationActionData G E ρE ∧
          IsGroupQuotientData G (productActionData G E F ρE ρF) q ∧
          IsGroupQuotientData G ρF qF

end LeanCategories.Schemes
