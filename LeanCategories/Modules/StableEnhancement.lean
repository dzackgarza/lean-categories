/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import LeanCategories.Modules.AugmentedObjects

/-!
# The stable enhancement: suspension and the cofiber triangle

The governing construction of dzackgarza/lean-categories#62 realizes a selected augmented object as
an arrow `ε : R^• ⟶ j(X)` in a specified stable enhancement `E`, and reads off the canonical cofiber
sequence

`R^• --ε--> j(X) --> cofib(ε) --> Σ R^•`.

The issue records that `Sp(C)`, `D(C)` and `Σ` do not exist for an arbitrary `C`. They do exist for
cochain complexes over an abelian category: `CochainComplex C ℤ` carries the genuine suspension
`Σ = ⟦1⟧`, and the cofiber sequence of an arrow of cochain complexes is the mapping-cone triangle,
distinguished in the homotopy category. This file states that, so the fourth term of the sequence is
a real suspension and not the abelian fiber of `LeanCategories.Modules.AugmentedObjects`.

The chain-complex model of a selected augmented object is *not* built here: converting the
`ℕ`-indexed selected terms into `CochainComplex C ℤ` is the remaining step, and until it exists the
triangle below is stated for an arbitrary arrow of cochain complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace LeanCategories.Modules

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The suspension `Σ` of the stable enhancement: the shift of cochain complexes by one. -/
noncomputable abbrev suspension (K : CochainComplex C ℤ) : CochainComplex C ℤ := K⟦(1 : ℤ)⟧

/-- The cofiber sequence of an arrow of cochain complexes, as a triangle
`K --φ--> L --> cofib(φ) --> Σ K` in the homotopy category. -/
noncomputable abbrev cofiberTriangle {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  CochainComplex.mappingCone.triangleh φ

/-- The cofiber sequence is a distinguished triangle: the mapping cone supplies the third vertex and
the map to the suspension. -/
theorem cofiberTriangle_distinguished {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    cofiberTriangle φ ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
  HomotopyCategory.mappingCone_triangleh_distinguished φ

/-- The suspension of a vanishing cofiber is the cofiber of the suspension:
`Σ cofib(φ) ≅ cofib(Σ φ)`. This is the compatibility that makes the cofiber sequence stable. -/
noncomputable def cofiberSuspension {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    suspension (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone (φ⟦(1 : ℤ)⟧') :=
  CochainComplex.mappingCone.shiftIso (φ := φ) 1

end LeanCategories.Modules
