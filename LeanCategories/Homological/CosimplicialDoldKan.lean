/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.Algebra.Homology.Opposite

/-!
# Dual Dold--Kan for cosimplicial objects

Weibel, *An Introduction to Homological Algebra* (1994), Corollary/Definition
8.4.3, §8.4, pp. 270--274 (FC05-C08-U045).

The cosimplicial/cochain form of Dold--Kan is obtained formally by passing to
opposite categories, applying Mathlib's simplicial Dold--Kan equivalence in
`Aᵒᵖ`, and transporting chain complexes back to cochain complexes in `A`.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The dual Dold--Kan equivalence at the level of opposite categories. -/
def cosimplicialDoldKanOpEquivalence :
    (CosimplicialObject A)ᵒᵖ ≌ (CochainComplex A ℕ)ᵒᵖ :=
  (cosimplicialSimplicialEquiv A).trans
    ((CategoryTheory.Abelian.DoldKan.equivalence (A := Aᵒᵖ)).trans
      (HomologicalComplex.opEquivalence A (.up ℕ)).symm)

/-- Dual Dold--Kan: cosimplicial objects in an abelian category are equivalent
to nonnegatively graded cochain complexes. -/
def cosimplicialDoldKanEquivalence :
    CosimplicialObject A ≌ CochainComplex A ℕ :=
  (cosimplicialDoldKanOpEquivalence A).rightOp.trans
    (opOpEquivalence (CochainComplex A ℕ))

end LeanCategories.Homological
