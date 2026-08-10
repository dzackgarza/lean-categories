/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChange
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]

/-- Reduction of integral lattices modulo an ideal. -/
noncomputable def reduceIntegralModuloIdeal (I : Ideal R) :
    IntegralLatticeCat R ⥤ IntegralLatticeCat (R ⧸ I) :=
  baseChangeIntegral R (R ⧸ I)

/-- Reduction of finite projective integral lattices modulo an ideal. -/
noncomputable def reduceFiniteIntegralModuloIdeal (I : Ideal R) :
    FiniteProjectiveLatticeCat R R ⥤
      FiniteProjectiveLatticeCat (R ⧸ I) (R ⧸ I) :=
  baseChangeFiniteIntegral R (R ⧸ I)

@[simp]
theorem reduceIntegralModuloIdeal_pairing_tmul
    (I : Ideal R) (L : IntegralLatticeCat R)
    (a b : R ⧸ I) (x y : L.obj.carrier) :
    ((reduceIntegralModuloIdeal R I).obj L).obj.pairing
        (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R (R ⧸ I) (L.obj.pairing x y) :=
  baseChangeIntegral_pairing_tmul R (R ⧸ I) L a b x y

/-- Reduction of integral lattices to the residue field at a prime ideal. -/
noncomputable def reduceIntegralToResidueField
    (P : Ideal R) [P.IsPrime] :
    IntegralLatticeCat R ⥤ IntegralLatticeCat P.ResidueField :=
  baseChangeIntegral R P.ResidueField

/-- Reduction of finite projective lattices to the residue field at a prime ideal. -/
noncomputable def reduceFiniteIntegralToResidueField
    (P : Ideal R) [P.IsPrime] :
    FiniteProjectiveLatticeCat R R ⥤
      FiniteProjectiveLatticeCat P.ResidueField P.ResidueField :=
  baseChangeFiniteIntegral R P.ResidueField

@[simp]
theorem reduceIntegralToResidueField_pairing_tmul
    (P : Ideal R) [P.IsPrime] (L : IntegralLatticeCat R)
    (a b : P.ResidueField) (x y : L.obj.carrier) :
    ((reduceIntegralToResidueField R P).obj L).obj.pairing
        (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R P.ResidueField (L.obj.pairing x y) :=
  baseChangeIntegral_pairing_tmul R P.ResidueField L a b x y

end LeanCategories.Lattices.Valued
