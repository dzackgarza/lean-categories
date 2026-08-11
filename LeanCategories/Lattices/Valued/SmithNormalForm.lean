/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Discriminant
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

section PID

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Fraction-field perfection gives a full-rank adjoint image in the value dual. -/
theorem adjointRange_finrank_eq_valueDual (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsFractionFieldPerfect R L) :
    Module.finrank R (LinearMap.range L.obj.adjoint) =
      Module.finrank R L.obj.valueDual := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Free R L.obj.carrier := by infer_instance
  letI : Module.Finite R L.obj.valueDual := by infer_instance
  letI : Module.Free R L.obj.valueDual := by infer_instance
  have hinj := adjoint_injective_of_fractionFieldPerfect R L hL
  have hrange : Module.finrank R (LinearMap.range L.obj.adjoint) =
      Module.finrank R L.obj.carrier :=
    (LinearEquiv.ofInjective L.obj.adjoint hinj).finrank_eq.symm
  let b := Module.Free.chooseBasis R L.obj.carrier
  have hdual : Module.finrank R L.obj.valueDual =
      Module.finrank R L.obj.carrier := by
    rw [Module.finrank_eq_card_basis b.dualBasis]
    rw [Module.finrank_eq_card_basis b]
  exact hrange.trans hdual.symm

/-- Smith normal form for the adjoint image inside the value dual. -/
noncomputable def adjointSmithNormalForm {I : Type*} [Fintype I] [DecidableEq I]
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier]
    (hL : IsFractionFieldPerfect R L)
    (b : Module.Basis I R L.obj.carrier) :
    Module.Basis.SmithNormalForm (LinearMap.range L.obj.adjoint) I
      (Fintype.card I) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Free R L.obj.carrier := Module.Free.of_basis b
  letI : Module.Finite R L.obj.valueDual := by infer_instance
  letI : Module.Free R L.obj.valueDual := by infer_instance
  exact (LinearMap.range L.obj.adjoint).smithNormalFormOfRankEq b.dualBasis
    (adjointRange_finrank_eq_valueDual L hL)

/-- The adjoint defect as the product of its cyclic Smith factors. -/
noncomputable def defectEquivPiSpan {I : Type*} [Finite I] [DecidableEq I]
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier]
    (hL : IsFractionFieldPerfect R L)
    (b : Module.Basis I R L.obj.carrier) :
    L.obj.defect ≃ₗ[R]
      ∀ i, R ⧸ Ideal.span
        ({Submodule.smithNormalFormCoeffs b.dualBasis
          (adjointRange_finrank_eq_valueDual L hL) i} : Set R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Free R L.obj.carrier := Module.Free.of_basis b
  letI : Module.Finite R L.obj.valueDual := by infer_instance
  letI : Module.Free R L.obj.valueDual := by infer_instance
  exact (LinearMap.range L.obj.adjoint).quotientEquivPiSpan b.dualBasis
    (adjointRange_finrank_eq_valueDual L hL)

end PID

/-- An integral discriminant module as a product of cyclic Smith factors. -/
noncomputable def defectEquivPiZMod {I : Type*} [Finite I] [DecidableEq I]
    (L : IntegralLatticeCat ℤ) [Module.Finite ℤ L.obj.carrier]
    (hL : IsFractionFieldPerfect ℤ L)
    (b : Module.Basis I ℤ L.obj.carrier) :
    L.obj.defect ≃+
      ∀ i, ZMod (Submodule.smithNormalFormCoeffs b.dualBasis
        (adjointRange_finrank_eq_valueDual L hL) i).natAbs := by
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Free ℤ L.obj.carrier := Module.Free.of_basis b
  letI : Module.Finite ℤ L.obj.valueDual := by infer_instance
  letI : Module.Free ℤ L.obj.valueDual := by infer_instance
  exact (LinearMap.range L.obj.adjoint).quotientEquivPiZMod b.dualBasis
    (adjointRange_finrank_eq_valueDual L hL)

/-- The discriminant order is the product of the absolute Smith coefficients. -/
theorem natCard_defect_eq_prod_smithCoefficients {I : Type*} [Fintype I]
    [DecidableEq I] (L : IntegralLatticeCat ℤ)
    [Module.Finite ℤ L.obj.carrier]
    (hL : IsFractionFieldPerfect ℤ L)
    (b : Module.Basis I ℤ L.obj.carrier) :
    Nat.card L.obj.defect =
      ∏ i, (Submodule.smithNormalFormCoeffs b.dualBasis
        (adjointRange_finrank_eq_valueDual L hL) i).natAbs := by
  rw [Nat.card_congr (defectEquivPiZMod L hL b).toEquiv, Nat.card_pi]
  simp

/-- The discriminant order is the absolute Gram determinant. -/
theorem natCard_defect_eq_natAbs_determinant {I : Type*} [Fintype I]
    [DecidableEq I] (L : IntegralLatticeCat ℤ)
    [Module.Finite ℤ L.obj.carrier]
    (hL : IsFractionFieldPerfect ℤ L)
    (b : Module.Basis I ℤ L.obj.carrier) :
    Nat.card L.obj.defect = Int.natAbs (determinant L b) := by
  symm
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Free ℤ L.obj.carrier := Module.Free.of_basis b
  letI : Module.Finite ℤ L.obj.valueDual := by infer_instance
  letI : Module.Free ℤ L.obj.valueDual := by infer_instance
  have hinj := adjoint_injective_of_fractionFieldPerfect ℤ L hL
  let e := LinearEquiv.ofInjective L.obj.adjoint hinj
  let br : Module.Basis I ℤ (LinearMap.range L.obj.adjoint) := b.map e
  have hcard := Submodule.natAbs_det_basis_change b.dualBasis
    (LinearMap.range L.obj.adjoint) br
  rw [← hcard]
  congr 1
  rw [Module.Basis.det_apply]
  rw [determinant, ← adjoint_toMatrix_eq_gramMatrix L b]
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply]
  simp [br, e, LinearMap.toMatrix_apply]

/-- The discriminant order generates the determinant ideal. -/
theorem determinantIdeal_eq_span_natCard_defect
    {I : Type*} [Fintype I] [DecidableEq I]
    (L : IntegralLatticeCat ℤ) [Module.Finite ℤ L.obj.carrier]
    (hL : IsFractionFieldPerfect ℤ L)
    (b : Module.Basis I ℤ L.obj.carrier) :
    determinantIdeal L b =
      Ideal.span {(Nat.card L.obj.defect : ℤ)} := by
  rw [determinantIdeal, natCard_defect_eq_natAbs_determinant L hL b]
  exact (Int.span_natAbs (determinant L b)).symm

end LeanCategories.Lattices.Valued
