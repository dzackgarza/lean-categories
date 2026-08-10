/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.MetricDual
public import LeanCategories.Modules.Bilinear.Valued.Torsion
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

variable [IsDomain R]

/-- The discriminant formed module as the categorical cokernel of `L → L♯`. -/
noncomputable def discriminantSymBilWFormObject (L : IntegralLatticeCat R) : SymBilWFormCat R :=
  SymBilWFormCat.cokernelObject (toMetricDualSymBilWForm R L)

/-- The formed quotient map from the metric dual to the discriminant module. -/
noncomputable def discriminantSymBilWFormProjection (L : IntegralLatticeCat R) :
    metricDualSymBilWFormObject R L ⟶ discriminantSymBilWFormObject R L :=
  SymBilWFormCat.cokernelProjection (toMetricDualSymBilWForm R L)

/-- The quadratic map `x ↦ b_A(x,x)` on the categorical discriminant module. -/
noncomputable def discriminantSymBilWQuadraticMap (L : IntegralLatticeCat R) :
    QuadraticMap R (discriminantSymBilWFormObject R L).obj.carrier
      (discriminantSymBilWFormObject R L).obj.value :=
  LinearMap.BilinMap.toQuadraticMap
    (discriminantSymBilWFormObject R L).obj.formed.bilinMap

/-- The discriminant is the categorical cokernel among symmetric formed modules. -/
noncomputable def discriminantSymBilWFormIsCokernel (L : IntegralLatticeCat R) :
    IsColimit (SymBilWFormCat.cokernelCofork (toMetricDualSymBilWForm R L)) :=
  SymBilWFormCat.cokernelIsColimit (toMetricDualSymBilWForm R L)

/-- The value relations in the discriminant cokernel are exactly the image of `R`. -/
theorem discriminantValueRelations_eq (L : IntegralLatticeCat R) :
    BilWFormCat.cokernelValueRelations (toMetricDualSymBilWForm R L).hom =
      LinearMap.range (Algebra.linearMap R (FractionRing R)) := by
  apply le_antisymm
  · rw [BilWFormCat.cokernelValueRelations, sup_le_iff, sup_le_iff]
    constructor
    · constructor
      · exact le_rfl
      · rw [BilWFormCat.leftMixedRelations, Submodule.span_le]
        rintro _ ⟨⟨x, y⟩, rfl⟩
        change metricDual R L at y
        refine ⟨metricDualToValueDual R L y x, ?_⟩
        change algebraMap R (FractionRing R) (metricDualToValueDual R L y x) =
          rationalizedForm R L (toRationalSpan R L x) y
        rw [rationalizedForm_isSymmetric]
        exact (rationalizedForm R L).dualSubmoduleParing_spec
          y (toIntegralImage R L x)
    · rw [BilWFormCat.rightMixedRelations, Submodule.span_le]
      rintro _ ⟨⟨y, x⟩, rfl⟩
      change metricDual R L at y
      refine ⟨metricDualToValueDual R L y x, ?_⟩
      change algebraMap R (FractionRing R) (metricDualToValueDual R L y x) =
        rationalizedForm R L y (toRationalSpan R L x)
      exact (rationalizedForm R L).dualSubmoduleParing_spec
        y (toIntegralImage R L x)
  · exact le_trans le_sup_left le_sup_left

/-- The inclusion `L → L♯` in the category of `Frac(R)`-valued `R`-lattices. -/
noncomputable def toMetricDualLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    fractionValuedLattice R L ⟶ metricDualLattice R L hL :=
  ObjectProperty.homMk (toMetricDualBilin R L)

omit [IsDomain R] in
theorem rieszDualBilinMap_adjoint_left (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (x : L.obj.carrier)
    (f : L.obj.valueDual) :
    rieszDualBilinMap R L hL (L.obj.adjoint x) f =
      algebraMap R (FractionRing R) (f x) := by
  change rationalizedForm R L (rieszEmbedding R L hL (L.obj.adjoint x))
    (rieszEmbedding R L hL f) = _
  rw [rieszEmbedding_adjoint, rationalizedForm_isSymmetric]
  exact rationalizedForm_rieszEmbedding R L hL f x

omit [IsDomain R] in
theorem rieszDualBilinMap_adjoint_right (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (f : L.obj.valueDual)
    (x : L.obj.carrier) :
    rieszDualBilinMap R L hL f (L.obj.adjoint x) =
      algebraMap R (FractionRing R) (f x) := by
  change rationalizedForm R L (rieszEmbedding R L hL f)
    (rieszEmbedding R L hL (L.obj.adjoint x)) = _
  rw [rieszEmbedding_adjoint]
  exact rationalizedForm_rieszEmbedding R L hL f x

/-- The value module `Frac(R) / R`. -/
abbrev FractionValueQuotient :=
  FractionRing R ⧸ LinearMap.range (Algebra.linearMap R (FractionRing R))

/-- The quotient map `Frac(R) → Frac(R) / R`. -/
def fractionValueProjection :
    FractionRing R →ₗ[R] FractionValueQuotient R :=
  Submodule.mkQ (LinearMap.range (Algebra.linearMap R (FractionRing R)))

omit [IsDomain R] in
@[simp]
theorem fractionValueProjection_algebraMap (r : R) :
    fractionValueProjection R (algebraMap R (FractionRing R) r) = 0 := by
  rw [fractionValueProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨r, rfl⟩

/-- The Riesz form after projection to `Frac(R) / R`. -/
noncomputable def quotientRieszDualBilinMap (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.BilinMap R L.obj.valueDual (FractionValueQuotient R) :=
  (rieszDualBilinMap R L hL).compr₂ (fractionValueProjection R)

omit [IsDomain R] in
theorem adjointRange_le_ker_quotientRieszDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.range L.obj.adjoint ≤ LinearMap.ker (quotientRieszDualBilinMap R L hL) := by
  rintro f ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro g
  change fractionValueProjection R
    (rieszDualBilinMap R L hL (L.obj.adjoint x) g) = 0
  rw [rieszDualBilinMap_adjoint_left, fractionValueProjection_algebraMap]

omit [IsDomain R] in
theorem adjointRange_le_flipKer_quotientRieszDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.range L.obj.adjoint ≤
      LinearMap.ker (quotientRieszDualBilinMap R L hL).flip := by
  rintro f ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro g
  change fractionValueProjection R
    (rieszDualBilinMap R L hL g (L.obj.adjoint x)) = 0
  rw [rieszDualBilinMap_adjoint_right, fractionValueProjection_algebraMap]

/-- The discriminant bilinear map on `A_L = L*/iota_L(L)`. -/
noncomputable def discriminantBilinMap (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.BilinMap R L.obj.defect (FractionValueQuotient R) :=
  (quotientRieszDualBilinMap R L hL).liftQ₂
    (LinearMap.range L.obj.adjoint) (LinearMap.range L.obj.adjoint)
    (adjointRange_le_ker_quotientRieszDual R L hL)
    (adjointRange_le_flipKer_quotientRieszDual R L hL)

/-- Tensor-hom form of the discriminant bilinear map. -/
noncomputable def discriminantForm (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    TensorProduct R L.obj.defect L.obj.defect →ₗ[R] FractionValueQuotient R :=
  (TensorProduct.lift.equiv (.id R) L.obj.defect L.obj.defect
    (FractionValueQuotient R)) (discriminantBilinMap R L hL)

/-- The discriminant module with its `Frac(R) / R`-valued bilinear form. -/
noncomputable def discriminantBilinObject (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    BilinModuleCat R (FractionValueQuotient R) :=
  op ⟨op (ModuleCat.of R L.obj.defect), discriminantForm R L hL⟩

omit [IsDomain R] in
@[simp]
theorem discriminantBilinMap_mk (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (f g : L.obj.valueDual) :
    discriminantBilinMap R L hL
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      fractionValueProjection R (rieszDualBilinMap R L hL f g) :=
  rfl

omit [IsDomain R] in
theorem rieszDualBilinMap_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    ∀ f g, rieszDualBilinMap R L hL f g = rieszDualBilinMap R L hL g f := by
  intro f g
  exact rationalizedForm_isSymmetric R L _ _

omit [IsDomain R] in
theorem discriminantBilinMap_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    ∀ x y, discriminantBilinMap R L hL x y = discriminantBilinMap R L hL y x := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    induction y using Submodule.Quotient.induction_on with
    | _ g =>
      change fractionValueProjection R (rieszDualBilinMap R L hL f g) =
        fractionValueProjection R (rieszDualBilinMap R L hL g f)
      rw [rieszDualBilinMap_isSymmetric]

omit [IsDomain R] in
theorem discriminantBilinObject_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    (discriminantBilinObject R L hL).IsSymmetric :=
  discriminantBilinMap_isSymmetric R L hL

/-- Generic nondegeneracy makes the integral adjoint injective. -/
theorem adjoint_injective_of_genericallyNondegenerate
    (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    Function.Injective L.obj.adjoint := by
  intro x y hxy
  letI : Module.Projective R L.obj.carrier := L.property.1
  apply Module.Flat.tensorProduct_mk_injective R L.obj.carrier
    (FractionRing R)
  change toRationalSpan R L x = toRationalSpan R L y
  rw [← rieszEmbedding_adjoint R L hL x]
  rw [← rieszEmbedding_adjoint R L hL y]
  exact congrArg (rieszEmbedding R L hL) hxy

/-- The discriminant module of a finite integer lattice is a torsion module. -/
theorem discriminant_isTorsion_int (L : IntegralLatticeCat ℤ)
    [Module.Finite ℤ L.obj.carrier]
    (hL : IsGenericallyNondegenerate ℤ L) :
    Module.IsTorsion ℤ L.obj.defect := by
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Free ℤ L.obj.carrier := inferInstance
  letI : Module.Finite ℤ L.obj.valueDual := inferInstance
  letI : Module.Free ℤ L.obj.valueDual := inferInstance
  have hinj := adjoint_injective_of_genericallyNondegenerate ℤ L hL
  have hrange : Module.finrank ℤ (LinearMap.range L.obj.adjoint) =
      Module.finrank ℤ L.obj.carrier :=
    (LinearEquiv.ofInjective L.obj.adjoint hinj).finrank_eq.symm
  let b := Module.Free.chooseBasis ℤ L.obj.carrier
  have hdual : Module.finrank ℤ L.obj.valueDual =
      Module.finrank ℤ L.obj.carrier := by
    rw [Module.finrank_eq_card_basis b.dualBasis]
    rw [Module.finrank_eq_card_basis b]
  have hfull : Module.finrank ℤ (LinearMap.range L.obj.adjoint) =
      Module.finrank ℤ L.obj.valueDual :=
    hrange.trans hdual.symm
  letI : Finite L.obj.defect :=
    Submodule.finiteQuotientOfFreeOfRankEq
      (LinearMap.range L.obj.adjoint) hfull
  exact (AddMonoid.isTorsion_iff_isTorsion_int).mp
    is_add_torsion_of_finite

/-- `A_L` in the category of finite symmetric `Frac(R) / R`-valued form modules. -/
noncomputable def discriminantFormModule (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    FiniteFormCat R (FractionValueQuotient R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  refine ⟨discriminantBilinObject R L hL, ?_⟩
  change Module.Finite R L.obj.defect ∧
    (discriminantBilinObject R L hL).IsSymmetric
  exact ⟨inferInstance, discriminantBilinObject_isSymmetric R L hL⟩

/-- A discriminant form with a proved torsion carrier. -/
noncomputable def discriminantTorsionFormModule
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L)
    (hT : Module.IsTorsion R L.obj.defect) :
    FiniteTorsionSymBilinModuleCat R (FractionValueQuotient R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  refine ⟨discriminantBilinObject R L hL, ?_⟩
  change Module.Finite R L.obj.defect ∧
    Module.IsTorsion R L.obj.defect ∧
    (discriminantBilinObject R L hL).IsSymmetric
  exact ⟨inferInstance, hT,
    discriminantBilinObject_isSymmetric R L hL⟩

/-- The integer discriminant form, with torsion proved from generic nondegeneracy. -/
noncomputable def discriminantTorsionFormModuleInt
    (L : IntegralLatticeCat ℤ) [Module.Finite ℤ L.obj.carrier]
    (hL : IsGenericallyNondegenerate ℤ L) :=
  discriminantTorsionFormModule ℤ L hL
    (discriminant_isTorsion_int L hL)

omit [IsDomain R] in
/-- The integral image is the integral span of a base-changed integral basis. -/
theorem integralImage_eq_span_baseChangeBasis
    (L : IntegralLatticeCat R) [Module.Free R L.obj.carrier]
    [Module.Finite R L.obj.carrier] :
    integralImage R L =
      Submodule.span R (Set.range
        ((Module.Free.chooseBasis R L.obj.carrier).baseChange
          (FractionRing R))) := by
  let b := Module.Free.chooseBasis R L.obj.carrier
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    apply Set.mem_range.mpr
    refine ⟨i, ?_⟩
    rw [Module.Basis.baseChange_apply]
    change 1 ⊗ₜ[R] b i = 1 ⊗ₜ[R] b i
    rfl
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, by simp [b, toRationalSpan]⟩

/-- The discriminant bilinear form of a finite free lattice has zero radical. -/
theorem discriminantBilinObject_isNondegenerate
    (L : IntegralLatticeCat R) [Module.Free R L.obj.carrier]
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    (discriminantBilinObject R L hL).IsNondegenerate := by
  rw [BilinModuleCat.isNondegenerate_iff_adjoint_injective]
  change Function.Injective (discriminantBilinMap R L hL)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    induction x using Submodule.Quotient.induction_on with
    | _ f =>
      change Submodule.Quotient.mk f = 0
      rw [Submodule.Quotient.mk_eq_zero]
      have hRationalNondegenerate :
          (rationalizedForm R L).Nondegenerate := by
        apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
        intro v hv
        apply hL.1
        apply LinearMap.ext
        intro y
        simpa using hv y
      have hRationalSymmetric : (rationalizedForm R L).IsSymm :=
        LinearMap.BilinForm.isSymm_def.mpr
          (rationalizedForm_isSymmetric R L)
      have hDoubleDual :=
        (rationalizedForm R L).dualSubmodule_dualSubmodule_of_basis
          (R := R) (S := FractionRing R)
          hRationalNondegenerate hRationalSymmetric
          ((Module.Free.chooseBasis R L.obj.carrier).baseChange
            (FractionRing R))
      rw [← integralImage_eq_span_baseChangeBasis R L] at hDoubleDual
      have hRieszInDoubleDual :
          rieszEmbedding R L hL f ∈
            (rationalizedForm R L).dualSubmodule (metricDual R L) := by
        rw [LinearMap.BilinForm.mem_dualSubmodule]
        intro y hy
        let yDual : metricDual R L := ⟨y, hy⟩
        let g := metricDualToValueDual R L yDual
        have hPair := LinearMap.congr_fun hx (Submodule.Quotient.mk g)
        change fractionValueProjection R
          (rieszDualBilinMap R L hL f g) = 0 at hPair
        have hyEq : rieszEmbedding R L hL g = y := by
          exact congrArg Subtype.val
            (rieszToMetricDual_metricDualToValueDual R L hL yDual)
        change fractionValueProjection R
          (rationalizedForm R L (rieszEmbedding R L hL f)
            (rieszEmbedding R L hL g)) = 0 at hPair
        rw [hyEq] at hPair
        rw [fractionValueProjection, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hPair
        rcases hPair with ⟨r, hr⟩
        exact Submodule.mem_one.mpr ⟨r, hr⟩
      have hRieszInIntegralImage :
          rieszEmbedding R L hL f ∈ integralImage R L := by
        rw [← hDoubleDual]
        exact hRieszInDoubleDual
      rcases hRieszInIntegralImage with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply (rieszMetricDualEquiv R L hL).injective
      apply Subtype.ext
      exact (rieszEmbedding_adjoint R L hL z).trans hz
  · exact bot_le

/-- The discriminant bilinear form of a finite free lattice is perfect. -/
theorem discriminantBilinObject_isPerfect
    (L : IntegralLatticeCat R) [Module.Free R L.obj.carrier]
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    (discriminantBilinObject R L hL).IsPerfect := by
  change Function.Bijective (discriminantBilinMap R L hL)
  refine ⟨(BilinModuleCat.isNondegenerate_iff_adjoint_injective
    (discriminantBilinObject R L hL)).mp
      (discriminantBilinObject_isNondegenerate R L hL), ?_⟩
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Projective R L.obj.valueDual := inferInstance
  intro φ
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (fractionValueProjection R) (φ.comp L.obj.defectProjection)
    (Submodule.mkQ_surjective _)
  let b := Module.Free.chooseBasis R L.obj.carrier
  let x : RationalSpan R L := ∑ i,
    g (b.dualBasis i) •
      (b.baseChange (FractionRing R) i)
  have hxPairing (f : L.obj.valueDual) :
      rationalizedForm R L x (rieszEmbedding R L hL f) = g f := by
    calc
      rationalizedForm R L x (rieszEmbedding R L hL f) =
          rationalizedForm R L (rieszEmbedding R L hL f) x :=
        rationalizedForm_isSymmetric R L _ _
      _ = ∑ i, g (b.dualBasis i) *
          rationalizedForm R L (rieszEmbedding R L hL f)
            (b.baseChange (FractionRing R) i) := by
        simp [x]
      _ = ∑ i, g (b.dualBasis i) *
          algebraMap R (FractionRing R) (f (b i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Module.Basis.baseChange_apply]
        change g (b.dualBasis i) *
          rationalizedForm R L (rieszEmbedding R L hL f)
            (toRationalSpan R L (b i)) = _
        rw [rationalizedForm_rieszEmbedding]
      _ = g f := by
        calc
          _ = ∑ i, (b.dualBasis.repr f i) • g (b.dualBasis i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [b.dualBasis_repr]
            rw [Algebra.smul_def, mul_comm]
          _ = g (∑ i, (b.dualBasis.repr f i) • b.dualBasis i) := by
            rw [map_sum]
            simp only [map_smul]
          _ = g f := by rw [b.dualBasis.sum_repr]
  have hxMetric : x ∈ metricDual R L := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rcases hy with ⟨z, rfl⟩
    have hLift := LinearMap.congr_fun hg (L.obj.adjoint z)
    have hDefect : L.obj.defectProjection (L.obj.adjoint z) = 0 := by
      rw [BilinModuleCat.defectProjection, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨z, rfl⟩
    change fractionValueProjection R (g (L.obj.adjoint z)) =
      φ (L.obj.defectProjection (L.obj.adjoint z)) at hLift
    rw [hDefect, map_zero] at hLift
    have hPairing := hxPairing (L.obj.adjoint z)
    rw [rieszEmbedding_adjoint] at hPairing
    rw [← hPairing, fractionValueProjection, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hLift
    rcases hLift with ⟨r, hr⟩
    exact Submodule.mem_one.mpr ⟨r, hr⟩
  let xDual : metricDual R L := ⟨x, hxMetric⟩
  let f := metricDualToValueDual R L xDual
  refine ⟨Submodule.Quotient.mk f, ?_⟩
  apply LinearMap.ext
  intro a
  induction a using Submodule.Quotient.induction_on with
  | _ k =>
    change fractionValueProjection R (rieszDualBilinMap R L hL f k) =
      φ (Submodule.Quotient.mk k)
    have hxEq : rieszEmbedding R L hL f = x := by
      exact congrArg Subtype.val
        (rieszToMetricDual_metricDualToValueDual R L hL xDual)
    change fractionValueProjection R
      (rationalizedForm R L (rieszEmbedding R L hL f)
        (rieszEmbedding R L hL k)) = _
    rw [hxEq, hxPairing]
    exact LinearMap.congr_fun hg k

/-- A finite free discriminant form with proved torsion and zero radical. -/
noncomputable def discriminantRadicalFreeTorsionFormModule
    (L : IntegralLatticeCat R) [Module.Free R L.obj.carrier]
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L)
    (hT : Module.IsTorsion R L.obj.defect) :
    RadicalFreeFiniteTorsionBilinModuleCat R (FractionValueQuotient R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  refine ⟨discriminantBilinObject R L hL, ?_⟩
  change Module.Finite R L.obj.defect ∧ Module.IsTorsion R L.obj.defect ∧
    (discriminantBilinObject R L hL).IsSymmetric ∧
    (discriminantBilinObject R L hL).IsNondegenerate
  exact ⟨inferInstance, hT, discriminantBilinObject_isSymmetric R L hL,
    discriminantBilinObject_isNondegenerate R L hL⟩

/-- The integer discriminant form in the radical-free finite torsion category. -/
noncomputable def discriminantRadicalFreeTorsionFormModuleInt
    (L : IntegralLatticeCat ℤ) [Module.Finite ℤ L.obj.carrier]
    (hL : IsGenericallyNondegenerate ℤ L) :=
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Free ℤ L.obj.carrier := inferInstance
  discriminantRadicalFreeTorsionFormModule ℤ L hL
    (discriminant_isTorsion_int L hL)

/-- A finite free discriminant form in the nonsingular torsion category. -/
noncomputable def discriminantNonsingularTorsionFormModule
    (L : IntegralLatticeCat R) [Module.Free R L.obj.carrier]
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L)
    (hT : Module.IsTorsion R L.obj.defect) :
    NonsingularFiniteTorsionBilinModuleCat R (FractionValueQuotient R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  refine ⟨discriminantBilinObject R L hL, ?_⟩
  change Module.Finite R L.obj.defect ∧ Module.IsTorsion R L.obj.defect ∧
    (discriminantBilinObject R L hL).IsSymmetric ∧
    (discriminantBilinObject R L hL).IsPerfect
  exact ⟨inferInstance, hT, discriminantBilinObject_isSymmetric R L hL,
    discriminantBilinObject_isPerfect R L hL⟩

/-- The integer discriminant form in the nonsingular finite torsion category. -/
noncomputable def discriminantNonsingularTorsionFormModuleInt
    (L : IntegralLatticeCat ℤ) [Module.Finite ℤ L.obj.carrier]
    (hL : IsGenericallyNondegenerate ℤ L) :=
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Free ℤ L.obj.carrier := inferInstance
  discriminantNonsingularTorsionFormModule ℤ L hL
    (discriminant_isTorsion_int L hL)

/-- The Riesz model after projection of its values to `Frac(R) / R`. -/
noncomputable def projectedRieszDualLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    LatticeCat R (FractionValueQuotient R) :=
  (changeValue R (FractionRing R) (fractionValueProjection R)).obj
    (rieszDualLattice R L hL)

/-- The projected Riesz model, regarded as a finite symmetric form module. -/
noncomputable def projectedRieszDualFiniteForm (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    FiniteFormCat R (FractionValueQuotient R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Finite R L.obj.valueDual := inferInstance
  refine ⟨(projectedRieszDualLattice R L hL).obj, ?_⟩
  change Module.Finite R L.obj.valueDual ∧
    (projectedRieszDualLattice R L hL).obj.IsSymmetric
  exact ⟨inferInstance, (projectedRieszDualLattice R L hL).property.2⟩

/-- The quotient projection `L♯ → A_L` preserves the projected forms. -/
noncomputable def discriminantProjectionBilin (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    (projectedRieszDualLattice R L hL).obj ⟶ discriminantBilinObject R L hL := by
  refine Quiver.Hom.op (CategoryOfElements.homMk _ _
    (op (ModuleCat.ofHom L.obj.defectProjection)) ?_)
  dsimp [bilinearForms]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => rfl
  | add x y hx hy => simp [hx, hy]

/-- The quotient projection `L♯ → A_L` in the finite-form category. -/
noncomputable def discriminantProjection (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) :
    projectedRieszDualFiniteForm R L hL ⟶ discriminantFormModule R L hL :=
  ObjectProperty.homMk (discriminantProjectionBilin R L hL)

/-- The associated quadratic map `q(x) = b_A(x,x)` on the discriminant module. -/
noncomputable def discriminantQuadraticMap (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    QuadraticMap R L.obj.defect (FractionValueQuotient R) :=
  (discriminantBilinMap R L hL).toQuadraticMap

omit [IsDomain R] in
@[simp]
theorem discriminantQuadraticMap_apply (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (x : L.obj.defect) :
    discriminantQuadraticMap R L hL x = discriminantBilinMap R L hL x x :=
  rfl

omit [IsDomain R] in
/-- The module sequence from the radical through the adjoint and its cokernel is exact. -/
theorem adjointModuleSequenceExact (L : IntegralLatticeCat R) :
    Function.Injective L.obj.radicalInclusion ∧
      Function.Exact L.obj.radicalInclusion L.obj.adjoint ∧
      Function.Exact L.obj.adjoint L.obj.defectProjection ∧
      Function.Surjective L.obj.defectProjection :=
  ⟨L.obj.radicalInclusion_injective, L.obj.exact_radical_adjoint,
    L.obj.exact_adjoint_defect, L.obj.defectProjection_surjective⟩

theorem toRationalSpan_injective (L : IntegralLatticeCat R) :
    Function.Injective (toRationalSpan R L) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  exact Module.Flat.tensorProduct_mk_injective R L.obj.carrier (FractionRing R)

theorem exact_radical_toMetricDual_iff (L : IntegralLatticeCat R) :
    Function.Exact L.obj.radicalInclusion (toMetricDual R L) ↔
      L.obj.IsNondegenerate := by
  rw [LinearMap.exact_iff]
  have hker : LinearMap.ker (toMetricDual R L) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx0 : x = 0 := (toMetricDual_injective R L) (by simpa using hx)
      simp [hx0]
    · exact bot_le
  have hrange : LinearMap.range L.obj.radicalInclusion = L.obj.radical :=
    Submodule.range_subtype L.obj.radical
  rw [hker, hrange]
  exact eq_comm

/-- The radical-to-metric-dual sequence is exact for a nondegenerate lattice. -/
theorem exact_radical_toMetricDual (L : IntegralLatticeCat R)
    (hL : L.obj.IsNondegenerate) :
    Function.Exact L.obj.radicalInclusion (toMetricDual R L) := by
  exact (exact_radical_toMetricDual_iff R L).mpr hL

/-- The metric-dual map followed by the carrier map of the formed cokernel is exact. -/
theorem exact_toMetricDual_discriminantCarrier (L : IntegralLatticeCat R) :
    Function.Exact (toMetricDual R L)
      (BilWFormCat.carrierMap (discriminantSymBilWFormProjection R L).hom).hom := by
  exact BilWFormCat.exact_carrierMap_cokernelCarrierProjection
    (toMetricDualSymBilWForm R L).hom

/-- The carrier map of the formed discriminant projection is surjective. -/
theorem discriminantCarrierProjection_surjective (L : IntegralLatticeCat R) :
    Function.Surjective
      (BilWFormCat.carrierMap (discriminantSymBilWFormProjection R L).hom).hom := by
  exact BilWFormCat.cokernelCarrierProjection_surjective
    (toMetricDualSymBilWForm R L).hom

/--
The underlying module sequence
`0 → rad(L) → L → L♯ → A(L) → 0` is exact for a nondegenerate lattice.
-/
theorem discriminantCarrierModuleSequenceExact (L : IntegralLatticeCat R)
    (hL : L.obj.IsNondegenerate) :
    Function.Injective L.obj.radicalInclusion ∧
      Function.Exact L.obj.radicalInclusion (toMetricDual R L) ∧
      Function.Exact (toMetricDual R L)
        (BilWFormCat.carrierMap (discriminantSymBilWFormProjection R L).hom).hom ∧
      Function.Surjective
        (BilWFormCat.carrierMap (discriminantSymBilWFormProjection R L).hom).hom :=
  ⟨L.obj.radicalInclusion_injective, exact_radical_toMetricDual R L hL,
    exact_toMetricDual_discriminantCarrier R L,
    discriminantCarrierProjection_surjective R L⟩

end LeanCategories.Lattices.Valued
