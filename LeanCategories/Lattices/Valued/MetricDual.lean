/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IdealDual

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

/-- The algebraic dual `Hom_R(L,R)` of an integral lattice. -/
abbrev algebraicDual (L : IntegralLatticeCat R) := L.obj.valueDual

/-- The pairing map from an integral lattice to its algebraic dual. -/
abbrev toAlgebraicDual (L : IntegralLatticeCat R) :
    L.obj.carrier →ₗ[R] algebraicDual R L :=
  L.obj.adjoint

/-- The metric dual as a submodule of the rational span. -/
noncomputable abbrev metricDual (L : IntegralLatticeCat R) :
    Submodule R (RationalSpan R L) :=
  (rationalizedForm R L).dualSubmodule (integralImage R L)

/-- The specified inclusion `L♯ → L ⊗_R Frac(R)`. -/
noncomputable def metricDualInclusion (L : IntegralLatticeCat R) :
    metricDual R L →ₗ[R] RationalSpan R L :=
  (metricDual R L).subtype

/-- The canonical map `L → L♯`. -/
noncomputable def toMetricDual (L : IntegralLatticeCat R) :
    L.obj.carrier →ₗ[R] metricDual R L :=
  LinearMap.codRestrict (metricDual R L) (toRationalSpan R L) (by
    intro x
    change (toRationalSpan R L) x ∈
      (rationalizedForm R L).dualSubmodule (integralImage R L)
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rcases hy with ⟨y, rfl⟩
    refine Submodule.mem_one.mpr ⟨L.obj.pairing x y, ?_⟩
    change algebraMap R (FractionRing R) (L.obj.pairing x y) =
      rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
    rw [rationalizedForm_tmul]
    simp)

/-- A lattice is unimodular when its metric dual equals its integral image. -/
noncomputable def IsUnimodular (L : IntegralLatticeCat R) : Prop :=
  metricDual R L = integralImage R L

/-- Metric-dual equality is equivalent to surjectivity of the canonical inclusion. -/
theorem isUnimodular_iff_toMetricDual_surjective (L : IntegralLatticeCat R) :
    IsUnimodular R L ↔ Function.Surjective (toMetricDual R L) := by
  constructor
  · intro h v
    have hv : (v : RationalSpan R L) ∈ integralImage R L := h ▸ v.property
    rcases hv with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  · intro h
    apply le_antisymm
    · intro v hv
      obtain ⟨x, hx⟩ := h ⟨v, hv⟩
      exact ⟨x, congrArg Subtype.val hx⟩
    · intro v hv
      rcases hv with ⟨x, rfl⟩
      exact (toMetricDual R L x).property

/-- The form over the fraction field is nondegenerate when both radicals vanish. -/
def IsFractionFieldNondegenerate (L : IntegralLatticeCat R) : Prop :=
  (rationalizedForm R L).Nondegenerate

/-- The form over the fraction field is perfect when its correlation map is an isomorphism.
This does not say that the integral adjoint is a primitive embedding. -/
def IsFractionFieldPerfect (L : IntegralLatticeCat R) : Prop :=
  Function.Bijective (rationalizedForm R L)

/-- For a finite-projective lattice, fraction-field nondegeneracy equals perfection. -/
theorem isFractionFieldNondegenerate_iff_isFractionFieldPerfect
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier] :
    IsFractionFieldNondegenerate R L ↔ IsFractionFieldPerfect R L := by
  let B := rationalizedForm R L
  letI : Module.Finite (FractionRing R) (RationalSpan R L) := inferInstance
  constructor
  · intro hB
    let e := B.toDual hB
    have he : B = e.toLinearMap := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact (LinearMap.BilinForm.toDual_def hB).symm
    change Function.Bijective B
    rw [he]
    exact e.bijective
  · intro hB
    have hseparating : B.SeparatingLeft := by
      intro x hx
      apply hB.1
      apply LinearMap.ext
      intro y
      simpa only [map_zero, LinearMap.zero_apply] using hx y
    exact LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hseparating

/-- Finite projective integral lattices whose fraction-field form is perfect. -/
def isFractionFieldPerfectFiniteProjectiveLattice :
    ObjectProperty (FiniteProjectiveLatticeCat R R) :=
  fun L ↦ IsFractionFieldPerfect R L.obj

/-- Finite projective integral lattices whose fraction-field form is perfect. -/
abbrev FractionFieldPerfectFiniteProjectiveLatticeCat :=
  (isFractionFieldPerfectFiniteProjectiveLattice R).FullSubcategory

/-- Finite projective integral lattices whose generic-fiber form is nondegenerate. -/
def isGenericallyNondegenerateLattice :
    ObjectProperty (FiniteProjectiveLatticeCat R R) :=
  fun L ↦ IsFractionFieldNondegenerate R L.obj

/-- The full category of generically nondegenerate finite projective lattices. -/
abbrev GenericallyNondegenerateLatticeCat :=
  (isGenericallyNondegenerateLattice R).FullSubcategory

/-- Forget generic-fiber nondegeneracy. -/
def genericallyNondegenerateForget :
    GenericallyNondegenerateLatticeCat R ⥤ FiniteProjectiveLatticeCat R R :=
  (isGenericallyNondegenerateLattice R).ι

/-- Forget generic-fiber perfection while retaining finite projectivity. -/
def fractionFieldPerfectFiniteProjectiveToFiniteProjective :
    FractionFieldPerfectFiniteProjectiveLatticeCat R ⥤ FiniteProjectiveLatticeCat R R :=
  (isFractionFieldPerfectFiniteProjectiveLattice R).ι

/-- Unimodular finite projective lattices whose fraction-field form is perfect. -/
noncomputable def isUnimodularFiniteProjectiveLattice :
    ObjectProperty (FractionFieldPerfectFiniteProjectiveLatticeCat R) :=
  fun L ↦ IsUnimodular R L.obj.obj

/-- The full category of unimodular finite projective lattices. -/
noncomputable abbrev UnimodularLatticeCat :=
  (isUnimodularFiniteProjectiveLattice R).FullSubcategory

/-- Forget unimodularity while retaining generic-fiber perfection. -/
def unimodularForget :
    UnimodularLatticeCat R ⥤ FractionFieldPerfectFiniteProjectiveLatticeCat R :=
  (isUnimodularFiniteProjectiveLattice R).ι

/-- Forget finiteness and fraction-field perfection while retaining the integral lattice. -/
def fractionFieldPerfectFiniteProjectiveForget :
    FractionFieldPerfectFiniteProjectiveLatticeCat R ⥤ IntegralLatticeCat R :=
  (isFractionFieldPerfectFiniteProjectiveLattice R).ι ⋙
    (isFiniteProjectiveLattice R R).ι

omit [IsDomain R] in
/-- A base-changed basis maps the integral Gram matrix into the fraction field. -/
theorem rationalizedForm_toMatrix {I : Type*} [Fintype I]
    [DecidableEq I] (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) :
    LinearMap.BilinForm.toMatrix
      (b.baseChange (FractionRing R)) (rationalizedForm R L) =
        (algebraMap R (FractionRing R)).mapMatrix (gramMatrix L b) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, gramMatrix, Algebra.smul_def]

/-- A finite Gram determinant is nonzero exactly when the fraction-field form is perfect. -/
theorem isFractionFieldPerfect_iff_determinant_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) :
    IsFractionFieldPerfect R L ↔ determinant L b ≠ 0 := by
  let bK := b.baseChange (FractionRing R)
  let B := rationalizedForm R L
  letI : Module.Finite (FractionRing R) (RationalSpan R L) :=
    Module.Finite.of_basis bK
  have hmatrix : LinearMap.BilinForm.toMatrix bK B =
      (algebraMap R (FractionRing R)).mapMatrix (gramMatrix L b) :=
    rationalizedForm_toMatrix R L b
  constructor
  · intro hB
    have hseparating : B.SeparatingLeft := by
      intro x hx
      apply hB.1
      apply LinearMap.ext
      intro y
      simpa [B] using hx y
    have hnondegenerate : B.Nondegenerate :=
      LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hseparating
    have hdet :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bK).mp
        hnondegenerate
    rw [hmatrix, ← RingHom.map_det] at hdet
    simpa [determinant] using hdet
  · intro hdet
    have hdetK : (LinearMap.BilinForm.toMatrix bK B).det ≠ 0 := by
      rw [hmatrix, ← RingHom.map_det]
      simpa [determinant] using hdet
    have hnondegenerate : B.Nondegenerate :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bK).mpr hdetK
    let e := B.toDual hnondegenerate
    have he : B = e.toLinearMap := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact (LinearMap.BilinForm.toDual_def hnondegenerate).symm
    change Function.Bijective B
    rw [he]
    exact e.bijective

/-- The Riesz equivalence supplied by the extended form and fraction-field perfection. -/
noncomputable def rationalAdjointEquiv (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    RationalSpan R L ≃ₗ[FractionRing R]
      Module.Dual (FractionRing R) (RationalSpan R L) :=
  LinearEquiv.ofBijective (rationalizedForm R L) hL

/-- The Riesz realization of `Hom_R(L,R)` inside the rational span. -/
noncomputable def rieszEmbedding (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    L.obj.valueDual →ₗ[R] RationalSpan R L :=
  (rationalAdjointEquiv R L hL).symm.toLinearMap.restrictScalars R ∘ₗ
    Module.Dual.baseChange (FractionRing R)

/-- The extended form, restricted to `R`-scalars. -/
noncomputable def restrictedRationalizedForm (L : IntegralLatticeCat R) :
    LinearMap.BilinMap R (RationalSpan R L) (FractionRing R) :=
  LinearMap.mk₂ R (fun x y ↦ rationalizedForm R L x y)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)

/-- The form on `Hom_R(L,R)` transported through its Riesz realization. -/
noncomputable def rieszDualBilinMap (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    LinearMap.BilinMap R L.obj.valueDual (FractionRing R) :=
  (restrictedRationalizedForm R L).compl₁₂
    (rieszEmbedding R L hL) (rieszEmbedding R L hL)

/-- Tensor-hom form transported to `Hom_R(L,R)` by the Riesz realization. -/
noncomputable def rieszDualForm (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    TensorProduct R L.obj.valueDual L.obj.valueDual →ₗ[R] FractionRing R :=
  (TensorProduct.lift.equiv (.id R) L.obj.valueDual L.obj.valueDual
    (FractionRing R)) (rieszDualBilinMap R L hL)

/-- `Hom_R(L,R)` with the form supplied by `b_K` and its Riesz equivalence. -/
noncomputable def rieszDualBilinObject (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    BilinModuleCat R (FractionRing R) :=
  op ⟨op (ModuleCat.of R L.obj.valueDual), rieszDualForm R L hL⟩

omit [IsDomain R] in
theorem rationalizedForm_isSymmetric (L : IntegralLatticeCat R) :
    ∀ x y, rationalizedForm R L x y = rationalizedForm R L y x := by
  intro x y
  have hsymm : ∀ a b, L.obj.bilinMap a b = L.obj.bilinMap b a := by
    intro a b
    exact L.property.2 a b
  change (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
      (FractionRing R))
      (LinearMap.BilinMap.baseChange (FractionRing R) L.obj.bilinMap x y) =
    (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
      (FractionRing R))
      (LinearMap.BilinMap.baseChange (FractionRing R) L.obj.bilinMap y x)
  rw [LinearMap.BilinMap.baseChange_isSymm hsymm]

omit [IsDomain R] in
theorem rieszDualBilinObject_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    (rieszDualBilinObject R L hL).IsSymmetric := by
  intro f g
  exact rationalizedForm_isSymmetric R L _ _

omit [IsDomain R] in
theorem rieszEmbedding_adjoint (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (x : L.obj.carrier) :
    rieszEmbedding R L hL (L.obj.adjoint x) = toRationalSpan R L x := by
  apply (rationalAdjointEquiv R L hL).injective
  simp only [rieszEmbedding, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    toRationalSpan]
  change (rationalAdjointEquiv R L hL)
      ((rationalAdjointEquiv R L hL).symm
        (Module.Dual.baseChange (FractionRing R) (L.obj.adjoint x))) =
    (rationalAdjointEquiv R L hL) (1 ⊗ₜ[R] x)
  rw [LinearEquiv.apply_symm_apply]
  change Module.Dual.baseChange (FractionRing R) (L.obj.adjoint x) =
    rationalizedForm R L (1 ⊗ₜ[R] x)
  ext z
  simp [BilinModuleCat.adjoint]

omit [IsDomain R] in
theorem rieszDualBilinMap_adjoint (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (x y : L.obj.carrier) :
    rieszDualBilinMap R L hL (L.obj.adjoint x) (L.obj.adjoint y) =
      algebraMap R (FractionRing R) (L.obj.pairing x y) := by
  change rationalizedForm R L
    (rieszEmbedding R L hL (L.obj.adjoint x))
    (rieszEmbedding R L hL (L.obj.adjoint y)) = _
  rw [rieszEmbedding_adjoint, rieszEmbedding_adjoint]
  change rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) = _
  rw [rationalizedForm_tmul]
  simp

/-- Change an integral form from `R`-values to `Frac(R)`-values. -/
noncomputable def fractionValuedLattice (L : IntegralLatticeCat R) :
    LatticeCat R (FractionRing R) :=
  (changeValue R R (Algebra.linearMap R (FractionRing R))).obj L

/-- The Riesz model of `L♯`: `Hom_R(L,R)` with the form induced by `b_K`. -/
noncomputable def rieszDualLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsFractionFieldPerfect R L) :
    LatticeCat R (FractionRing R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  refine ⟨rieszDualBilinObject R L hL, ?_⟩
  change Module.Projective R L.obj.valueDual ∧
    (rieszDualBilinObject R L hL).IsSymmetric
  exact ⟨inferInstance, rieszDualBilinObject_isSymmetric R L hL⟩

/-- The adjoint is an isometry after changing values to `Frac(R)`. -/
noncomputable def toRieszDualBilin (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    (fractionValuedLattice R L).obj ⟶ rieszDualBilinObject R L hL := by
  refine Quiver.Hom.op (CategoryOfElements.homMk _ _
    (op (ModuleCat.ofHom L.obj.adjoint)) ?_)
  dsimp [bilinearForms]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    exact rieszDualBilinMap_adjoint R L hL x y
  | add x y hx hy => simp [hx, hy]

/-- The adjoint `L → L♯` in the category of `Frac(R)`-valued `R`-lattices. -/
noncomputable def toRieszDual (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsFractionFieldPerfect R L) :
    fractionValuedLattice R L ⟶ rieszDualLattice R L hL :=
  ObjectProperty.homMk (toRieszDualBilin R L hL)

omit [IsDomain R] in
theorem rationalizedForm_rieszEmbedding (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (f : L.obj.valueDual)
    (x : L.obj.carrier) :
    rationalizedForm R L (rieszEmbedding R L hL f) (toRationalSpan R L x) =
      algebraMap R (FractionRing R) (f x) := by
  change (rationalAdjointEquiv R L hL) (rieszEmbedding R L hL f)
      (1 ⊗ₜ[R] x) = _
  simp [rieszEmbedding, Algebra.smul_def]

/-- The Riesz model maps into the metric-dual submodule of the rational span. -/
noncomputable def rieszToMetricDual (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    L.obj.valueDual →ₗ[R] metricDual R L :=
  LinearMap.codRestrict (metricDual R L) (rieszEmbedding R L hL) (by
    intro f
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rcases hy with ⟨y, rfl⟩
    refine Submodule.mem_one.mpr ⟨f y, ?_⟩
    exact (rationalizedForm_rieszEmbedding R L hL f y).symm)

@[simp]
theorem rieszToMetricDual_coe (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (f : L.obj.valueDual) :
    (rieszToMetricDual R L hL f : RationalSpan R L) = rieszEmbedding R L hL f :=
  rfl

/-- The integral lattice mapped onto its image in the rational span. -/
def toIntegralImage (L : IntegralLatticeCat R) :
    L.obj.carrier →ₗ[R] integralImage R L :=
  (toRationalSpan R L).rangeRestrict

/-- A metric-dual vector defines an `R`-linear functional by integral pairing. -/
noncomputable def metricDualToValueDual (L : IntegralLatticeCat R) :
    metricDual R L →ₗ[R] L.obj.valueDual where
  toFun v := ((rationalizedForm R L).dualSubmoduleToDual
    (integralImage R L) v).comp (toIntegralImage R L)
  map_add' v w := by
    ext x
    simp [toIntegralImage]
  map_smul' r v := by
    ext x
    simp [toIntegralImage]

theorem metricDualToValueDual_rieszToMetricDual (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (f : L.obj.valueDual) :
    metricDualToValueDual R L (rieszToMetricDual R L hL f) = f := by
  ext x
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  change algebraMap R (FractionRing R)
      ((rationalizedForm R L).dualSubmoduleParing
        (rieszToMetricDual R L hL f) (toIntegralImage R L x)) =
    algebraMap R (FractionRing R) (f x)
  rw [LinearMap.BilinForm.dualSubmoduleParing_spec]
  exact rationalizedForm_rieszEmbedding R L hL f x

theorem rieszToMetricDual_metricDualToValueDual (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (v : metricDual R L) :
    rieszToMetricDual R L hL (metricDualToValueDual R L v) = v := by
  apply Subtype.ext
  apply (rationalAdjointEquiv R L hL).injective
  change (rationalAdjointEquiv R L hL)
      ((rationalAdjointEquiv R L hL).symm
        (Module.Dual.baseChange (FractionRing R) (metricDualToValueDual R L v))) =
    rationalizedForm R L v
  rw [LinearEquiv.apply_symm_apply]
  ext x
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply]
  simp only [LinearMap.coe_restrictScalars]
  rw [Module.Dual.baseChange_apply_tmul]
  simp only [Algebra.smul_def, mul_one]
  change algebraMap R (FractionRing R)
      ((rationalizedForm R L).dualSubmoduleParing v (toIntegralImage R L x)) =
    rationalizedForm R L v (1 ⊗ₜ[R] x)
  exact (rationalizedForm R L).dualSubmoduleParing_spec v (toIntegralImage R L x)

/-- The Riesz model and the metric-dual submodule are isomorphic as `R`-modules. -/
noncomputable def rieszMetricDualEquiv (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    L.obj.valueDual ≃ₗ[R] metricDual R L :=
  { toLinearMap := rieszToMetricDual R L hL
    invFun := metricDualToValueDual R L
    left_inv := metricDualToValueDual_rieszToMetricDual R L hL
    right_inv := rieszToMetricDual_metricDualToValueDual R L hL }

@[simp]
theorem rieszMetricDualEquiv_adjoint (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (x : L.obj.carrier) :
    rieszMetricDualEquiv R L hL (L.obj.adjoint x) = toMetricDual R L x := by
  apply Subtype.ext
  change rieszEmbedding R L hL (L.obj.adjoint x) = toRationalSpan R L x
  exact rieszEmbedding_adjoint R L hL x

/-- The canonical map from a projective lattice to its metric dual is injective. -/
theorem toMetricDual_injective (L : IntegralLatticeCat R) :
    Function.Injective (toMetricDual R L) := by
  intro x y hxy
  letI : Module.Projective R L.obj.carrier := L.property.1
  apply Module.Flat.tensorProduct_mk_injective R L.obj.carrier (FractionRing R)
  exact congrArg Subtype.val hxy

/-- For a lattice with perfect generic fiber, perfectness equals unimodularity. -/
theorem isPerfect_iff_isUnimodular (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) :
    L.obj.IsPerfect ↔ IsUnimodular R L := by
  rw [L.obj.isPerfect_iff_adjoint_bijective_of_isSymmetric L.property.2]
  rw [isUnimodular_iff_toMetricDual_surjective]
  let e := rieszMetricDualEquiv R L hL
  constructor
  · intro h v
    obtain ⟨x, hx⟩ := h.2 (e.symm v)
    refine ⟨x, ?_⟩
    rw [← rieszMetricDualEquiv_adjoint R L hL]
    simpa only [LinearEquiv.apply_symm_apply] using congrArg e hx
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply toMetricDual_injective R L
      rw [← rieszMetricDualEquiv_adjoint R L hL,
        ← rieszMetricDualEquiv_adjoint R L hL, hxy]
    · intro f
      obtain ⟨x, hx⟩ := h (e f)
      refine ⟨x, e.injective ?_⟩
      rw [rieszMetricDualEquiv_adjoint R L hL]
      exact hx

/-- The restriction of `b_K` to the metric-dual submodule. -/
noncomputable def metricDualBilinMap (L : IntegralLatticeCat R) :
    LinearMap.BilinMap R (metricDual R L) (FractionRing R) :=
  (restrictedRationalizedForm R L).compl₁₂
    (metricDualInclusion R L) (metricDualInclusion R L)

/-- Tensor-hom form on the metric-dual submodule. -/
noncomputable def metricDualForm (L : IntegralLatticeCat R) :
    TensorProduct R (metricDual R L) (metricDual R L) →ₗ[R] FractionRing R :=
  (TensorProduct.lift.equiv (.id R) (metricDual R L) (metricDual R L)
    (FractionRing R)) (metricDualBilinMap R L)

/-- The metric dual as a bilinear object, using the restriction of `b_K`. -/
noncomputable def metricDualBilinObject (L : IntegralLatticeCat R) :
    BilinModuleCat R (FractionRing R) :=
  op ⟨op (ModuleCat.of R (metricDual R L)), metricDualForm R L⟩

theorem metricDualBilinObject_isSymmetric (L : IntegralLatticeCat R) :
    (metricDualBilinObject R L).IsSymmetric := by
  intro x y
  change metricDualBilinMap R L x y = metricDualBilinMap R L y x
  change rationalizedForm R L (metricDualInclusion R L x) (metricDualInclusion R L y) =
    rationalizedForm R L (metricDualInclusion R L y) (metricDualInclusion R L x)
  exact rationalizedForm_isSymmetric R L _ _

/--
The metric dual as a formed lattice.

This construction requires a finite carrier and a bijective rational adjoint.
It does not require the original integral form to be nondegenerate over `R`.
-/
noncomputable def metricDualLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier]
    (hL : IsFractionFieldPerfect R L) :
    LatticeCat R (FractionRing R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Finite R L.obj.valueDual := inferInstance
  letI : Module.Projective R L.obj.valueDual := inferInstance
  refine ⟨metricDualBilinObject R L, ?_⟩
  change Module.Projective R (metricDual R L) ∧
    (metricDualBilinObject R L).IsSymmetric
  exact ⟨Module.Projective.of_equiv' (rieszMetricDualEquiv R L hL),
    metricDualBilinObject_isSymmetric R L⟩

/-- The inclusion `L → L♯` preserves the `Frac(R)`-valued forms. -/
noncomputable def toMetricDualBilin (L : IntegralLatticeCat R) :
    (fractionValuedLattice R L).obj ⟶ metricDualBilinObject R L := by
  refine Quiver.Hom.op (CategoryOfElements.homMk _ _
    (op (ModuleCat.ofHom (toMetricDual R L))) ?_)
  dsimp [bilinearForms]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) =
      algebraMap R (FractionRing R) (L.obj.pairing x y)
    rw [rationalizedForm_tmul]
    simp
  | add x y hx hy => simp [hx, hy]

/-- An integral lattice in the total category of symmetric variable-valued forms. -/
noncomputable def integralSymBilWFormObject (L : IntegralLatticeCat R) : SymBilWFormCat R :=
  ⟨BilWFormCat.of (ModuleCat.of R L.obj.carrier) (ModuleCat.of R R) L.obj.form,
    L.property.2⟩

/-- The metric dual in the total category of symmetric variable-valued forms. -/
noncomputable def metricDualSymBilWFormObject (L : IntegralLatticeCat R) : SymBilWFormCat R :=
  ⟨⟨ModuleCat.of R (FractionRing R), metricDualBilinObject R L⟩,
    metricDualBilinObject_isSymmetric R L⟩

/-- The inclusion into the metric dual, with values changed from `R` to `Frac(R)`. -/
noncomputable def toMetricDualSymBilWForm (L : IntegralLatticeCat R) :
    integralSymBilWFormObject R L ⟶ metricDualSymBilWFormObject R L :=
  ObjectProperty.homMk
    (BilWFormCat.homMk (toMetricDual R L) (Algebra.linearMap R (FractionRing R)) (by
      intro x y
      change algebraMap R (FractionRing R) (L.obj.pairing x y) =
        rationalizedForm R L (toRationalSpan R L x) (toRationalSpan R L y)
      change algebraMap R (FractionRing R) (L.obj.pairing x y) =
        rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
      rw [rationalizedForm_tmul]
      simp))

end LeanCategories.Lattices.Valued
