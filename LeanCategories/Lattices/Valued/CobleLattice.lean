/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspHomFibre
public import LeanCategories.Lattices.Valued.CuspDescent
public import LeanCategories.Lattices.Valued.Standard
public import LeanCategories.Lattices.Valued.SmithNormalForm

/-!
# The Coble lattice `T_Co`, its discriminant form and its cusps (#115)

`T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(2)` is presented here on `Fin 13 → ℤ` as twice a unimodular lattice: the
form is `2 • S`, where `S` is the Gram matrix of `⟨1⟩ ⊕ U ⊕ U ⊕ E₈`. Doubling a unimodular form
gives an even form whose discriminant module is the `2`-torsion quotient, which keeps every
hypothesis of the cusp machinery computable from an explicit integer matrix.

The two hyperbolic planes are part of the definition: a single `U(2)` summand would give a lattice
of signature `(10, 1)`, in which no rank-2 totally isotropic sublattice — and so no 1-cusp —
exists.

The file records, in order:

* the lattice `cobleLattice`, its evenness and fraction-field perfection;
* the quadratic discriminant form `cobleQuadraticDiscriminant` and the representation
  `cobleRho : O(T_Co) →* O(q)`, with the finiteness of `O(q)`;
* the orientation subgroup `cobleOrientationSubgroup` (`det = 1`, of index at most two) and
  `Γ_Co = O⁺(T_Co) ∩ ker ρ`;
* the cusp objects `cobleCuspKernel` and `cobleCuspGamma` with their rank-1 and rank-2 orbit sets.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

-- Pin the quotient module instance of the discriminant carrier, so that the quadratic
-- discriminant object and its orthogonal group see the same `ℤ`-module structure.
attribute [local instance 10000] Submodule.Quotient.module

/-! ## The unimodular half of the form -/

/-- The Gram matrix of `⟨1⟩ ⊕ U ⊕ U ⊕ E₈`: blocks of sizes `1`, `2`, `2`, `8`. -/
noncomputable def cobleHalfMatrix : Matrix (Fin 13) (Fin 13) ℤ :=
  ![
    ![  1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   0,   0,   1,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   0,   0,   0,   2,   0,  -1,   0,   0,   0,   0,   0],
    ![  0,   0,   0,   0,   0,   0,   2,   0,  -1,   0,   0,   0,   0],
    ![  0,   0,   0,   0,   0,  -1,   0,   2,  -1,   0,   0,   0,   0],
    ![  0,   0,   0,   0,   0,   0,  -1,  -1,   2,  -1,   0,   0,   0],
    ![  0,   0,   0,   0,   0,   0,   0,   0,  -1,   2,  -1,   0,   0],
    ![  0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,   2,  -1,   0],
    ![  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,   2,  -1],
    ![  0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,   2]]

/-- The integral inverse of `cobleHalfMatrix`. -/
noncomputable def cobleHalfMatrixInverse : Matrix (Fin 13) (Fin 13) ℤ :=
  ![
    ![  1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   0,   0,   1,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,   0,   0,   0,   4,   5,   7,  10,   8,   6,   4,   2],
    ![  0,   0,   0,   0,   0,   5,   8,  10,  15,  12,   9,   6,   3],
    ![  0,   0,   0,   0,   0,   7,  10,  14,  20,  16,  12,   8,   4],
    ![  0,   0,   0,   0,   0,  10,  15,  20,  30,  24,  18,  12,   6],
    ![  0,   0,   0,   0,   0,   8,  12,  16,  24,  20,  15,  10,   5],
    ![  0,   0,   0,   0,   0,   6,   9,  12,  18,  15,  12,   8,   4],
    ![  0,   0,   0,   0,   0,   4,   6,   8,  12,  10,   8,   6,   3],
    ![  0,   0,   0,   0,   0,   2,   3,   4,   6,   5,   4,   3,   2]]

/-- The displayed inverse is a right inverse. -/
theorem cobleHalfMatrix_mul_inverse :
    cobleHalfMatrix * cobleHalfMatrixInverse = 1 := by
  decide

/-- The half form is symmetric. -/
theorem cobleHalfMatrix_isSymm : cobleHalfMatrix.IsSymm := by
  decide

/-- The half form is unimodular: its determinant is nonzero. -/
theorem cobleHalfMatrix_det_ne_zero : cobleHalfMatrix.det ≠ 0 := by
  intro h
  have hmul : cobleHalfMatrix.det * cobleHalfMatrixInverse.det = 1 := by
    rw [← Matrix.det_mul, cobleHalfMatrix_mul_inverse, Matrix.det_one]
  rw [h, zero_mul] at hmul
  exact zero_ne_one hmul

/-! ## The Coble lattice -/

/-- The Gram matrix of `T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(2)`: twice the unimodular form above. -/
noncomputable def cobleGramMatrix : Matrix (Fin 13) (Fin 13) ℤ :=
  (2 : ℤ) • cobleHalfMatrix

/-- The Gram matrix of `T_Co` is symmetric. -/
theorem cobleGramMatrix_isSymm : cobleGramMatrix.IsSymm := by
  decide

/-- The Coble lattice `T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(2)` on `Fin 13 → ℤ`. -/
noncomputable def cobleLattice : IntegralLatticeCat ℤ :=
  latticeOfGramMatrix cobleGramMatrix cobleGramMatrix_isSymm

/-- The standard basis has the Coble Gram matrix. -/
theorem coble_gramMatrix :
    gramMatrix cobleLattice (Pi.basisFun ℤ (Fin 13)) = cobleGramMatrix :=
  latticeOfGramMatrix_gramMatrix cobleGramMatrix cobleGramMatrix_isSymm

/-- Pairings of standard basis vectors are the entries of the Gram matrix. -/
theorem coble_pairing_basis (i j : Fin 13) :
    cobleLattice.obj.pairing ((Pi.basisFun ℤ (Fin 13)) i) ((Pi.basisFun ℤ (Fin 13)) j) =
      cobleGramMatrix i j := by
  have h : cobleLattice.obj.pairing ((Pi.basisFun ℤ (Fin 13)) i) ((Pi.basisFun ℤ (Fin 13)) j) =
      Matrix.toBilin' cobleGramMatrix ((Pi.basisFun ℤ (Fin 13)) i)
        ((Pi.basisFun ℤ (Fin 13)) j) := rfl
  rw [h, Pi.basisFun_apply, Pi.basisFun_apply, Matrix.toBilin'_single]

/-- The carrier of `T_Co` is a free `ℤ`-module: instance search does not unfold the packaged
carrier, so the two structural instances are recorded here. -/
instance cobleCarrierFree : Module.Free ℤ ↥cobleLattice.obj.carrier :=
  inferInstanceAs (Module.Free ℤ (Fin 13 → ℤ))

/-- The carrier of `T_Co` is a finite `ℤ`-module. -/
instance cobleCarrierFinite : Module.Finite ℤ ↥cobleLattice.obj.carrier :=
  inferInstanceAs (Module.Finite ℤ (Fin 13 → ℤ))

/-- The carrier of `T_Co` is `ℤ¹³`, hence torsion-free. -/
instance cobleLatticeCarrierTorsionFree :
    NoZeroSMulDivisors ℤ ↥cobleLattice.obj.carrier :=
  inferInstanceAs (NoZeroSMulDivisors ℤ (Fin 13 → ℤ))

/-- `T_Co` is even: its Gram diagonal is the doubled diagonal of the unimodular form. -/
theorem coble_isEven : IsEven cobleLattice := by
  apply latticeOfGramMatrix_isEven cobleGramMatrix cobleGramMatrix_isSymm
  intro i
  rw [Ideal.mem_span_singleton]
  refine ⟨cobleHalfMatrix i i, ?_⟩
  simp only [cobleGramMatrix, Matrix.smul_apply, smul_eq_mul]

/-- `T_Co` is fraction-field perfect: its Gram determinant is `2 ^ 13` times a unit. -/
theorem coble_isFractionFieldPerfect : IsFractionFieldPerfect ℤ cobleLattice := by
  rw [isFractionFieldPerfect_iff_determinant_ne_zero ℤ cobleLattice (Pi.basisFun ℤ (Fin 13))]
  change (gramMatrix cobleLattice (Pi.basisFun ℤ (Fin 13))).det ≠ 0
  rw [coble_gramMatrix, cobleGramMatrix, Matrix.det_smul, Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero 13 (by norm_num)) cobleHalfMatrix_det_ne_zero

/-- The value dual of `T_Co` is a free `ℤ`-module: instance search does not unfold the packaged
duals, so the two structural instances are recorded here. -/
instance cobleValueDualFree : Module.Free ℤ cobleLattice.obj.valueDual := inferInstance

/-- The value dual of `T_Co` is a finite `ℤ`-module. -/
instance cobleValueDualFinite : Module.Finite ℤ cobleLattice.obj.valueDual := inferInstance

/-- The discriminant module of `T_Co` is finite: it is the quotient of the finite free value dual
by the adjoint range, which has full rank. -/
noncomputable instance cobleDefectFinite : Finite cobleLattice.obj.defect := by
  exact Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range cobleLattice.obj.adjoint)
    (adjointRange_finrank_eq_valueDual cobleLattice coble_isFractionFieldPerfect)

/-! ## The quadratic discriminant form and `ρ` -/

/-- The quadratic discriminant form `q = q_{T_Co}` of the even lattice `T_Co`. -/
noncomputable abbrev cobleQuadraticDiscriminant :=
  evenDiscriminantQuadraticObject cobleLattice coble_isFractionFieldPerfect coble_isEven

/-- The discriminant carrier is finite. -/
instance cobleQuadraticCarrierFinite : Finite cobleQuadraticDiscriminant.carrier :=
  cobleDefectFinite

/-- `O(q_{T_Co})` is finite: it is a group of permutations of a finite carrier. -/
instance cobleOrthogonalGroupFinite :
    Finite (QuadModuleCat.OrthogonalGroup cobleQuadraticDiscriminant) := by
  let f : QuadModuleCat.OrthogonalGroup cobleQuadraticDiscriminant →
      (cobleQuadraticDiscriminant.carrier → cobleQuadraticDiscriminant.carrier) :=
    fun g => fun x => g.1 x
  exact Finite.of_injective f
    (fun a b h => Subtype.ext (LinearEquiv.ext fun x => congrFun h x))

/-- The representation `ρ : O(T_Co) →* O(q_{T_Co})` on the quadratic discriminant form. -/
noncomputable abbrev cobleRho : OrthogonalGroup cobleLattice →*
    QuadModuleCat.OrthogonalGroup cobleQuadraticDiscriminant :=
  OrthogonalGroup.evenDiscriminantRepresentation coble_isFractionFieldPerfect coble_isEven

/-- `ker ρ`: the isometries of `T_Co` acting trivially on the discriminant form. -/
noncomputable def cobleKernel : Subgroup (OrthogonalGroup cobleLattice) :=
  MonoidHom.ker cobleRho

/-- `ker ρ` has finite index, because `O(q)` is finite. -/
theorem cobleKernel_finiteIndex : cobleKernel.FiniteIndex where
  index_ne_zero := by
    rw [cobleKernel, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

/-! ## The orientation subgroup `O⁺` and `Γ_Co` -/

/-- The determinant character of `O(T_Co)`, with values in the units of `ℤ`. -/
noncomputable def orthogonalDeterminant (L : IntegralLatticeCat ℤ) :
    OrthogonalGroup L →* ℤˣ :=
  (LinearEquiv.det (R := ℤ) (M := L.obj.carrier)).comp (Subgroup.subtype (OrthogonalGroup L))

/-- `O⁺(T_Co)`, the orientation subgroup, formalized as the kernel of the determinant. The
positive-cone characterization of the cusp literature is not part of this development; what the
cusp statements consume is that it is a subgroup of index at most two. -/
noncomputable def cobleOrientationSubgroup : Subgroup (OrthogonalGroup cobleLattice) :=
  MonoidHom.ker (orthogonalDeterminant cobleLattice)

/-- The orientation subgroup has index at most two: `O(T_Co) ⧸ O⁺` injects into `ℤˣ`. -/
theorem cobleOrientationSubgroup_index_le_two : cobleOrientationSubgroup.index ≤ 2 := by
  rw [cobleOrientationSubgroup, Subgroup.index_ker]
  calc Nat.card ↥(MonoidHom.range (orthogonalDeterminant cobleLattice))
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- The orientation subgroup has finite index. -/
theorem cobleOrientationSubgroup_finiteIndex : cobleOrientationSubgroup.FiniteIndex where
  index_ne_zero := by
    rw [cobleOrientationSubgroup, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr
      ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

/-- `Γ_Co = O⁺(T_Co) ∩ ker ρ`. -/
noncomputable def cobleGammaCo : Subgroup (OrthogonalGroup cobleLattice) :=
  cobleOrientationSubgroup ⊓ cobleKernel

/-- `Γ_Co` has finite index: it is the intersection of two finite-index subgroups. -/
theorem cobleGammaCo_finiteIndex : cobleGammaCo.FiniteIndex := by
  refine ⟨?_⟩
  rw [cobleGammaCo]
  exact Subgroup.index_inf_ne_zero cobleOrientationSubgroup_finiteIndex.index_ne_zero
    cobleKernel_finiteIndex.index_ne_zero

/-- `ker ρ` as a finite-index subgroup of `O(T_Co)`. -/
noncomputable def cobleKernelSubgroup : FiniteIndexSubgroup cobleLattice :=
  ⟨cobleKernel, cobleKernel_finiteIndex⟩

/-- `Γ_Co` as a finite-index subgroup of `O(T_Co)`. -/
noncomputable def cobleGammaCoSubgroup : FiniteIndexSubgroup cobleLattice :=
  ⟨cobleGammaCo, cobleGammaCo_finiteIndex⟩

/-! ## The cusp objects and their orbit sets -/

/-- The cusp object `(T_Co, ker ρ)` of the cusp category. -/
noncomputable def cobleCuspKernel : CuspObject (R := ℤ) :=
  ⟨cobleLattice, cobleKernelSubgroup⟩

/-- The cusp object `(T_Co, Γ_Co)` of the cusp category. -/
noncomputable def cobleCuspGamma : CuspObject (R := ℤ) :=
  ⟨cobleLattice, cobleGammaCoSubgroup⟩

/-- The `ker ρ`-orbits of primitive isotropic lines: the 0-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsKernelOne : Type :=
  CuspOrbits cobleLattice cobleKernelSubgroup 1

/-- The `ker ρ`-orbits of primitive isotropic planes: the 1-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsKernelTwo : Type :=
  CuspOrbits cobleLattice cobleKernelSubgroup 2

/-- The `Γ_Co`-orbits of primitive isotropic lines: the 0-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaOne : Type :=
  CuspOrbits cobleLattice cobleGammaCoSubgroup 1

/-- The `Γ_Co`-orbits of primitive isotropic planes: the 1-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaTwo : Type :=
  CuspOrbits cobleLattice cobleGammaCoSubgroup 2

end LeanCategories.Lattices.Valued
