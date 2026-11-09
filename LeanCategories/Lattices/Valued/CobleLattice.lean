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

`T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(−2) = ⟨2⟩ ⊕ E₁₀(2)`, of rank 11 and signature `(2, 9)`, is presented here
on `Fin 11 → ℤ` as twice the odd unimodular lattice `B = ⟨1⟩ ⊕ E₁₀ = ⟨1⟩ ⊕ U ⊕ E₈(−1)`. Since
`T_Co = B(2)`, `O(T_Co) = O(B)`; the form of `T_Co` is `2 • B`, whose Gram diagonal is even, and
whose determinant is `2 ^ 11 · det B = -2 ^ 11`, so `T_Co` is even and fraction-field perfect.

The file records, in order:

* the lattice `cobleLattice`, its evenness and fraction-field perfection;
* the quadratic discriminant form `cobleQuadraticDiscriminant` and the representation
  `cobleRho : O(T_Co) →* O(q)`, with the finiteness of `O(q)`;
* the kernel of `det` (`cobleSpecialOrthogonal`) and, separately, the orientation subgroup
  `cobleOPlus = O⁺(T_Co)` and `cobleGammaCo = O⁺(T_Co) ∩ ker ρ`, both of index at most two;
* the cusp objects `(T_Co, ker ρ)` and `(T_Co, Γ_Co)` with their rank-1 and rank-2 orbit sets.

## `O⁺(T_Co)`

`O⁺(T_Co)` is the subgroup of `O(T_Co)` preserving the orientation of the positive definite
2-planes of `T_Co ⊗ ℝ`, equivalently the kernel of the real spinor norm. It is **not** the kernel
of `det`: `SO(T_Co)` (`cobleSpecialOrthogonal`) does not see the orientation of the positive
definite 2-planes.

The construction is concrete. With `P = ⟨p₁, p₂⟩` the plane of `p₁ = e₀` (of norm `2`) and
`p₂ = e₁ + e₂` (of norm `4`), and `M(g) = (⟨g pᵢ, pⱼ⟩)ᵢⱼ` as in the issue, `O⁺(T_Co)` is the
kernel of `cobleOPlusSign : O(T_Co) →* ℤˣ`, the sign of `det A(g)` where `A(g)` is the matrix of
the `P`-component of `g` (`coblePlaneA`). Since `det M(g) = 8 · det A(g)` (`coblePlaneGram_det`),
`O⁺(T_Co) = {g | 0 < det M(g)}` (`cobleOPlus_mem_iff`): the character is the one displayed in the
issue.

Two facts carry the construction, neither of them a computation on the finite group:

* the complement `P^⊥ = {x₀ = 0, x₂ = −x₁}` is negative definite, with Gram matrix
  `diag(−4, E₈(−2))`; its negation `coblePosMatrixZ = diag(4, 2E₈)` is certified positive definite
  by the explicit integer `LDLᵀ` factorization `coblePosL * coblePosD * coblePosLᵀ = 108000 •
  coblePosMatrixZ` with `coblePosD` diagonal and positive, checked by `decide`, and the left
  inverse `coblePosL * coblePosLinv = 3600 • 1` makes `coblePosL` invertible. The sum of squares
  `u ⬝ᵥ (D *ᵥ u) = ∑ dᵢ uᵢ²` then gives positive definiteness in `coblePosMatrix_quadratic_pos`;
* the sign of `det A` is multiplicative. Along the straight line
  `A(g)A(h) + t·(B(g)C(h))` from `A(g)A(h)` to `A(gh)`, no point is singular
  (`coblePlaneInterp_ker`): for a vector `y` of the plane, `x = A(h)y`, `u = C(h)y`, the vector
  `x + t·u` has square `(1 − t²)|x|² + t²|y|² > 0` because `|u|² = |y|² − |x|²` and `u` is
  negative semidefinite, while if the path were singular at `y` the image `g(x + t·u)` would lie
  in `P^⊥` and have negative square. The determinant of the path is a polynomial in `t` with no
  zeros on `[0, 1]`, so by the intermediate value theorem `det A(g) · det A(h) · det A(gh) > 0`
  (`coblePlaneA_det_triple_pos`), which is multiplicativity of the sign.

`O⁺(T_Co)` is the kernel of that character, so it has index at most two
(`cobleOPlus_index_le_two`). `Γ_Co = O⁺(T_Co) ∩ ker ρ` is `cobleGammaCo`, a definition and not a
parameter.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

-- Pin the quotient module instance of the discriminant carrier, so that the quadratic
-- discriminant object and its orthogonal group see the same `ℤ`-module structure.
attribute [local instance 10000] Submodule.Quotient.module

/-! ## The odd unimodular half `B = ⟨1⟩ ⊕ U ⊕ E₈(−1)` -/

/-- The Gram matrix of `B = ⟨1⟩ ⊕ U ⊕ E₈(−1)`: blocks of sizes `1`, `2`, `8`. -/
noncomputable def cobleHalfMatrix : Matrix (Fin 11) (Fin 11) ℤ :=
  ![
    ![   1,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    0,    1,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    1,    0,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    0,    0,   -2,    0,    1,    0,    0,    0,    0,    0],
    ![   0,    0,    0,    0,   -2,    0,    1,    0,    0,    0,    0],
    ![   0,    0,    0,    1,    0,   -2,    1,    0,    0,    0,    0],
    ![   0,    0,    0,    0,    1,    1,   -2,    1,    0,    0,    0],
    ![   0,    0,    0,    0,    0,    0,    1,   -2,    1,    0,    0],
    ![   0,    0,    0,    0,    0,    0,    0,    1,   -2,    1,    0],
    ![   0,    0,    0,    0,    0,    0,    0,    0,    1,   -2,    1],
    ![   0,    0,    0,    0,    0,    0,    0,    0,    0,    1,   -2]]

/-- The integral inverse of `cobleHalfMatrix`: `B` is odd unimodular. -/
noncomputable def cobleHalfMatrixInverse : Matrix (Fin 11) (Fin 11) ℤ :=
  ![
    ![   1,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    0,    1,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    1,    0,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    0,    0,   -4,   -5,   -7,  -10,   -8,   -6,   -4,   -2],
    ![   0,    0,    0,   -5,   -8,  -10,  -15,  -12,   -9,   -6,   -3],
    ![   0,    0,    0,   -7,  -10,  -14,  -20,  -16,  -12,   -8,   -4],
    ![   0,    0,    0,  -10,  -15,  -20,  -30,  -24,  -18,  -12,   -6],
    ![   0,    0,    0,   -8,  -12,  -16,  -24,  -20,  -15,  -10,   -5],
    ![   0,    0,    0,   -6,   -9,  -12,  -18,  -15,  -12,   -8,   -4],
    ![   0,    0,    0,   -4,   -6,   -8,  -12,  -10,   -8,   -6,   -3],
    ![   0,    0,    0,   -2,   -3,   -4,   -6,   -5,   -4,   -3,   -2]]

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

/-! ## The Coble lattice `T_Co = B(2)` -/

/-- The Gram matrix of `T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(−2)`, as an explicit integer matrix so that its
entries reduce: diagonal `(2, 0, 0, -4, …, -4)`, and the `U(2)` and `E₈(−2)` blocks. -/
noncomputable def cobleGramMatrix : Matrix (Fin 11) (Fin 11) ℤ :=
  ![
    ![   2,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    0,    2,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    2,    0,    0,    0,    0,    0,    0,    0,    0,    0],
    ![   0,    0,    0,   -4,    0,    2,    0,    0,    0,    0,    0],
    ![   0,    0,    0,    0,   -4,    0,    2,    0,    0,    0,    0],
    ![   0,    0,    0,    2,    0,   -4,    2,    0,    0,    0,    0],
    ![   0,    0,    0,    0,    2,    2,   -4,    2,    0,    0,    0],
    ![   0,    0,    0,    0,    0,    0,    2,   -4,    2,    0,    0],
    ![   0,    0,    0,    0,    0,    0,    0,    2,   -4,    2,    0],
    ![   0,    0,    0,    0,    0,    0,    0,    0,    2,   -4,    2],
    ![   0,    0,    0,    0,    0,    0,    0,    0,    0,    2,   -4]]

/-- The Gram matrix of `T_Co` is twice the odd unimodular form. -/
theorem cobleGramMatrix_eq : cobleGramMatrix = (2 : ℤ) • cobleHalfMatrix := by
  decide

/-- The Gram matrix of `T_Co` is symmetric. -/
theorem cobleGramMatrix_isSymm : cobleGramMatrix.IsSymm := by
  decide

/-- The Coble lattice `T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(−2)`, of rank 11 and signature `(2, 9)`. -/
noncomputable def cobleLattice : IntegralLatticeCat ℤ :=
  latticeOfGramMatrix cobleGramMatrix cobleGramMatrix_isSymm

/-- The standard basis has the Coble Gram matrix. -/
theorem coble_gramMatrix :
    gramMatrix cobleLattice (Pi.basisFun ℤ (Fin 11)) = cobleGramMatrix :=
  latticeOfGramMatrix_gramMatrix cobleGramMatrix cobleGramMatrix_isSymm

/-- Pairings of standard basis vectors are the entries of the Gram matrix. -/
theorem coble_pairing_basis (i j : Fin 11) :
    cobleLattice.obj.pairing ((Pi.basisFun ℤ (Fin 11)) i) ((Pi.basisFun ℤ (Fin 11)) j) =
      cobleGramMatrix i j := by
  have h : cobleLattice.obj.pairing ((Pi.basisFun ℤ (Fin 11)) i) ((Pi.basisFun ℤ (Fin 11)) j) =
      Matrix.toBilin' cobleGramMatrix ((Pi.basisFun ℤ (Fin 11)) i)
        ((Pi.basisFun ℤ (Fin 11)) j) := rfl
  rw [h, Pi.basisFun_apply, Pi.basisFun_apply, Matrix.toBilin'_single]

/-- The carrier of `T_Co` is a free `ℤ`-module: instance search does not unfold the packaged
carrier, so the structural instances are recorded here. -/
instance cobleCarrierFree : Module.Free ℤ ↥cobleLattice.obj.carrier :=
  inferInstanceAs (Module.Free ℤ (Fin 11 → ℤ))

/-- The carrier of `T_Co` is a finite `ℤ`-module. -/
instance cobleCarrierFinite : Module.Finite ℤ ↥cobleLattice.obj.carrier :=
  inferInstanceAs (Module.Finite ℤ (Fin 11 → ℤ))

/-- The carrier of `T_Co` is `ℤ¹¹`, hence torsion-free. -/
instance cobleLatticeCarrierTorsionFree :
    NoZeroSMulDivisors ℤ ↥cobleLattice.obj.carrier :=
  inferInstanceAs (NoZeroSMulDivisors ℤ (Fin 11 → ℤ))

/-- Coordinates of a vector of `T_Co`: the standard basis identifies the carrier with `ℤ¹¹`. -/
noncomputable def cobleCoordEquiv : ↥cobleLattice.obj.carrier ≃ₗ[ℤ] (Fin 11 → ℤ) :=
  (Pi.basisFun ℤ (Fin 11)).equivFun

/-- `T_Co` is even: its Gram diagonal is the doubled diagonal of the odd unimodular form. -/
theorem coble_isEven : IsEven cobleLattice := by
  apply latticeOfGramMatrix_isEven cobleGramMatrix cobleGramMatrix_isSymm
  intro i
  rw [Ideal.mem_span_singleton]
  refine ⟨cobleHalfMatrix i i, ?_⟩
  rw [cobleGramMatrix_eq]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- `T_Co` is fraction-field perfect: its Gram determinant is `2 ^ 11` times a unit. -/
theorem coble_isFractionFieldPerfect : IsFractionFieldPerfect ℤ cobleLattice := by
  rw [isFractionFieldPerfect_iff_determinant_ne_zero ℤ cobleLattice (Pi.basisFun ℤ (Fin 11))]
  change (gramMatrix cobleLattice (Pi.basisFun ℤ (Fin 11))).det ≠ 0
  rw [coble_gramMatrix, cobleGramMatrix_eq, Matrix.det_smul, Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero 11 (by norm_num)) cobleHalfMatrix_det_ne_zero

/-- The value dual of `T_Co` is a free `ℤ`-module. -/
instance cobleValueDualFree : Module.Free ℤ cobleLattice.obj.valueDual := inferInstance

/-- The value dual of `T_Co` is a finite `ℤ`-module. -/
instance cobleValueDualFinite : Module.Finite ℤ cobleLattice.obj.valueDual := inferInstance

/-- The discriminant module of `T_Co` is finite: it is the quotient of the finite free value dual
by the adjoint range, which has full rank. -/
noncomputable instance cobleDefectFinite : Finite cobleLattice.obj.defect :=
  Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range cobleLattice.obj.adjoint)
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

/-- `ker ρ` as a finite-index subgroup of `O(T_Co)`. -/
noncomputable def cobleKernelSubgroup : FiniteIndexSubgroup cobleLattice :=
  ⟨cobleKernel, cobleKernel_finiteIndex⟩

/-! ## The kernel of `det`, and the data of `O⁺` -/

/-- The determinant character of `O(T_Co)`, with values in the units of `ℤ`. -/
noncomputable def orthogonalDeterminant (L : IntegralLatticeCat ℤ) :
    OrthogonalGroup L →* ℤˣ :=
  (LinearEquiv.det (R := ℤ) (M := L.obj.carrier)).comp (Subgroup.subtype (OrthogonalGroup L))

/-- `SO(T_Co)`, the kernel of `det`. It has index at most two but it is **not** `O⁺(T_Co)`: for a
lattice of signature `(2, 9)` the determinant does not see the orientation of the positive-definite
2-planes. -/
noncomputable def cobleSpecialOrthogonal : Subgroup (OrthogonalGroup cobleLattice) :=
  MonoidHom.ker (orthogonalDeterminant cobleLattice)

/-- `SO(T_Co)` has index at most two: `O(T_Co) ⧸ SO(T_Co)` injects into `ℤˣ`. -/
theorem cobleSpecialOrthogonal_index_le_two : cobleSpecialOrthogonal.index ≤ 2 := by
  rw [cobleSpecialOrthogonal, Subgroup.index_ker]
  calc Nat.card ↥(MonoidHom.range (orthogonalDeterminant cobleLattice))
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- `SO(T_Co)` has finite index. -/
theorem cobleSpecialOrthogonal_finiteIndex : cobleSpecialOrthogonal.FiniteIndex where
  index_ne_zero := by
    rw [cobleSpecialOrthogonal, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

/-- The two discriminant representations carry the same linear equivalence: the underlying action
on `A_L` is `actOnDefect`, and only the form attached to the module differs. -/
theorem discriminantRepresentation_apply_eq_even {R : Type} [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (g : OrthogonalGroup L) :
    (Subtype.val ((OrthogonalGroup.discriminantRepresentation hL) g) :
        L.obj.defect ≃ₗ[R] L.obj.defect) =
      (Subtype.val ((OrthogonalGroup.evenDiscriminantRepresentation hL hEven) g) :
        L.obj.defect ≃ₗ[R] L.obj.defect) :=
  rfl

/-- The stable orthogonal group and the kernel of the quadratic discriminant representation are the
same subgroup. Both are the isometries acting trivially on `A_L`: the bilinear and the quadratic
discriminant forms are attached to the same module, so an isometry acts trivially on it or it does
not, whatever form is attached. -/
theorem stableOrthogonalGroup_eq_stableEven {R : Type} [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R}
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :
    OrthogonalGroup.stableOrthogonalGroup hL =
      OrthogonalGroup.stableEvenOrthogonalGroup hL hEven := by
  ext g
  constructor
  · intro hg
    rw [OrthogonalGroup.stableEvenOrthogonalGroup, MonoidHom.mem_ker]
    rw [OrthogonalGroup.stableOrthogonalGroup, MonoidHom.mem_ker] at hg
    apply Subtype.ext
    rw [← discriminantRepresentation_apply_eq_even hL hEven g]
    exact congrArg Subtype.val hg
  · intro hg
    rw [OrthogonalGroup.stableOrthogonalGroup, MonoidHom.mem_ker]
    rw [OrthogonalGroup.stableEvenOrthogonalGroup, MonoidHom.mem_ker] at hg
    apply Subtype.ext
    rw [discriminantRepresentation_apply_eq_even hL hEven g]
    exact congrArg Subtype.val hg

/-- The stable orthogonal group is contained in `ker ρ`: at `T_Co`, `ker ρ` is the subgroup of
isometries acting trivially on `A_{T_Co}`, and so is the stable group. -/
theorem stableOrthogonalGroup_le_cobleKernel :
    OrthogonalGroup.stableOrthogonalGroup coble_isFractionFieldPerfect ≤ cobleKernel := by
  rw [stableOrthogonalGroup_eq_stableEven coble_isFractionFieldPerfect coble_isEven]
  exact le_rfl


/-! ## The real form of `T_Co` -/

/-- The real Gram matrix of `T_Co ⊗ ℝ`. -/
noncomputable def cobleGramReal : Matrix (Fin 11) (Fin 11) ℝ :=
  cobleGramMatrix.map (Int.castRingHom ℝ)

theorem cobleGramReal_apply (i j : Fin 11) : cobleGramReal i j = (cobleGramMatrix i j : ℝ) :=
  rfl

/-- The real form of `T_Co` is symmetric. -/
theorem cobleGramReal_isSymm : cobleGramReal.IsSymm := by
  have h := congrArg (fun M : Matrix (Fin 11) (Fin 11) ℤ => M.map (Int.castRingHom ℝ))
    cobleGramMatrix_isSymm
  rwa [Matrix.transpose_map] at h

/-- The real bilinear form of `T_Co ⊗ ℝ`. -/
noncomputable abbrev cobleRealForm : LinearMap.BilinForm ℝ (Fin 11 → ℝ) :=
  Matrix.toBilin' cobleGramReal

/-- The real form is symmetric. -/
theorem cobleRealForm_symm (x y : Fin 11 → ℝ) : cobleRealForm x y = cobleRealForm y x :=
  (Matrix.isSymm_toBilin'_iff_isSymm.mpr cobleGramReal_isSymm).eq x y

/-- The real form in coordinates: the Gram matrix of `T_Co`. -/
theorem cobleRealForm_coord (x y : Fin 11 → ℝ) :
    cobleRealForm x y = ∑ i, ∑ j, x i * (cobleGramMatrix i j : ℝ) * y j := by
  rw [cobleRealForm, Matrix.toBilin'_apply]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [cobleGramReal_apply]

/-- The real form as a dot product. -/
theorem cobleRealForm_dot (x y : Fin 11 → ℝ) :
    cobleRealForm x y = x ⬝ᵥ (cobleGramReal *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

/-- Cast an integer coordinate vector of `T_Co` to a real one. -/
noncomputable def cobleVecCast (v : Fin 11 → ℤ) : Fin 11 → ℝ := fun i => (v i : ℝ)

theorem cobleVecCast_add (v w : Fin 11 → ℤ) :
    cobleVecCast (v + w) = cobleVecCast v + cobleVecCast w := by
  ext i; simp [cobleVecCast]

theorem cobleVecCast_smul (a : ℤ) (v : Fin 11 → ℤ) :
    cobleVecCast (a • v) = (a : ℝ) • cobleVecCast v := by
  ext i; simp [cobleVecCast]

theorem cobleVecCast_single (i : Fin 11) (a : ℤ) :
    cobleVecCast (Pi.single i a) = Pi.single i (a : ℝ) := by
  ext j; simp [cobleVecCast, Pi.single_apply]

/-- The real form of a pair of integral vectors is the cast of their integral pairing. -/
theorem cobleRealForm_cast (x y : Fin 11 → ℤ) :
    cobleRealForm (cobleVecCast x) (cobleVecCast y)
      = ((∑ i, ∑ j, x i * cobleGramMatrix i j * y j : ℤ) : ℝ) := by
  rw [cobleRealForm_coord]
  push_cast
  rfl

/-- An integral value of the real form, from an integral coordinate computation. -/
theorem cobleRealForm_cast_of (x y : Fin 11 → ℤ) (m : ℤ)
    (h : ∑ i, ∑ j, x i * cobleGramMatrix i j * y j = m) :
    cobleRealForm (cobleVecCast x) (cobleVecCast y) = (m : ℝ) := by
  rw [cobleRealForm_cast, h]

/-- Casting commutes with the matrix-vector product. -/
theorem cobleVecCast_mulVec (M : Matrix (Fin 11) (Fin 11) ℤ) (v : Fin 11 → ℤ) :
    cobleVecCast (M *ᵥ v) = M.map (Int.castRingHom ℝ) *ᵥ cobleVecCast v := by
  ext i
  simp only [cobleVecCast, Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl fun x _ => rfl

/-! ## The positive definite plane `P = span(e₀, e₁ + e₂)` -/

/-- `p₁ = e₀`, of norm `2`. -/
noncomputable def cobleP1Z : Fin 11 → ℤ := Pi.single (0 : Fin 11) 1

/-- `p₂ = e₁ + e₂`, of norm `4`. -/
noncomputable def cobleP2Z : Fin 11 → ℤ := Pi.single (1 : Fin 11) 1 + Pi.single (2 : Fin 11) 1

/-- The first vector of the positive definite plane, in real coordinates. -/
noncomputable def cobleP1 : Fin 11 → ℝ := cobleVecCast cobleP1Z

/-- The second vector of the positive definite plane, in real coordinates. -/
noncomputable def cobleP2 : Fin 11 → ℝ := cobleVecCast cobleP2Z

theorem cobleRealForm_p1_p1 : cobleRealForm cobleP1 cobleP1 = 2 := by
  have h := cobleRealForm_cast_of cobleP1Z cobleP1Z 2 (by decide)
  have h' : cobleRealForm cobleP1 cobleP1 = ((2 : ℤ) : ℝ) := h
  norm_num at h'
  exact h'

theorem cobleRealForm_p2_p2 : cobleRealForm cobleP2 cobleP2 = 4 := by
  have h := cobleRealForm_cast_of cobleP2Z cobleP2Z 4 (by decide)
  have h' : cobleRealForm cobleP2 cobleP2 = ((4 : ℤ) : ℝ) := h
  norm_num at h'
  exact h'

theorem cobleRealForm_p1_p2 : cobleRealForm cobleP1 cobleP2 = 0 := by
  have h := cobleRealForm_cast_of cobleP1Z cobleP2Z 0 (by decide)
  have h' : cobleRealForm cobleP1 cobleP2 = ((0 : ℤ) : ℝ) := h
  norm_num at h'
  exact h'

/-- The Gram matrix sends `p₁` to twice `p₁`. -/
theorem cobleGramMatrix_mulVec_p1 : cobleGramMatrix *ᵥ cobleP1Z = (2 : ℤ) • cobleP1Z := by
  unfold cobleP1Z
  decide

/-- The Gram matrix sends `p₂ = e₁ + e₂` to twice `p₂`. -/
theorem cobleGramMatrix_mulVec_p2 : cobleGramMatrix *ᵥ cobleP2Z = (2 : ℤ) • cobleP2Z := by
  unfold cobleP2Z
  decide

theorem cobleGramReal_mulVec_p1 : cobleGramReal *ᵥ cobleP1 = 2 • cobleP1 := by
  have h := cobleVecCast_mulVec cobleGramMatrix cobleP1Z
  rw [cobleGramMatrix_mulVec_p1, cobleVecCast_smul] at h
  unfold cobleGramReal cobleP1
  rw [← h]
  ext i
  simp

theorem cobleGramReal_mulVec_p2 : cobleGramReal *ᵥ cobleP2 = 2 • cobleP2 := by
  have h := cobleVecCast_mulVec cobleGramMatrix cobleP2Z
  rw [cobleGramMatrix_mulVec_p2, cobleVecCast_smul] at h
  unfold cobleGramReal cobleP2
  rw [← h]
  ext i
  simp

theorem cobleP1_dot (x : Fin 11 → ℝ) : x ⬝ᵥ cobleP1 = x 0 := by
  rw [cobleP1, cobleP1Z, cobleVecCast_single, dotProduct_single]
  simp

theorem cobleP2_dot (x : Fin 11 → ℝ) : x ⬝ᵥ cobleP2 = x 1 + x 2 := by
  rw [cobleP2, cobleP2Z, cobleVecCast_add, cobleVecCast_single, cobleVecCast_single,
    dotProduct_add, dotProduct_single, dotProduct_single]
  ring

/-- The form pairs `p₁` against `x` by twice the `0`-th coordinate. -/
theorem cobleRealForm_p1_left (x : Fin 11 → ℝ) : cobleRealForm cobleP1 x = 2 * x 0 := by
  rw [cobleRealForm_symm, cobleRealForm_dot, cobleGramReal_mulVec_p1, dotProduct_smul,
    cobleP1_dot]
  ring

/-- The form pairs `p₂` against `x` by twice the sum of the `1`-st and `2`-nd coordinates. -/
theorem cobleRealForm_p2_left (x : Fin 11 → ℝ) :
    cobleRealForm cobleP2 x = 2 * (x 1 + x 2) := by
  rw [cobleRealForm_symm, cobleRealForm_dot, cobleGramReal_mulVec_p2, dotProduct_smul,
    cobleP2_dot]
  ring



/-! ## The negative definite complement `P^⊥ = {x₀ = 0, x₂ = −x₁}` -/

/-- The integer coordinates of the `j`-th basis vector `e₁ − e₂, e₃, …, e₁₀` of the complement. -/
noncomputable def cobleWBasisZ (j : Fin 9) : Fin 11 → ℤ := fun i =>
  if i.val = 0 then 0
  else if i.val = 1 then (if (0 : Fin 9) = j then 1 else 0)
  else if i.val = 2 then -(if (0 : Fin 9) = j then 1 else 0)
  else if (⟨i.val - 2, by omega⟩ : Fin 9) = j then 1 else 0

/-- The complement `P^⊥ = {x₀ = 0, x₂ = −x₁}` of the positive plane, in coordinates. -/
noncomputable def cobleWIncl : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 11 → ℝ) :=
  LinearMap.pi fun i : Fin 11 =>
    if i.val = 0 then 0
    else if i.val = 1 then LinearMap.proj (0 : Fin 9)
    else if i.val = 2 then -(LinearMap.proj (0 : Fin 9))
    else LinearMap.proj ⟨i.val - 2, by omega⟩

theorem cobleWIncl_apply (v : Fin 9 → ℝ) (i : Fin 11) :
    cobleWIncl v i =
      (if i.val = 0 then 0
      else if i.val = 1 then v 0
      else if i.val = 2 then -v 0
      else v ⟨i.val - 2, by omega⟩) := by
  rw [cobleWIncl, LinearMap.pi_apply]
  split_ifs <;> simp

/-- The image of a basis vector is the corresponding integral vector of the complement. -/
theorem cobleWIncl_single (j : Fin 9) :
    cobleWIncl (Pi.single j 1) = cobleVecCast (cobleWBasisZ j) := by
  ext i
  rw [cobleWIncl_apply]
  by_cases h0 : i.val = 0
  · simp [h0, cobleWBasisZ, cobleVecCast]
  by_cases h1 : i.val = 1
  · simp [h1, cobleWBasisZ, cobleVecCast, Pi.single_apply]
  by_cases h2 : i.val = 2
  · simp [h2, cobleWBasisZ, cobleVecCast, Pi.single_apply]
  · simp [h0, h1, h2, cobleWBasisZ, cobleVecCast, Pi.single_apply]



/-! ### The Gram matrix of the complement basis -/

/-- The Gram matrix of the integral basis `e₁ − e₂, e₃, …, e₁₀` of `P^⊥`. -/
noncomputable def cobleWBasisGramZ : Matrix (Fin 9) (Fin 9) ℤ :=
  fun i j => ∑ k, ∑ l, cobleWBasisZ i k * cobleGramMatrix k l * cobleWBasisZ j l

/-- The complement carries `diag(−4, E₈(−2))`: the plane `{x₀ = 0, x₂ = −x₁}` is negative
definite of rank nine. -/
theorem cobleWBasisGramZ_eq : cobleWBasisGramZ =
    ![
      ![ -4,  0,  0,  0,  0,  0,  0,  0,  0],
      ![  0, -4,  0,  2,  0,  0,  0,  0,  0],
      ![  0,  0, -4,  0,  2,  0,  0,  0,  0],
      ![  0,  2,  0, -4,  2,  0,  0,  0,  0],
      ![  0,  0,  2,  2, -4,  2,  0,  0,  0],
      ![  0,  0,  0,  0,  2, -4,  2,  0,  0],
      ![  0,  0,  0,  0,  0,  2, -4,  2,  0],
      ![  0,  0,  0,  0,  0,  0,  2, -4,  2],
      ![  0,  0,  0,  0,  0,  0,  0,  2, -4]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The complement form is the restriction of the real form of `T_Co` along the inclusion. -/
theorem cobleRealForm_comp_WIncl :
    cobleRealForm.comp cobleWIncl cobleWIncl =
      Matrix.toBilin' (cobleWBasisGramZ.map (Int.castRingHom ℝ)) := by
  have hmat : LinearMap.BilinForm.toMatrix' (cobleRealForm.comp cobleWIncl cobleWIncl) =
      cobleWBasisGramZ.map (Int.castRingHom ℝ) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix'_apply, LinearMap.BilinForm.comp_apply,
      cobleWIncl_single, cobleWIncl_single, cobleRealForm_cast]
    rfl
  rw [← hmat, Matrix.toBilin'_toMatrix']

/-- The quadratic form of the complement in coordinates. -/
theorem cobleRealForm_wIncl (v : Fin 9 → ℝ) :
    cobleRealForm (cobleWIncl v) (cobleWIncl v)
      = v ⬝ᵥ (cobleWBasisGramZ.map (Int.castRingHom ℝ) *ᵥ v) := by
  rw [← LinearMap.BilinForm.comp_apply, cobleRealForm_comp_WIncl, Matrix.toBilin'_apply']



/-! ### An `LDLᵀ` certificate for the positive definite matrix `− Gram(P^⊥)` -/

/-- The negation of the Gram matrix of the complement basis, `diag(4, 2E₈)`, which is positive
definite. -/
noncomputable def coblePosMatrixZ : Matrix (Fin 9) (Fin 9) ℤ :=
  ![
    ![  4,  0,  0,  0,  0,  0,  0,  0,  0],
    ![  0,  4,  0, -2,  0,  0,  0,  0,  0],
    ![  0,  0,  4,  0, -2,  0,  0,  0,  0],
    ![  0, -2,  0,  4, -2,  0,  0,  0,  0],
    ![  0,  0, -2, -2,  4, -2,  0,  0,  0],
    ![  0,  0,  0,  0, -2,  4, -2,  0,  0],
    ![  0,  0,  0,  0,  0, -2,  4, -2,  0],
    ![  0,  0,  0,  0,  0,  0, -2,  4, -2],
    ![  0,  0,  0,  0,  0,  0,  0, -2,  4]]

theorem coblePosMatrixZ_eq : coblePosMatrixZ = -cobleWBasisGramZ := by
  rw [cobleWBasisGramZ_eq]
  decide

/-- The unit lower triangular factor `L` of the `LDLᵀ` certificate for `coblePosMatrixZ`. -/
noncomputable def coblePosL : Matrix (Fin 9) (Fin 9) ℤ :=
  ![
    ![ 60,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,  60,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,  60,   0,   0,   0,   0,   0,   0],
    ![  0, -30,   0,  60,   0,   0,   0,   0,   0],
    ![  0,   0, -30, -40,  60,   0,   0,   0,   0],
    ![  0,   0,   0,   0, -72,  60,   0,   0,   0],
    ![  0,   0,   0,   0,   0, -75,  60,   0,   0],
    ![  0,   0,   0,   0,   0,   0, -80,  60,   0],
    ![  0,   0,   0,   0,   0,   0,   0, -90,  60]]

/-- The positive diagonal of the `LDLᵀ` certificate. -/
noncomputable def coblePosDiag : Fin 9 → ℤ := ![120, 120, 120, 90, 50, 48, 45, 40, 30]

/-- The diagonal factor `D` of the `LDLᵀ` certificate. -/
noncomputable def coblePosD : Matrix (Fin 9) (Fin 9) ℤ := Matrix.diagonal coblePosDiag

/-- An integral left inverse of `coblePosL`, up to the scalar `3600`. -/
noncomputable def coblePosLinv : Matrix (Fin 9) (Fin 9) ℤ :=
  ![
    ![ 60,   0,   0,   0,   0,   0,   0,   0,   0],
    ![  0,  60,   0,   0,   0,   0,   0,   0,   0],
    ![  0,   0,  60,   0,   0,   0,   0,   0,   0],
    ![  0,  30,   0,  60,   0,   0,   0,   0,   0],
    ![  0,  20,  30,  40,  60,   0,   0,   0,   0],
    ![  0,  24,  36,  48,  72,  60,   0,   0,   0],
    ![  0,  30,  45,  60,  90,  75,  60,   0,   0],
    ![  0,  40,  60,  80, 120, 100,  80,  60,   0],
    ![  0,  60,  90, 120, 180, 150, 120,  90,  60]]

/-- The certificate: `L · D · Lᵀ = 108000 · (− Gram(P^⊥))`, with `D` diagonal and positive. -/
theorem coblePosL_factor :
    coblePosL * coblePosD * coblePosLᵀ = (108000 : ℤ) • coblePosMatrixZ := by
  decide

/-- `L · L⁻¹ = 3600 · 1`, so `L` is invertible. -/
theorem coblePosL_inverse : coblePosL * coblePosLinv = (3600 : ℤ) • 1 := by
  decide

/-! ### The quadratic form of `coblePosMatrixZ` is positive definite -/

/-- A diagonal form with positive entries is positive on nonzero vectors. -/
theorem dotProduct_diagonal_mulVec_pos {n : Type} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (hd : ∀ i, 0 < d i) {w : n → ℝ} (hw : w ≠ 0) :
    0 < w ⬝ᵥ (Matrix.diagonal d *ᵥ w) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, w i ≠ 0 := Function.ne_iff.mp hw
  rw [dotProduct]
  refine Finset.sum_pos' ?_ ⟨i₀, Finset.mem_univ _, ?_⟩
  · intro i _
    rw [Matrix.mulVec_diagonal, show w i * (d i * w i) = d i * (w i * w i) by ring]
    exact mul_nonneg (le_of_lt (hd i)) (mul_self_nonneg _)
  · rw [Matrix.mulVec_diagonal, show w i₀ * (d i₀ * w i₀) = d i₀ * (w i₀ * w i₀) by ring]
    exact mul_pos (hd i₀) (mul_self_pos.mpr hi₀)

/-- Associate a dot product with a matrix-vector product on the left. -/
theorem dotProduct_mulVec_transpose {n : Type} [Fintype n]
    (A : Matrix n n ℝ) (v w : n → ℝ) : v ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem coblePosD_diagonal :
    coblePosD.map (Int.castRingHom ℝ) = Matrix.diagonal fun i => (coblePosD i i : ℝ) := by
  ext i j
  rw [Matrix.map_apply, coblePosD, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem coblePosD_pos (i : Fin 9) : 0 < (coblePosD i i : ℝ) := by
  rw [coblePosD, Matrix.diagonal_apply, if_pos rfl]
  fin_cases i <;> norm_num [coblePosDiag]

theorem coblePosL_inverse_real :
    coblePosL.map (Int.castRingHom ℝ) * coblePosLinv.map (Int.castRingHom ℝ)
      = (3600 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℝ) := by
  have h := congrArg (fun M : Matrix (Fin 9) (Fin 9) ℤ => M.map (Int.castRingHom ℝ))
    coblePosL_inverse
  simp only [Matrix.map_mul] at h
  rw [h, Matrix.map_smul]
  · ext i j
    simp [Matrix.smul_apply, smul_eq_mul]
  · intro a
    simp

theorem coblePosL_det_ne_zero : (coblePosL.map (Int.castRingHom ℝ)).det ≠ 0 := by
  have hmul : (coblePosL.map (Int.castRingHom ℝ)).det *
      (coblePosLinv.map (Int.castRingHom ℝ)).det = (3600 : ℝ) ^ 9 := by
    rw [← Matrix.det_mul, coblePosL_inverse_real, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one]
  intro hzero
  rw [hzero, zero_mul] at hmul
  norm_num at hmul

theorem coblePosL_factor_real :
    coblePosL.map (Int.castRingHom ℝ) * coblePosD.map (Int.castRingHom ℝ) *
        (coblePosL.map (Int.castRingHom ℝ))ᵀ
      = (108000 : ℝ) • coblePosMatrixZ.map (Int.castRingHom ℝ) := by
  have h := congrArg (fun M : Matrix (Fin 9) (Fin 9) ℤ => M.map (Int.castRingHom ℝ))
    coblePosL_factor
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  rw [h, Matrix.map_smul]
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    simp
  · intro a
    simp

/-- The negation of the complement Gram matrix is positive definite. -/
theorem coblePosMatrix_quadratic_pos {v : Fin 9 → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ (coblePosMatrixZ.map (Int.castRingHom ℝ) *ᵥ v) := by
  have hw : (coblePosL.map (Int.castRingHom ℝ))ᵀ *ᵥ v ≠ 0 := by
    intro h0
    refine hv (Matrix.eq_zero_of_mulVec_eq_zero ?_ h0)
    rw [Matrix.det_transpose]
    exact coblePosL_det_ne_zero
  have hpos : 0 < ((coblePosL.map (Int.castRingHom ℝ))ᵀ *ᵥ v) ⬝ᵥ
      (coblePosD.map (Int.castRingHom ℝ) *ᵥ ((coblePosL.map (Int.castRingHom ℝ))ᵀ *ᵥ v)) := by
    rw [coblePosD_diagonal]
    exact dotProduct_diagonal_mulVec_pos _ coblePosD_pos hw
  have hkey : ((coblePosL.map (Int.castRingHom ℝ))ᵀ *ᵥ v) ⬝ᵥ
      (coblePosD.map (Int.castRingHom ℝ) *ᵥ ((coblePosL.map (Int.castRingHom ℝ))ᵀ *ᵥ v))
      = v ⬝ᵥ ((coblePosL.map (Int.castRingHom ℝ) * coblePosD.map (Int.castRingHom ℝ) *
          (coblePosL.map (Int.castRingHom ℝ))ᵀ) *ᵥ v) := by
    conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec_transpose]
  rw [coblePosL_factor_real, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hkey
  nlinarith [hpos, hkey]

/-- The negation of the complement Gram matrix is positive semidefinite. -/
theorem coblePosMatrix_quadratic_nonneg (v : Fin 9 → ℝ) :
    0 ≤ v ⬝ᵥ (coblePosMatrixZ.map (Int.castRingHom ℝ) *ᵥ v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact le_of_lt (coblePosMatrix_quadratic_pos hv)



/-! ## The real matrix of an isometry of `T_Co` -/

/-- Associate a dot product with two matrix-vector products. -/
theorem dotProduct_mulVec_mulVec {n : Type} [Fintype n]
    (P Q : Matrix n n ℝ) (x y : n → ℝ) :
    (P *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ ((Pᵀ * Q) *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec,
    show P *ᵥ x = x ᵥ* Pᵀ from Matrix.mulVec_transpose Pᵀ x,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]

/-- The integer matrix of an isometry of `T_Co`, in the standard basis. -/
noncomputable def cobleIntMatrix (g : OrthogonalGroup cobleLattice) : Matrix (Fin 11) (Fin 11) ℤ :=
  LinearMap.toMatrix' (g.1 : ↥cobleLattice.obj.carrier →ₗ[ℤ] ↥cobleLattice.obj.carrier)

theorem cobleIntMatrix_mulVec (g : OrthogonalGroup cobleLattice) (x : Fin 11 → ℤ) :
    cobleIntMatrix g *ᵥ x = (g.1 x : Fin 11 → ℤ) :=
  LinearMap.toMatrix'_mulVec _ _

/-- The real matrix of an isometry of `T_Co`. -/
noncomputable def cobleRealMatrix (g : OrthogonalGroup cobleLattice) :
    Matrix (Fin 11) (Fin 11) ℝ :=
  (cobleIntMatrix g).map (Int.castRingHom ℝ)

/-- The integer matrix of an isometry preserves the Gram matrix. -/
theorem cobleIntMatrix_isometry (g : OrthogonalGroup cobleLattice) :
    (cobleIntMatrix g)ᵀ * cobleGramMatrix * cobleIntMatrix g = cobleGramMatrix := by
  have hcomp : (Matrix.toBilin' cobleGramMatrix).comp (Matrix.toLin' (cobleIntMatrix g))
      (Matrix.toLin' (cobleIntMatrix g)) = Matrix.toBilin' cobleGramMatrix := by
    refine LinearMap.BilinForm.ext fun x y => ?_
    rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      cobleIntMatrix_mulVec, cobleIntMatrix_mulVec]
    exact g.property x y
  have h := Matrix.toBilin'_comp (M := cobleGramMatrix) (cobleIntMatrix g) (cobleIntMatrix g)
  rw [hcomp] at h
  exact (Matrix.toBilin'.injective h).symm

/-- The real matrix of an isometry of `T_Co` preserves the real Gram matrix. -/
theorem cobleRealMatrix_isometry_matrix (g : OrthogonalGroup cobleLattice) :
    (cobleRealMatrix g)ᵀ * cobleGramReal * cobleRealMatrix g = cobleGramReal := by
  have h := congrArg (fun M : Matrix (Fin 11) (Fin 11) ℤ => M.map (Int.castRingHom ℝ))
    (cobleIntMatrix_isometry g)
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  simpa [cobleRealMatrix, cobleGramReal] using h

/-- An isometry of `T_Co` preserves the real form. -/
theorem cobleRealForm_isometry (g : OrthogonalGroup cobleLattice) (x y : Fin 11 → ℝ) :
    cobleRealForm (cobleRealMatrix g *ᵥ x) (cobleRealMatrix g *ᵥ y) = cobleRealForm x y := by
  rw [cobleRealForm_dot, cobleRealForm_dot, Matrix.mulVec_mulVec, dotProduct_mulVec_mulVec,
    ← Matrix.mul_assoc, cobleRealMatrix_isometry_matrix]

/-- The real action of an isometry of `T_Co`. -/
noncomputable def cobleRealAction (g : OrthogonalGroup cobleLattice) :
    (Fin 11 → ℝ) →ₗ[ℝ] (Fin 11 → ℝ) :=
  Matrix.mulVecLin (cobleRealMatrix g)

/-! ## The positive definite plane and its orthogonal decomposition -/

/-- The coordinates of a vector in the plane `P = ⟨p₁, p₂⟩`. -/
noncomputable def coblePosPlaneCoord : (Fin 11 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.pi fun i : Fin 2 =>
    if i = 0 then (1 / 2 : ℝ) • cobleRealForm cobleP1
    else (1 / 4 : ℝ) • cobleRealForm cobleP2

theorem coblePosPlaneCoord_apply (x : Fin 11 → ℝ) :
    coblePosPlaneCoord x =
      ![cobleRealForm cobleP1 x / 2, cobleRealForm cobleP2 x / 4] := by
  ext i
  rw [coblePosPlaneCoord, LinearMap.pi_apply]
  fin_cases i <;> simp [div_eq_mul_inv, mul_comm]

theorem coblePosPlaneCoord_zero (x : Fin 11 → ℝ) :
    coblePosPlaneCoord x 0 = cobleRealForm cobleP1 x / 2 := by
  rw [coblePosPlaneCoord_apply]; simp

theorem coblePosPlaneCoord_one (x : Fin 11 → ℝ) :
    coblePosPlaneCoord x 1 = cobleRealForm cobleP2 x / 4 := by
  rw [coblePosPlaneCoord_apply]; simp

/-- The inclusion of the plane `P = ⟨p₁, p₂⟩`. -/
noncomputable def coblePosPlaneIncl : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 11 → ℝ) :=
  LinearMap.pi fun i : Fin 11 =>
    (cobleP1 i) • LinearMap.proj (0 : Fin 2) + (cobleP2 i) • LinearMap.proj (1 : Fin 2)

theorem coblePosPlaneIncl_apply (c : Fin 2 → ℝ) (i : Fin 11) :
    coblePosPlaneIncl c i = c 0 * cobleP1 i + c 1 * cobleP2 i := by
  rw [coblePosPlaneIncl, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, LinearMap.proj_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem coblePosPlaneIncl_eq (c : Fin 2 → ℝ) :
    coblePosPlaneIncl c = c 0 • cobleP1 + c 1 • cobleP2 := by
  ext i
  rw [coblePosPlaneIncl_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_comm]

/-- The form of `p₁` against a vector of the plane. -/
theorem cobleRealForm_p1_plane (c : Fin 2 → ℝ) :
    cobleRealForm cobleP1 (coblePosPlaneIncl c) = c 0 * 2 := by
  rw [coblePosPlaneIncl_eq, map_add, map_smul, map_smul, cobleRealForm_p1_p1,
    cobleRealForm_p1_p2, smul_eq_mul, smul_eq_mul]
  ring

/-- The form of `p₂` against a vector of the plane. -/
theorem cobleRealForm_p2_plane (c : Fin 2 → ℝ) :
    cobleRealForm cobleP2 (coblePosPlaneIncl c) = c 1 * 4 := by
  rw [coblePosPlaneIncl_eq, map_add, map_smul, map_smul, cobleRealForm_symm cobleP2 cobleP1,
    cobleRealForm_p1_p2, cobleRealForm_p2_p2, smul_eq_mul, smul_eq_mul]
  ring

/-- The quadratic form of the plane is `2 x² + 4 y²`. -/
theorem cobleRealForm_plane_expand (c : Fin 2 → ℝ) :
    cobleRealForm (coblePosPlaneIncl c) (coblePosPlaneIncl c)
      = 2 * (c 0) ^ 2 + 4 * (c 1) ^ 2 := by
  calc cobleRealForm (coblePosPlaneIncl c) (coblePosPlaneIncl c)
      = cobleRealForm (c 0 • cobleP1 + c 1 • cobleP2) (coblePosPlaneIncl c) := by
        rw [coblePosPlaneIncl_eq]
    _ = c 0 * cobleRealForm cobleP1 (coblePosPlaneIncl c)
          + c 1 * cobleRealForm cobleP2 (coblePosPlaneIncl c) := by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    _ = c 0 * (c 0 * 2) + c 1 * (c 1 * 4) := by
        rw [cobleRealForm_p1_plane, cobleRealForm_p2_plane]
    _ = 2 * (c 0) ^ 2 + 4 * (c 1) ^ 2 := by ring

theorem coblePosPlaneCoord_incl (c : Fin 2 → ℝ) : coblePosPlaneCoord (coblePosPlaneIncl c) = c := by
  have h1 := cobleRealForm_p1_plane c
  have h2 := cobleRealForm_p2_plane c
  ext i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [coblePosPlaneCoord_zero, h1]; ring
  · rw [coblePosPlaneCoord_one, h2]; ring

/-- The plane `P = ⟨p₁, p₂⟩` is positive definite. -/
theorem cobleRealForm_plane_pos {c : Fin 2 → ℝ} (hc : c ≠ 0) :
    0 < cobleRealForm (coblePosPlaneIncl c) (coblePosPlaneIncl c) := by
  rw [cobleRealForm_plane_expand]
  have hc' : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    rcases eq_or_ne (c 0) 0 with h | h
    · refine Or.inr fun h1 => hc ?_
      funext i
      fin_cases i <;> simp [h, h1]
    · exact Or.inl h
  rcases hc' with h | h
  · nlinarith [mul_self_pos.mpr h, sq_nonneg (c 1 : ℝ)]
  · nlinarith [mul_self_pos.mpr h, sq_nonneg (c 0 : ℝ)]



/-! ### The coordinates of the complement inclusion -/

theorem cobleWIncl_apply_zero (v : Fin 9 → ℝ) : cobleWIncl v 0 = 0 := by
  rw [cobleWIncl_apply, if_pos (by decide : ((0 : Fin 11)).val = 0)]

theorem cobleWIncl_apply_one (v : Fin 9 → ℝ) : cobleWIncl v 1 = v 0 := by
  rw [cobleWIncl_apply, if_neg (by decide : ¬ ((1 : Fin 11)).val = 0),
    if_pos (by decide : ((1 : Fin 11)).val = 1)]

theorem cobleWIncl_apply_two (v : Fin 9 → ℝ) : cobleWIncl v 2 = -v 0 := by
  rw [cobleWIncl_apply, if_neg (by decide : ¬ ((2 : Fin 11)).val = 0),
    if_neg (by decide : ¬ ((2 : Fin 11)).val = 1),
    if_pos (by decide : ((2 : Fin 11)).val = 2)]

theorem cobleWIncl_apply_ge (v : Fin 9 → ℝ) (i : Fin 11) (hi : 3 ≤ i.val) :
    cobleWIncl v i = v ⟨i.val - 2, by omega⟩ := by
  rw [cobleWIncl_apply, if_neg (by omega : ¬ i.val = 0), if_neg (by omega : ¬ i.val = 1),
    if_neg (by omega : ¬ i.val = 2)]

/-! ### Negative definiteness of the complement -/

theorem cobleWBasisGramZ_map_eq_neg :
    cobleWBasisGramZ.map (Int.castRingHom ℝ) = -(coblePosMatrixZ.map (Int.castRingHom ℝ)) := by
  have h := congrArg (fun M : Matrix (Fin 9) (Fin 9) ℤ => M.map (Int.castRingHom ℝ))
    coblePosMatrixZ_eq
  rw [show (-cobleWBasisGramZ).map (Int.castRingHom ℝ)
      = -(cobleWBasisGramZ.map (Int.castRingHom ℝ)) from by
    ext i j
    simp] at h
  simpa using congrArg Neg.neg h.symm

theorem cobleWBasisGramZ_quadratic_neg {v : Fin 9 → ℝ} (hv : v ≠ 0) :
    v ⬝ᵥ (cobleWBasisGramZ.map (Int.castRingHom ℝ) *ᵥ v) < 0 := by
  rw [cobleWBasisGramZ_map_eq_neg, Matrix.neg_mulVec, dotProduct_neg]
  have := coblePosMatrix_quadratic_pos hv
  linarith

theorem cobleWBasisGramZ_quadratic_nonpos (v : Fin 9 → ℝ) :
    v ⬝ᵥ (cobleWBasisGramZ.map (Int.castRingHom ℝ) *ᵥ v) ≤ 0 := by
  rw [cobleWBasisGramZ_map_eq_neg, Matrix.neg_mulVec, dotProduct_neg]
  have := coblePosMatrix_quadratic_nonneg v
  linarith

/-- A vector orthogonal to the positive plane is in the complement `P^⊥ = {x₀ = 0, x₂ = −x₁}`. -/
theorem cobleRealForm_orthogonal_exists (w : Fin 11 → ℝ)
    (h1 : cobleRealForm w cobleP1 = 0) (h2 : cobleRealForm w cobleP2 = 0) :
    ∃ v : Fin 9 → ℝ, w = cobleWIncl v := by
  have h0 : w 0 = 0 := by
    have h := h1
    rw [cobleRealForm_symm w cobleP1, cobleRealForm_p1_left] at h
    linarith
  have hs : w 1 + w 2 = 0 := by
    have h := h2
    rw [cobleRealForm_symm w cobleP2, cobleRealForm_p2_left] at h
    linarith
  refine ⟨fun j => if j.val = 0 then w 1 else w ⟨j.val + 2, by omega⟩, ?_⟩
  ext i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ 3 ≤ i.val := by omega
  rcases hi with h | h | h | h
  · rw [show i = 0 from Fin.ext h, cobleWIncl_apply_zero]
    exact h0
  · rw [show i = 1 from Fin.ext h, cobleWIncl_apply_one]
    simp
  · rw [show i = 2 from Fin.ext h, cobleWIncl_apply_two]
    simp
    linarith
  · rw [cobleWIncl_apply_ge _ _ h]
    have hne : ¬ ((⟨i.val - 2, by omega⟩ : Fin 9).val = 0) := by
      rw [show (⟨i.val - 2, by omega⟩ : Fin 9).val = i.val - 2 from rfl]
      omega
    rw [if_neg hne]
    congr 1
    exact Fin.ext (by
      change i.val = (⟨i.val - 2, by omega⟩ : Fin 9).val + 2
      have hv : (⟨i.val - 2, by omega⟩ : Fin 9).val = i.val - 2 := rfl
      omega)

/-- The complement of the positive plane is negative definite. -/
theorem cobleRealForm_neg_of_orthogonal (w : Fin 11 → ℝ)
    (h1 : cobleRealForm w cobleP1 = 0) (h2 : cobleRealForm w cobleP2 = 0) (hw : w ≠ 0) :
    cobleRealForm w w < 0 := by
  obtain ⟨v, rfl⟩ := cobleRealForm_orthogonal_exists w h1 h2
  have hvne : v ≠ 0 := by
    intro hzero
    exact hw (by rw [hzero, map_zero])
  rw [cobleRealForm_wIncl]
  exact cobleWBasisGramZ_quadratic_neg hvne

/-- The complement of the positive plane is negative semidefinite. -/
theorem cobleRealForm_nonpos_of_orthogonal (w : Fin 11 → ℝ)
    (h1 : cobleRealForm w cobleP1 = 0) (h2 : cobleRealForm w cobleP2 = 0) :
    cobleRealForm w w ≤ 0 := by
  obtain ⟨v, rfl⟩ := cobleRealForm_orthogonal_exists w h1 h2
  rw [cobleRealForm_wIncl]
  exact cobleWBasisGramZ_quadratic_nonpos v

/-- The plane `P^⊥` is annihilated by the plane coordinates. -/
theorem coblePosPlaneCoord_of_orthogonal (w : Fin 11 → ℝ)
    (h1 : cobleRealForm w cobleP1 = 0) (h2 : cobleRealForm w cobleP2 = 0) :
    coblePosPlaneCoord w = 0 := by
  ext i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [coblePosPlaneCoord_zero, cobleRealForm_symm cobleP1 w, h1]
    simp
  · rw [coblePosPlaneCoord_one, cobleRealForm_symm cobleP2 w, h2]
    simp

/-- The complement of the plane is annihilated by the plane coordinates. -/
theorem coblePosPlaneCoord_wIncl (v : Fin 9 → ℝ) : coblePosPlaneCoord (cobleWIncl v) = 0 := by
  refine coblePosPlaneCoord_of_orthogonal _ ?_ ?_
  · rw [cobleRealForm_symm, cobleRealForm_p1_left, cobleWIncl_apply_zero]; ring
  · rw [cobleRealForm_symm, cobleRealForm_p2_left, cobleWIncl_apply_one, cobleWIncl_apply_two]
    ring



/-! ## The orthogonal decomposition of the real form -/

/-- The plane component of a vector. -/
noncomputable def coblePlanePart (y : Fin 11 → ℝ) : Fin 11 → ℝ :=
  coblePosPlaneIncl (coblePosPlaneCoord y)

/-- The orthogonal projection onto the complement of the positive plane. -/
noncomputable def coblePlaneProject : (Fin 11 → ℝ) →ₗ[ℝ] (Fin 11 → ℝ) :=
  LinearMap.id - coblePosPlaneIncl.comp coblePosPlaneCoord

theorem coblePlaneProject_apply (y : Fin 11 → ℝ) :
    coblePlaneProject y = y - coblePlanePart y := by
  rw [coblePlaneProject, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    coblePlanePart]

theorem coblePlanePart_add_project (y : Fin 11 → ℝ) :
    coblePlanePart y + coblePlaneProject y = y := by
  rw [coblePlaneProject_apply]
  abel

theorem cobleRealForm_p1_project (y : Fin 11 → ℝ) :
    cobleRealForm cobleP1 (coblePlaneProject y) = 0 := by
  rw [coblePlaneProject_apply, coblePlanePart, map_sub, cobleRealForm_p1_plane,
    coblePosPlaneCoord_zero, cobleRealForm_p1_left]
  ring

theorem cobleRealForm_p2_project (y : Fin 11 → ℝ) :
    cobleRealForm cobleP2 (coblePlaneProject y) = 0 := by
  rw [coblePlaneProject_apply, coblePlanePart, map_sub, cobleRealForm_p2_plane,
    coblePosPlaneCoord_one, cobleRealForm_p2_left]
  ring

/-- The complement component is negative semidefinite. -/
theorem cobleRealForm_project_nonpos (y : Fin 11 → ℝ) :
    cobleRealForm (coblePlaneProject y) (coblePlaneProject y) ≤ 0 := by
  refine cobleRealForm_nonpos_of_orthogonal _ ?_ ?_
  · rw [cobleRealForm_symm]; exact cobleRealForm_p1_project y
  · rw [cobleRealForm_symm]; exact cobleRealForm_p2_project y

/-- The plane component is positive semidefinite. -/
theorem cobleRealForm_planePart_nonneg (y : Fin 11 → ℝ) :
    0 ≤ cobleRealForm (coblePlanePart y) (coblePlanePart y) := by
  rw [coblePlanePart, cobleRealForm_plane_expand]
  positivity

/-- The plane and its complement are orthogonal. -/
theorem cobleRealForm_planeIncl_project (c : Fin 2 → ℝ) (y : Fin 11 → ℝ) :
    cobleRealForm (coblePosPlaneIncl c) (coblePlaneProject y) = 0 := by
  have h1 : cobleRealForm cobleP1 (coblePlaneProject y) = 0 := cobleRealForm_p1_project y
  have h2 : cobleRealForm cobleP2 (coblePlaneProject y) = 0 := cobleRealForm_p2_project y
  conv_lhs => rw [coblePosPlaneIncl_eq]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
    mul_zero, add_zero]

/-- The orthogonal decomposition of the self-pairing. -/
theorem cobleRealForm_self_decomp (y : Fin 11 → ℝ) :
    cobleRealForm y y = cobleRealForm (coblePlanePart y) (coblePlanePart y)
      + cobleRealForm (coblePlaneProject y) (coblePlaneProject y) := by
  have hcross : cobleRealForm (coblePlanePart y) (coblePlaneProject y) = 0 :=
    cobleRealForm_planeIncl_project (coblePosPlaneCoord y) y
  have hcross' : cobleRealForm (coblePlaneProject y) (coblePlanePart y) = 0 := by
    rw [cobleRealForm_symm]
    exact hcross
  conv_lhs => rw [← coblePlanePart_add_project y]
  simp only [map_add, LinearMap.add_apply, hcross, hcross', add_zero, zero_add]

/-- The plane coordinates vanish exactly on the complement of the plane. -/
theorem cobleRealForm_orthogonal_of_coord_zero (u : Fin 11 → ℝ)
    (h : coblePosPlaneCoord u = 0) :
    cobleRealForm u cobleP1 = 0 ∧ cobleRealForm u cobleP2 = 0 := by
  have h0 : cobleRealForm cobleP1 u = 0 := by
    have h' : cobleRealForm cobleP1 u / 2 = 0 := by
      have := congrFun h 0
      rwa [coblePosPlaneCoord_zero] at this
    linarith
  have h1 : cobleRealForm cobleP2 u = 0 := by
    have h' : cobleRealForm cobleP2 u / 4 = 0 := by
      have := congrFun h 1
      rwa [coblePosPlaneCoord_one] at this
    linarith
  exact ⟨by rwa [cobleRealForm_symm] at h0, by rwa [cobleRealForm_symm] at h1⟩



/-! ## The sign of the plane determinant -/

theorem cobleIntMatrix_mul (g h : OrthogonalGroup cobleLattice) :
    cobleIntMatrix (g * h) = cobleIntMatrix g * cobleIntMatrix h := by
  have key : ((g * h).1 : ↥cobleLattice.obj.carrier →ₗ[ℤ] ↥cobleLattice.obj.carrier)
      = (g.1 : ↥cobleLattice.obj.carrier →ₗ[ℤ] ↥cobleLattice.obj.carrier)
        * (h.1 : ↥cobleLattice.obj.carrier →ₗ[ℤ] ↥cobleLattice.obj.carrier) := rfl
  rw [cobleIntMatrix, cobleIntMatrix, cobleIntMatrix, key]
  exact LinearMap.toMatrix'_mul _ _

theorem cobleIntMatrix_one : cobleIntMatrix (1 : OrthogonalGroup cobleLattice) = 1 := by
  rw [cobleIntMatrix, ← LinearMap.toMatrix'_one]
  rfl

theorem cobleRealMatrix_mul (g h : OrthogonalGroup cobleLattice) :
    cobleRealMatrix (g * h) = cobleRealMatrix g * cobleRealMatrix h := by
  rw [cobleRealMatrix, cobleRealMatrix, cobleRealMatrix, cobleIntMatrix_mul, Matrix.map_mul]

theorem cobleRealMatrix_one : cobleRealMatrix (1 : OrthogonalGroup cobleLattice) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [cobleRealMatrix, cobleIntMatrix_one, Matrix.one_apply, h]

theorem cobleRealAction_mul (g h : OrthogonalGroup cobleLattice) :
    cobleRealAction (g * h) = (cobleRealAction g).comp (cobleRealAction h) := by
  rw [cobleRealAction, cobleRealAction, cobleRealAction, cobleRealMatrix_mul, Matrix.mulVecLin_mul]

theorem cobleRealAction_one :
    cobleRealAction (1 : OrthogonalGroup cobleLattice) = LinearMap.id := by
  rw [cobleRealAction, cobleRealMatrix_one, Matrix.mulVecLin_one]

/-- The real matrix of an isometry is invertible. -/
theorem cobleRealMatrix_det_ne_zero (g : OrthogonalGroup cobleLattice) :
    (cobleRealMatrix g).det ≠ 0 := by
  refine Matrix.det_ne_zero_of_right_inverse (B := cobleRealMatrix g⁻¹) ?_
  rw [← cobleRealMatrix_mul, mul_inv_cancel, cobleRealMatrix_one]

theorem cobleRealAction_injective (g : OrthogonalGroup cobleLattice) :
    Function.Injective (cobleRealAction g) := by
  rw [cobleRealAction]
  exact Matrix.mulVec_injective_of_det_ne_zero (cobleRealMatrix_det_ne_zero g)

/-- The `P`-component `A(g)` of an isometry of `T_Co ⊗ ℝ`. -/
noncomputable def coblePlaneA (g : OrthogonalGroup cobleLattice) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  coblePosPlaneCoord.comp ((cobleRealAction g).comp coblePosPlaneIncl)

theorem coblePlaneA_apply (g : OrthogonalGroup cobleLattice) (c : Fin 2 → ℝ) :
    coblePlaneA g c = coblePosPlaneCoord (cobleRealAction g (coblePosPlaneIncl c)) := rfl

theorem coblePlaneA_one : coblePlaneA (1 : OrthogonalGroup cobleLattice) = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  rw [coblePlaneA_apply, cobleRealAction_one, LinearMap.id_apply, coblePosPlaneCoord_incl,
    LinearMap.id_apply]

/-- The mixed component of the path from `A(g)A(h)` to `A(gh)`. -/
noncomputable def coblePlaneMix (g h : OrthogonalGroup cobleLattice) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (coblePosPlaneCoord.comp (cobleRealAction g)).comp
    (coblePlaneProject.comp ((cobleRealAction h).comp coblePosPlaneIncl))

/-- The path from `A(g)A(h)` to `A(gh)`. -/
noncomputable def coblePlaneInterp (g h : OrthogonalGroup cobleLattice) (t : ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (coblePlaneA g).comp (coblePlaneA h) + t • coblePlaneMix g h

theorem coblePlaneInterp_apply (g h : OrthogonalGroup cobleLattice) (t : ℝ)
    (c : Fin 2 → ℝ) :
    coblePlaneInterp g h t c = coblePosPlaneCoord (cobleRealAction g
      (coblePlanePart (cobleRealAction h (coblePosPlaneIncl c))
        + t • coblePlaneProject (cobleRealAction h (coblePosPlaneIncl c)))) := by
  simp only [coblePlaneInterp, coblePlaneA, coblePlaneMix, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, coblePlanePart, map_add, map_smul]

theorem coblePlaneInterp_zero (g h : OrthogonalGroup cobleLattice) :
    coblePlaneInterp g h 0 = (coblePlaneA g).comp (coblePlaneA h) := by
  rw [coblePlaneInterp]
  simp

theorem coblePlaneInterp_one (g h : OrthogonalGroup cobleLattice) :
    coblePlaneInterp g h 1 = coblePlaneA (g * h) := by
  refine LinearMap.ext fun c => ?_
  rw [coblePlaneInterp_apply, one_smul, coblePlanePart_add_project, coblePlaneA_apply,
    cobleRealAction_mul, LinearMap.comp_apply]



/-! ### The path stays inside the general linear group -/

theorem coblePlaneInterp_ker (g h : OrthogonalGroup cobleLattice) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (c : Fin 2 → ℝ) (hc : coblePlaneInterp g h t c = 0) : c = 0 := by
  by_contra hcne
  have hxne : coblePosPlaneIncl c ≠ 0 := by
    intro h0
    exact hcne (by rw [← coblePosPlaneCoord_incl c, h0, map_zero])
  set x : Fin 11 → ℝ := coblePosPlaneIncl c with hx
  set y : Fin 11 → ℝ := cobleRealAction h x with hy
  set u : Fin 11 → ℝ := coblePlaneProject y with hu
  have hcoord : coblePosPlaneCoord (cobleRealAction g (coblePlanePart y + t • u)) = 0 := by
    rw [coblePlaneInterp_apply g h t c] at hc
    exact hc
  obtain ⟨ho1, ho2⟩ := cobleRealForm_orthogonal_of_coord_zero _ hcoord
  have hBpp : cobleRealForm (coblePlanePart y) u = 0 :=
    cobleRealForm_planeIncl_project (coblePosPlaneCoord y) y
  have hBup : cobleRealForm u (coblePlanePart y) = 0 := by
    rw [cobleRealForm_symm]
    exact hBpp
  have hdec : cobleRealForm y y = cobleRealForm (coblePlanePart y) (coblePlanePart y)
      + cobleRealForm u u := cobleRealForm_self_decomp y
  have hByy : cobleRealForm y y = cobleRealForm x x := cobleRealForm_isometry h x x
  have hBuu : cobleRealForm u u = cobleRealForm x x
      - cobleRealForm (coblePlanePart y) (coblePlanePart y) := by
    rw [hByy] at hdec
    linarith
  have hzval : cobleRealForm (coblePlanePart y + t • u) (coblePlanePart y + t • u)
      = (1 - t ^ 2) * cobleRealForm (coblePlanePart y) (coblePlanePart y)
        + t ^ 2 * cobleRealForm x x := by
    have hexp : cobleRealForm (coblePlanePart y + t • u) (coblePlanePart y + t • u)
        = cobleRealForm (coblePlanePart y) (coblePlanePart y) + t ^ 2 * cobleRealForm u u := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBpp, hBup, mul_zero, add_zero]
      ring
    rw [hexp, hBuu]
    ring
  have hxpos : 0 < cobleRealForm x x := cobleRealForm_plane_pos hcne
  have hzpos : 0 < cobleRealForm (coblePlanePart y + t • u) (coblePlanePart y + t • u) := by
    rw [hzval]
    have hpp : 0 ≤ cobleRealForm (coblePlanePart y) (coblePlanePart y) :=
      cobleRealForm_planePart_nonneg y
    have hbu : cobleRealForm u u ≤ 0 := cobleRealForm_project_nonpos y
    have hdiff : 0 ≤ cobleRealForm (coblePlanePart y) (coblePlanePart y)
        - cobleRealForm x x := by linarith
    have h1mt : 0 ≤ 1 - t ^ 2 := by nlinarith
    have hprod : 0 ≤ (1 - t ^ 2) * (cobleRealForm (coblePlanePart y) (coblePlanePart y)
        - cobleRealForm x x) := mul_nonneg h1mt hdiff
    nlinarith [hprod, hxpos, sq_nonneg t, ht0, ht1]
  have hzne : coblePlanePart y + t • u ≠ 0 := by
    intro h0
    rw [h0] at hzpos
    simp at hzpos
  have hgz : cobleRealAction g (coblePlanePart y + t • u) ≠ 0 := by
    intro h0
    refine hzne (cobleRealAction_injective g ?_)
    rw [h0, map_zero]
  have hneg : cobleRealForm (cobleRealAction g (coblePlanePart y + t • u))
      (cobleRealAction g (coblePlanePart y + t • u)) < 0 :=
    cobleRealForm_neg_of_orthogonal _ ho1 ho2 hgz
  have heq : cobleRealForm (cobleRealAction g (coblePlanePart y + t • u))
      (cobleRealAction g (coblePlanePart y + t • u))
      = cobleRealForm (coblePlanePart y + t • u) (coblePlanePart y + t • u) :=
    cobleRealForm_isometry g _ _
  linarith

theorem coblePlaneInterp_injective (g h : OrthogonalGroup cobleLattice) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : Function.Injective (coblePlaneInterp g h t) := by
  intro c d hcd
  have hzero : coblePlaneInterp g h t (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  exact sub_eq_zero.mp (coblePlaneInterp_ker g h ht0 ht1 (c - d) hzero)

theorem coblePlaneInterp_det_ne_zero (g h : OrthogonalGroup cobleLattice) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : LinearMap.det (coblePlaneInterp g h t) ≠ 0 := by
  have hinj := coblePlaneInterp_injective g h ht0 ht1
  have hker : LinearMap.ker (coblePlaneInterp g h t) = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  intro hdet
  have hkerne : LinearMap.ker (coblePlaneInterp g h t) ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hdet
  rw [hker] at hkerne
  exact hkerne rfl

theorem coblePlaneInterp_det_continuous (g h : OrthogonalGroup cobleLattice) :
    Continuous fun t : ℝ => LinearMap.det (coblePlaneInterp g h t) := by
  have hfun : (fun t : ℝ => LinearMap.det (coblePlaneInterp g h t))
      = fun t : ℝ => (LinearMap.toMatrix' ((coblePlaneA g).comp (coblePlaneA h))
          + t • LinearMap.toMatrix' (coblePlaneMix g h)).det := by
    funext t
    rw [← LinearMap.det_toMatrix', coblePlaneInterp, map_add, map_smul]
  rw [hfun]
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

/-- A continuous function with no zeros on `[0, 1]` has the same sign at both ends. -/
theorem pos_mul_pos_of_ne_zero_on_Icc {f : ℝ → ℝ} (hc : ContinuousOn f (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) : 0 < f 0 * f 1 := by
  have h0 : f 0 ≠ 0 := hne 0 (by norm_num)
  have h1 : f 1 ≠ 0 := hne 1 (by norm_num)
  rcases lt_or_gt_of_ne h0 with h0neg | h0pos
  · have h1neg : f 1 < 0 := by
      by_contra hcon
      have h1pos : 0 < f 1 := lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm h1)
      have hmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := ⟨h0neg.le, h1pos.le⟩
      obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc hmem
      exact hne s hs hsz
    exact mul_pos_of_neg_of_neg h0neg h1neg
  · have h1pos : 0 < f 1 := by
      by_contra hcon
      have h1neg : f 1 < 0 := lt_of_le_of_ne (not_lt.mp hcon) h1
      have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨h1neg.le, h0pos.le⟩
      obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc hmem
      exact hne s hs hsz
    exact mul_pos h0pos h1pos

/-- **The sign of the plane determinant is multiplicative**, up to the removal of a positive
factor: `det A(g) · det A(h) · det A(gh) > 0`. -/
theorem coblePlaneA_det_triple_pos (g h : OrthogonalGroup cobleLattice) :
    0 < LinearMap.det (coblePlaneA g) * LinearMap.det (coblePlaneA h)
      * LinearMap.det (coblePlaneA (g * h)) := by
  have hcont : ContinuousOn (fun t : ℝ => LinearMap.det (coblePlaneInterp g h t))
      (Set.Icc 0 1) := (coblePlaneInterp_det_continuous g h).continuousOn
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, LinearMap.det (coblePlaneInterp g h t) ≠ 0 :=
    fun t ht => coblePlaneInterp_det_ne_zero g h ht.1 ht.2
  have hsign := pos_mul_pos_of_ne_zero_on_Icc hcont hne
  rw [coblePlaneInterp_zero, coblePlaneInterp_one, LinearMap.det_comp] at hsign
  exact hsign

/-- The plane determinant of an isometry of `T_Co` is nonzero. -/
theorem coblePlaneA_det_ne_zero (g : OrthogonalGroup cobleLattice) :
    LinearMap.det (coblePlaneA g) ≠ 0 := by
  have h := coblePlaneA_det_triple_pos g 1
  rw [mul_one, coblePlaneA_one, LinearMap.det_id] at h
  intro h0
  rw [h0, mul_zero] at h
  exact absurd h (lt_irrefl 0)



/-! ## The orientation subgroup `O⁺(T_Co)` and `Γ_Co = O⁺(T_Co) ∩ ker ρ` -/

/-- The sign of a real number, as a unit of `ℤ`. -/
noncomputable def cobleSignOf (x : ℝ) : ℤˣ := if 0 < x then 1 else -1

theorem cobleSignOf_pos {x : ℝ} (h : 0 < x) : cobleSignOf x = 1 := if_pos h

theorem cobleSignOf_neg {x : ℝ} (h : x < 0) : cobleSignOf x = -1 := if_neg (not_lt.mpr h.le)

/-- The sign of the plane determinant is multiplicative. -/
theorem cobleOPlusSign_mul (g h : OrthogonalGroup cobleLattice) :
    cobleSignOf (LinearMap.det (coblePlaneA (g * h)))
      = cobleSignOf (LinearMap.det (coblePlaneA g))
        * cobleSignOf (LinearMap.det (coblePlaneA h)) := by
  set a := LinearMap.det (coblePlaneA g) with ha_def
  set b := LinearMap.det (coblePlaneA h) with hb_def
  set c := LinearMap.det (coblePlaneA (g * h)) with hc_def
  have htriple : 0 < a * b * c := coblePlaneA_det_triple_pos g h
  have ha : a ≠ 0 := coblePlaneA_det_ne_zero g
  have hb : b ≠ 0 := coblePlaneA_det_ne_zero h
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · have hab : (0 : ℝ) < a * b := mul_pos_of_neg_of_neg ha' hb'
    have hc' : 0 < c := by
      rcases mul_pos_iff.mp htriple with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd hab (not_lt.mpr h1.le)
    rw [cobleSignOf_pos hc', cobleSignOf_neg ha', cobleSignOf_neg hb']
    decide
  · have hab : a * b < 0 := mul_neg_of_neg_of_pos ha' hb'
    have hc' : c < 0 := by
      rcases mul_pos_iff.mp htriple with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd hab (not_lt.mpr h1.le)
      · exact h2
    rw [cobleSignOf_neg hc', cobleSignOf_neg ha', cobleSignOf_pos hb']
    decide
  · have hab : a * b < 0 := mul_neg_of_pos_of_neg ha' hb'
    have hc' : c < 0 := by
      rcases mul_pos_iff.mp htriple with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd hab (not_lt.mpr h1.le)
      · exact h2
    rw [cobleSignOf_neg hc', cobleSignOf_pos ha', cobleSignOf_neg hb']
    decide
  · have hab : (0 : ℝ) < a * b := mul_pos ha' hb'
    have hc' : 0 < c := by
      rcases mul_pos_iff.mp htriple with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd hab (not_lt.mpr h1.le)
    rw [cobleSignOf_pos hc', cobleSignOf_pos ha', cobleSignOf_pos hb']
    decide

/-- The plane basis `p₀ = e₀`, `p₁ = e₁ + e₂`, indexed by `Fin 2`. -/
noncomputable def coblePosPlaneVec (i : Fin 2) : Fin 11 → ℝ :=
  if i = 0 then cobleP1 else cobleP2

theorem coblePosPlaneVec_zero : coblePosPlaneVec 0 = cobleP1 := by
  rw [coblePosPlaneVec, if_pos rfl]

theorem coblePosPlaneVec_one : coblePosPlaneVec 1 = cobleP2 := by
  rw [coblePosPlaneVec, if_neg (by decide : ¬ (1 : Fin 2) = 0)]

theorem coblePosPlaneIncl_single_zero :
    coblePosPlaneIncl (Pi.single (0 : Fin 2) (1 : ℝ)) = cobleP1 := by
  rw [coblePosPlaneIncl_eq, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  simp

theorem coblePosPlaneIncl_single_one :
    coblePosPlaneIncl (Pi.single (1 : Fin 2) (1 : ℝ)) = cobleP2 := by
  rw [coblePosPlaneIncl_eq, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  simp

/-- The matrix `M(g) = (⟨g pᵢ, pⱼ⟩)ᵢⱼ` of #115. -/
noncomputable def coblePlaneGram (g : OrthogonalGroup cobleLattice) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => cobleRealForm (cobleRealAction g (coblePosPlaneVec i)) (coblePosPlaneVec j)

theorem coblePlaneGram_zero_zero (g : OrthogonalGroup cobleLattice) :
    coblePlaneGram g 0 0 = cobleRealForm (cobleRealAction g cobleP1) cobleP1 := by
  rw [coblePlaneGram, coblePosPlaneVec_zero]

theorem coblePlaneGram_zero_one (g : OrthogonalGroup cobleLattice) :
    coblePlaneGram g 0 1 = cobleRealForm (cobleRealAction g cobleP1) cobleP2 := by
  rw [coblePlaneGram, coblePosPlaneVec_zero, coblePosPlaneVec_one]

theorem coblePlaneGram_one_zero (g : OrthogonalGroup cobleLattice) :
    coblePlaneGram g 1 0 = cobleRealForm (cobleRealAction g cobleP2) cobleP1 := by
  rw [coblePlaneGram, coblePosPlaneVec_one, coblePosPlaneVec_zero]

theorem coblePlaneGram_one_one (g : OrthogonalGroup cobleLattice) :
    coblePlaneGram g 1 1 = cobleRealForm (cobleRealAction g cobleP2) cobleP2 := by
  rw [coblePlaneGram, coblePosPlaneVec_one]

theorem coblePlaneA_matrix_zero_zero (g : OrthogonalGroup cobleLattice) :
    LinearMap.toMatrix' (coblePlaneA g) 0 0
      = cobleRealForm (cobleRealAction g cobleP1) cobleP1 / 2 := by
  rw [LinearMap.toMatrix'_apply, coblePlaneA_apply, coblePosPlaneIncl_single_zero,
    coblePosPlaneCoord_zero, cobleRealForm_symm]

theorem coblePlaneA_matrix_zero_one (g : OrthogonalGroup cobleLattice) :
    LinearMap.toMatrix' (coblePlaneA g) 0 1
      = cobleRealForm (cobleRealAction g cobleP2) cobleP1 / 2 := by
  rw [LinearMap.toMatrix'_apply, coblePlaneA_apply, coblePosPlaneIncl_single_one,
    coblePosPlaneCoord_zero, cobleRealForm_symm]

theorem coblePlaneA_matrix_one_zero (g : OrthogonalGroup cobleLattice) :
    LinearMap.toMatrix' (coblePlaneA g) 1 0
      = cobleRealForm (cobleRealAction g cobleP1) cobleP2 / 4 := by
  rw [LinearMap.toMatrix'_apply, coblePlaneA_apply, coblePosPlaneIncl_single_zero,
    coblePosPlaneCoord_one, cobleRealForm_symm]

theorem coblePlaneA_matrix_one_one (g : OrthogonalGroup cobleLattice) :
    LinearMap.toMatrix' (coblePlaneA g) 1 1
      = cobleRealForm (cobleRealAction g cobleP2) cobleP2 / 4 := by
  rw [LinearMap.toMatrix'_apply, coblePlaneA_apply, coblePosPlaneIncl_single_one,
    coblePosPlaneCoord_one, cobleRealForm_symm]

/-- `det M(g) = 8 · det A(g)`: the character of #115 is the sign of `det A(g)`. -/
theorem coblePlaneGram_det (g : OrthogonalGroup cobleLattice) :
    (coblePlaneGram g).det = 8 * LinearMap.det (coblePlaneA g) := by
  rw [Matrix.det_fin_two, ← LinearMap.det_toMatrix', Matrix.det_fin_two,
    coblePlaneGram_zero_zero, coblePlaneGram_zero_one, coblePlaneGram_one_zero,
    coblePlaneGram_one_one, coblePlaneA_matrix_zero_zero, coblePlaneA_matrix_zero_one,
    coblePlaneA_matrix_one_zero, coblePlaneA_matrix_one_one]
  ring

/-- The sign character of the positive definite plane: the sign of the determinant of `A(g)`, the
matrix of `g` on the plane `P = ⟨e₀, e₁ + e₂⟩`. -/
noncomputable def cobleOPlusSign : OrthogonalGroup cobleLattice →* ℤˣ where
  toFun g := cobleSignOf (LinearMap.det (coblePlaneA g))
  map_one' := by
    rw [coblePlaneA_one, LinearMap.det_id]
    exact cobleSignOf_pos one_pos
  map_mul' := cobleOPlusSign_mul

/-- **`O⁺(T_Co)`**: the subgroup of `O(T_Co)` preserving the orientation of the positive definite
2-planes of `T_Co ⊗ ℝ`, i.e. the kernel of the real spinor norm. It is the kernel of the sign of
the determinant of `A(g)`, the matrix of `g` on the plane `P = ⟨e₀, e₁ + e₂⟩`. -/
noncomputable def cobleOPlus : Subgroup (OrthogonalGroup cobleLattice) :=
  MonoidHom.ker cobleOPlusSign

/-- **`O⁺(T_Co) = {g | 0 < det M(g)}`**, the characterization of #115: the orientation of the
positive definite plane, read off the determinant of `M(g) = (⟨g pᵢ, pⱼ⟩)ᵢⱼ`. -/
theorem cobleOPlus_mem_iff (g : OrthogonalGroup cobleLattice) :
    g ∈ cobleOPlus ↔ 0 < (coblePlaneGram g).det := by
  have key : ∀ x : ℝ, cobleSignOf x = 1 ↔ 0 < x := by
    intro x
    constructor
    · intro h
      by_contra hcon
      rw [cobleSignOf, if_neg hcon] at h
      exact absurd h (by decide : ¬ (-1 : ℤˣ) = 1)
    · intro h
      exact cobleSignOf_pos h
  have hmem : (g ∈ cobleOPlus) ↔ cobleSignOf (LinearMap.det (coblePlaneA g)) = 1 := by
    rw [cobleOPlus, MonoidHom.mem_ker]
    rfl
  rw [hmem, key, coblePlaneGram_det]
  constructor <;> intro h <;> linarith

/-- `O⁺(T_Co)` has index at most two. -/
theorem cobleOPlus_index_le_two : cobleOPlus.index ≤ 2 := by
  rw [cobleOPlus, Subgroup.index_ker]
  calc Nat.card ↥(MonoidHom.range cobleOPlusSign)
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- `O⁺(T_Co)` has finite index. -/
theorem cobleOPlus_finiteIndex : cobleOPlus.FiniteIndex where
  index_ne_zero := by
    rw [cobleOPlus, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

/-- `Γ_Co = O⁺(T_Co) ∩ ker ρ`. -/
noncomputable def cobleGammaCo : Subgroup (OrthogonalGroup cobleLattice) :=
  cobleOPlus ⊓ cobleKernel

/-- `Γ_Co` has finite index. -/
theorem cobleGammaCo_finiteIndex : cobleGammaCo.FiniteIndex where
  index_ne_zero := by
    rw [cobleGammaCo]
    exact Subgroup.index_inf_ne_zero cobleOPlus_finiteIndex.index_ne_zero
      cobleKernel_finiteIndex.index_ne_zero

/-- `Γ_Co` as a finite-index subgroup of `O(T_Co)`. -/
noncomputable def cobleGammaCoSubgroup : FiniteIndexSubgroup cobleLattice :=
  ⟨cobleGammaCo, cobleGammaCo_finiteIndex⟩



/-! ## `Γ_Co = O⁺(T_Co) ∩ ker ρ` and the cusp objects -/

/-- The cusp object `(T_Co, ker ρ)` of the cusp category. -/
noncomputable def cobleCuspKernel : CuspObject (R := ℤ) :=
  ⟨cobleLattice, cobleKernelSubgroup⟩

/-- The cusp object `(T_Co, Γ_Co)` of the cusp category. -/
noncomputable def cobleCuspGamma : CuspObject (R := ℤ) :=
  ⟨cobleLattice, cobleGammaCoSubgroup⟩

/-- The `ker ρ`-orbits of primitive isotropic lines: the 0-cusps counted for `ker ρ`. -/
noncomputable abbrev cobleCuspOrbitsKernelOne : Type :=
  CuspOrbits cobleLattice cobleKernelSubgroup 1

/-- The `ker ρ`-orbits of primitive isotropic planes: the 1-cusps counted for `ker ρ`. -/
noncomputable abbrev cobleCuspOrbitsKernelTwo : Type :=
  CuspOrbits cobleLattice cobleKernelSubgroup 2

/-- The `Γ_Co`-orbits of primitive isotropic lines: the 0-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaOne : Type :=
  CuspOrbits cobleLattice cobleGammaCoSubgroup 1

/-- The `Γ_Co`-orbits of primitive isotropic planes: the 1-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaTwo : Type :=
  CuspOrbits cobleLattice cobleGammaCoSubgroup 2

end LeanCategories.Lattices.Valued
