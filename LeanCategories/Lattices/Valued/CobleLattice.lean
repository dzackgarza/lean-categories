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
* the kernel of `det` (`cobleSpecialOrthogonal`, of index at most two) and, separately, the data of
  the orientation subgroup `O⁺(T_Co)` and `Γ_Co = O⁺(T_Co) ∩ ker ρ`;
* the cusp objects `(T_Co, ker ρ)` and `(T_Co, Γ_Co)` with their rank-1 and rank-2 orbit sets.

## `O⁺(T_Co)`

`O⁺(T_Co)` is the subgroup of `O(T_Co)` preserving the orientation of the positive-definite
2-planes of `T_Co ⊗ ℝ`, equivalently the kernel of the real spinor norm. It has index two and is
**not** the kernel of `det`. This development has no real quadratic space and no spinor norm, so
`O⁺` is not constructed here: `CobleOPlus` records the data a consumer supplies (a subgroup of
`O(T_Co)` of index at most two, intended to be `O⁺`), and `Γ_Co`, its cusp object and its orbit
sets are defined from that data. `cobleSpecialOrthogonal` is the concrete index-at-most-two
subgroup this file does construct — it is `SO(T_Co)`, the kernel of `det`, which is *not* `O⁺`.
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

/-- The data of the orientation subgroup `O⁺(T_Co)`: a subgroup of `O(T_Co)` of index at most two.
The intended instantiation is the subgroup preserving the orientation of the positive-definite
2-planes of `T_Co ⊗ ℝ`, i.e. the kernel of the real spinor norm.

The prescribed characterization is concrete: with `P = span(p₁, p₂)` the plane of coordinates
`p₁ = e₀` (norm `2`) and `p₂ = e₁ + e₂` (norm `4`) of `cobleHalfMatrix`, and
`M(g) = (⟨g pᵢ, pⱼ⟩)ᵢⱼ`, one has `O⁺(T_Co) = {g | 0 < det M(g)}`.

That this set is a subgroup is *not* formalized here, and the proof stops at its only nontrivial
step: multiplicativity of `sign det M`. Writing `g` in blocks over `T_Co ⊗ ℚ = P ⊥ P^⊥` as
`[[A, B], [C, D]]` gives `A(gh) = A(g)A(h) + B(g)C(h)`, hence
`sign det M(gh) = sign det M(g) · sign det M(h) · sign det(1 + A(g)⁻¹B(g)C(h)A(h)⁻¹)`, and the last
factor is `+1`, but only because `P` is positive definite and `P^⊥` is negative definite. There is
no exact algebraic identity to prove instead: numerically the ratio
`det M(gh) / (det M(g) det M(h) / det G_P)` ranges over `0.67 … 2.0`, so only the sign survives.

What the argument needs, and this development does not have, is (i) the negative definiteness of
`P^⊥` — an explicit definiteness certificate for the `E₈(−1)` block, for example a sum-of-squares
decomposition of the Cartan matrix — and (ii) a Loewner-order argument over an ordered field
(`mathlib` has `Matrix.PosSemidef` over `ℝ`, but there is no real form of `T_Co` here).

`cobleSpecialOrthogonal` below is the concrete index-two subgroup this file does construct; it is
`SO(T_Co)`, the kernel of `det`, and it is *not* `O⁺(T_Co)`. -/
structure CobleOPlus where
  /-- The intended `O⁺(T_Co)`. -/
  toSubgroup : Subgroup (OrthogonalGroup cobleLattice)
  /-- `[O(T_Co) : O⁺(T_Co)] ≤ 2`. -/
  index_le_two : toSubgroup.index ≤ 2
  /-- The subgroup has finite index. (`index ≤ 2` alone does not exclude Mathlib's `index = 0`
  convention for infinite index.) -/
  finiteIndex : toSubgroup.FiniteIndex

/-- `SO(T_Co)` has finite index. -/
theorem cobleSpecialOrthogonal_finiteIndex : cobleSpecialOrthogonal.FiniteIndex where
  index_ne_zero := by
    rw [cobleSpecialOrthogonal, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

/-- The concrete index-at-most-two subgroup of this file, `SO(T_Co)`, packaged as `CobleOPlus`
data. It satisfies the index bound that the data records; it is not `O⁺(T_Co)`. -/
noncomputable def cobleSpecialOrthogonalData : CobleOPlus where
  toSubgroup := cobleSpecialOrthogonal
  index_le_two := cobleSpecialOrthogonal_index_le_two
  finiteIndex := cobleSpecialOrthogonal_finiteIndex

/-! ## The stable group is the kernel of `ρ` -/

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

/-! ## `Γ_Co = O⁺(T_Co) ∩ ker ρ` -/

/-- `Γ_Co = O⁺(T_Co) ∩ ker ρ`, for supplied `O⁺` data. -/
noncomputable def cobleGammaCo (O : CobleOPlus) : Subgroup (OrthogonalGroup cobleLattice) :=
  O.toSubgroup ⊓ cobleKernel

/-- `Γ_Co` has finite index: the intersection of a subgroup of index at most two with `ker ρ`. -/
theorem cobleGammaCo_finiteIndex (O : CobleOPlus) : (cobleGammaCo O).FiniteIndex := by
  refine ⟨?_⟩
  rw [cobleGammaCo]
  exact Subgroup.index_inf_ne_zero O.finiteIndex.index_ne_zero
    cobleKernel_finiteIndex.index_ne_zero

/-- `Γ_Co` as a finite-index subgroup of `O(T_Co)`. -/
noncomputable def cobleGammaCoSubgroup (O : CobleOPlus) : FiniteIndexSubgroup cobleLattice :=
  ⟨cobleGammaCo O, cobleGammaCo_finiteIndex O⟩

/-! ## The cusp objects and their orbit sets -/

/-- The cusp object `(T_Co, ker ρ)` of the cusp category. -/
noncomputable def cobleCuspKernel : CuspObject (R := ℤ) :=
  ⟨cobleLattice, cobleKernelSubgroup⟩

/-- The cusp object `(T_Co, Γ_Co)` of the cusp category. -/
noncomputable def cobleCuspGamma (O : CobleOPlus) : CuspObject (R := ℤ) :=
  ⟨cobleLattice, cobleGammaCoSubgroup O⟩

/-- The `ker ρ`-orbits of primitive isotropic lines: the 0-cusps counted for `ker ρ`. -/
noncomputable abbrev cobleCuspOrbitsKernelOne : Type :=
  CuspOrbits cobleLattice cobleKernelSubgroup 1

/-- The `ker ρ`-orbits of primitive isotropic planes: the 1-cusps counted for `ker ρ`. -/
noncomputable abbrev cobleCuspOrbitsKernelTwo : Type :=
  CuspOrbits cobleLattice cobleKernelSubgroup 2

/-- The `Γ_Co`-orbits of primitive isotropic lines: the 0-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaOne (O : CobleOPlus) : Type :=
  CuspOrbits cobleLattice (cobleGammaCoSubgroup O) 1

/-- The `Γ_Co`-orbits of primitive isotropic planes: the 1-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaTwo (O : CobleOPlus) : Type :=
  CuspOrbits cobleLattice (cobleGammaCoSubgroup O) 2

end LeanCategories.Lattices.Valued
