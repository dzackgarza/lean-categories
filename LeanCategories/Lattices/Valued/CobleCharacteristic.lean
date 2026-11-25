/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CobleLattice
public import LeanCategories.Lattices.Valued.DiscriminantCharacteristic

/-!
# The characteristic class `[h/2]` of `T_Co` (#115)

The discriminant group of `T_Co = ⟨2⟩ ⊕ E(2)` is killed by `2`, so the general theorem of
`DiscriminantCharacteristic` applies: `x ↦ q(x) mod 1` is additive on `A_{T_Co}`, the class
pairing against it is unique, and every isometry of `T_Co` fixes it. This file exhibits that
class as `[h/2]`, `h = e₀` the generator of the `⟨2⟩` summand:

* `cobleHalfZ i` are the integer vectors `nᵢ = 2 · (G⁻¹ eᵢ)`, so that `nᵢ / 2` is the `i`-th vector
  of the dual basis (`cobleHalfZ_spec`, `cobleHalfZ_pairing`);
* `cobleHalfSpan i` is `nᵢ / 2` in the rational span, and `cobleDual_riesz` identifies it with the
  Riesz image of the `i`-th dual basis functional (`cobleBasis.dual i`);
* `cobleDiscriminant_two_smul` shows that `A_{T_Co}` is `2`-elementary, `cobleCharacteristic_exists`
  is the general existence theorem applied to it, `cobleHalfH_isCharacteristic` identifies `[h/2]`
  with the class the theorem produces, and `cobleHalfH_existsUnique` combines the two;
* `cobleGammaCo` is the stabilizer of `[h/2]` in `O(T_Co)`, and `cobleGammaCo_eq_top` is the
  research statement: `O(T_Co)` fixes `[h/2]`, so `Γ_Co = O(T_Co)`.

The half-dual vectors are computed from the construction's Gram matrix (`cobleGramMatrix`), not
typed against the lattice: `cobleHalfZ_spec` is proved entry by entry from the block structure.
-/

@[expose] public section


open Matrix
open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

attribute [local instance 10000] Submodule.Quotient.module
attribute [local instance 10000] TensorProduct.instModule
attribute [local instance 10000] Algebra.toModule

/-- Twice the `i`-th column of the inverse Gram matrix of `T_Co`, in coordinates: the integer
vectors `nᵢ` with `G · nᵢ = 2 · eᵢ`, so that `nᵢ / 2` is the `i`-th vector of the dual basis. -/
noncomputable def cobleHalfZMatrix : Matrix (Fin 11) (Fin 11) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -4, -5, -7, -10, -8, -6, -4, -2;
     0, 0, 0, -5, -8, -10, -15, -12, -9, -6, -3;
     0, 0, 0, -7, -10, -14, -20, -16, -12, -8, -4;
     0, 0, 0, -10, -15, -20, -30, -24, -18, -12, -6;
     0, 0, 0, -8, -12, -16, -24, -20, -15, -10, -5;
     0, 0, 0, -6, -9, -12, -18, -15, -12, -8, -4;
     0, 0, 0, -4, -6, -8, -12, -10, -8, -6, -3;
     0, 0, 0, -2, -3, -4, -6, -5, -4, -3, -2]

/-- Twice the `i`-th column of the inverse Gram matrix of `T_Co`. -/
noncomputable def cobleHalfZ (i : Fin 11) : Fin 11 → ℤ := cobleHalfZMatrix i

theorem cobleHalfZ_zero : cobleHalfZ 0 = cobleP1Z := by
  ext j
  fin_cases j <;> rfl

/-- The integral pairing of a vector with a standard basis vector is the corresponding entry of
`G · v`: the coordinate expression of `coble_pairing_coord` at a single basis vector. -/
theorem coble_pairing_coord_single (x : Fin 11 → ℤ) (j : Fin 11) :
    cobleLattice.obj.pairing (cobleCoordEquiv.symm x) (cobleBasis j) =
      (cobleGramMatrix *ᵥ x) j := by
  rw [← cobleCoordEquiv_symm_single j, coble_pairing_coord]
  rw [show (cobleGramMatrix *ᵥ x) j =
      ∑ i, cobleGramMatrix j i * x i from rfl]
  have hsymm : ∀ a b, cobleGramMatrix a b = cobleGramMatrix b a := fun a b => by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun cobleGramMatrix_isSymm b) a)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, hsymm b j]
    ring
  · intro b' _ hb'
    rw [Pi.single_eq_of_ne hb']
    ring
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem cobleHalfZ_spec_0 :
    cobleGramMatrix *ᵥ cobleHalfZ 0 = 2 • Pi.single (0 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_1 :
    cobleGramMatrix *ᵥ cobleHalfZ 1 = 2 • Pi.single (1 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_2 :
    cobleGramMatrix *ᵥ cobleHalfZ 2 = 2 • Pi.single (2 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_3 :
    cobleGramMatrix *ᵥ cobleHalfZ 3 = 2 • Pi.single (3 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_4 :
    cobleGramMatrix *ᵥ cobleHalfZ 4 = 2 • Pi.single (4 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_5 :
    cobleGramMatrix *ᵥ cobleHalfZ 5 = 2 • Pi.single (5 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_6 :
    cobleGramMatrix *ᵥ cobleHalfZ 6 = 2 • Pi.single (6 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_7 :
    cobleGramMatrix *ᵥ cobleHalfZ 7 = 2 • Pi.single (7 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_8 :
    cobleGramMatrix *ᵥ cobleHalfZ 8 = 2 • Pi.single (8 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_9 :
    cobleGramMatrix *ᵥ cobleHalfZ 9 = 2 • Pi.single (9 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem cobleHalfZ_spec_10 :
    cobleGramMatrix *ᵥ cobleHalfZ 10 = 2 • Pi.single (10 : Fin 11) 1 := by
  ext j
  fin_cases j <;>
    simp [cobleHalfZ, cobleHalfZMatrix, cobleGramMatrix, cobleBlockGramMatrix,
      rankOneGramMatrix, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- `nᵢ` is twice the `i`-th dual basis vector in coordinates: `G · nᵢ = 2 · eᵢ`. -/
theorem cobleHalfZ_spec (i : Fin 11) :
    cobleGramMatrix *ᵥ cobleHalfZ i = 2 • Pi.single i 1 := by
  fin_cases i
  · exact cobleHalfZ_spec_0
  · exact cobleHalfZ_spec_1
  · exact cobleHalfZ_spec_2
  · exact cobleHalfZ_spec_3
  · exact cobleHalfZ_spec_4
  · exact cobleHalfZ_spec_5
  · exact cobleHalfZ_spec_6
  · exact cobleHalfZ_spec_7
  · exact cobleHalfZ_spec_8
  · exact cobleHalfZ_spec_9
  · exact cobleHalfZ_spec_10

/-- The pairing of `nᵢ` with the `j`-th basis vector is `2` on the diagonal and `0` elsewhere. -/
theorem cobleHalfZ_pairing (i j : Fin 11) :
    cobleLattice.obj.pairing (cobleCoordEquiv.symm (cobleHalfZ i)) (cobleBasis j) =
      2 * (if i = j then 1 else 0) := by
  rw [coble_pairing_coord_single, cobleHalfZ_spec]
  by_cases h : i = j
  · subst h; simp
  · simp [h, eq_comm]

/-- The diagonal of the matrix of half-dual vectors is `1` at the `⟨2⟩` summand and even
elsewhere: the parity that makes `[h/2]` the characteristic class. -/
theorem cobleHalfZ_diag (i : Fin 11) :
    2 ∣ (cobleHalfZ i i - if i = 0 then 1 else 0) := by
  fin_cases i <;> simp [cobleHalfZ, cobleHalfZMatrix]

theorem cobleGramMatrix_comm (a b : Fin 11) :
    cobleGramMatrix a b = cobleGramMatrix b a := by
  have h := congrFun (congrFun cobleGramMatrix_isSymm b) a
  simpa [Matrix.transpose_apply] using h

theorem coble_pairing_halfZ (i : Fin 11) (x : ↥cobleLattice.obj.carrier) :
    cobleLattice.obj.pairing (cobleCoordEquiv.symm (cobleHalfZ i)) x =
      2 * cobleCoordEquiv x i := by
  have hinner : ∀ b, ∑ a, cobleHalfZ i a * cobleGramMatrix a b = 2 * (if i = b then 1 else 0) := by
    intro b
    rw [show (∑ a, cobleHalfZ i a * cobleGramMatrix a b) =
        (cobleGramMatrix *ᵥ cobleHalfZ i) b from by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [cobleGramMatrix_comm b a]
      ring]
    rw [cobleHalfZ_spec]
    simp only [Pi.smul_apply, Pi.single_apply]
    by_cases h : i = b
    · subst h; simp
    · simp [h, eq_comm]
  have hcomm : ∑ a, ∑ b, cobleHalfZ i a * cobleGramMatrix a b * cobleCoordEquiv x b =
      ∑ b, (∑ a, cobleHalfZ i a * cobleGramMatrix a b) * cobleCoordEquiv x b := by
    rw [Finset.sum_comm]
    simp [Finset.sum_mul]
  rw [show x = cobleCoordEquiv.symm (cobleCoordEquiv x) from
    (LinearEquiv.symm_apply_apply cobleCoordEquiv x).symm, coble_pairing_coord, hcomm]
  rw [Finset.sum_congr rfl fun b _ => by rw [hinner b]]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have h : i ≠ b := fun h' => hb h'.symm
    simp [h]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

noncomputable def cobleHalfSpan (i : Fin 11) : RationalSpan ℤ cobleLattice :=
  ((2 : FractionRing ℤ)⁻¹) • toRationalSpan ℤ cobleLattice
    (cobleCoordEquiv.symm (cobleHalfZ i))

theorem cobleHalfSpan_rationalizedForm (i : Fin 11) (x : ↥cobleLattice.obj.carrier) :
    rationalizedForm ℤ cobleLattice (cobleHalfSpan i) (toRationalSpan ℤ cobleLattice x) =
      algebraMap ℤ (FractionRing ℤ) (cobleCoordEquiv x i) := by
  have h0 : toRationalSpan ℤ cobleLattice x =
      (↑(toMetricDual ℤ cobleLattice x) : RationalSpan ℤ cobleLattice) := rfl
  rw [h0]
  have h1 : cobleHalfSpan i = ((2 : FractionRing ℤ)⁻¹) •
      (↑(toMetricDual ℤ cobleLattice (cobleCoordEquiv.symm (cobleHalfZ i))) :
        RationalSpan ℤ cobleLattice) := rfl
  rw [h1]
  simp only [LinearMap.map_smul, LinearMap.smul_apply]
  rw [rationalizedForm_toMetricDual, coble_pairing_halfZ, smul_eq_mul]
  have hcast : ∀ n : ℤ, algebraMap ℤ (FractionRing ℤ) n = (n : FractionRing ℤ) :=
    fun n => map_intCast (algebraMap ℤ (FractionRing ℤ)) n
  rw [hcast]
  push_cast
  rw [← mul_assoc, show ((2 : FractionRing ℤ)⁻¹ * 2) = 1 by norm_num, one_mul]
  exact (hcast (cobleCoordEquiv x i)).symm

theorem cobleHalfSpan_mem (i : Fin 11) : cobleHalfSpan i ∈ metricDual ℤ cobleLattice := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  rintro y ⟨x, rfl⟩
  exact Submodule.mem_one.mpr ⟨cobleCoordEquiv x i, (cobleHalfSpan_rationalizedForm i x).symm⟩

/-- The `i`-th vector of the dual basis, as an element of the metric dual `T_Co♯`. -/
noncomputable def cobleHalfDual (i : Fin 11) : metricDual ℤ cobleLattice :=
  ⟨cobleHalfSpan i, cobleHalfSpan_mem i⟩

theorem metricDualToValueDual_cobleHalfDual (i : Fin 11) :
    metricDualToValueDual ℤ cobleLattice (cobleHalfDual i) = cobleBasis.dualBasis i := by
  ext x
  apply FaithfulSMul.algebraMap_injective ℤ (FractionRing ℤ)
  rw [metricDualToValueDual_apply,
    show (↑(cobleHalfDual i) : RationalSpan ℤ cobleLattice) = cobleHalfSpan i from rfl,
    cobleHalfSpan_rationalizedForm, Module.Basis.dualBasis_apply]
  congr 1

/-- **The Riesz image of the `i`-th dual basis functional is `nᵢ / 2`.** -/
theorem cobleDual_riesz (i : Fin 11) :
    rieszToMetricDual ℤ cobleLattice coble_isFractionFieldPerfect (cobleBasis.dualBasis i) =
      cobleHalfDual i := by
  rw [← metricDualToValueDual_cobleHalfDual i]
  exact rieszToMetricDual_metricDualToValueDual ℤ cobleLattice coble_isFractionFieldPerfect _

/-- The class of the `i`-th dual basis functional in `A_{T_Co}` is the class of `nᵢ / 2`. -/
theorem metricDualToDiscriminant_cobleHalfDual (i : Fin 11) :
    metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual i) =
      cobleLattice.obj.defectProjection (cobleBasis.dualBasis i) := by
  rw [metricDualToDiscriminant, LinearMap.comp_apply, metricDualToValueDual_cobleHalfDual]


/-- The self-pairing of two half-dual vectors, in the rational span. -/
theorem rationalizedForm_cobleHalfDual (a b : Fin 11) :
    rationalizedForm ℤ cobleLattice (cobleHalfDual a) (cobleHalfDual b) =
      ((2 : FractionRing ℤ)⁻¹ * (2 : FractionRing ℤ)⁻¹) *
        algebraMap ℤ (FractionRing ℤ) (2 * cobleHalfZ b a) := by
  have ha : (↑(cobleHalfDual a) : RationalSpan ℤ cobleLattice) =
      ((2 : FractionRing ℤ)⁻¹) •
        (↑(toMetricDual ℤ cobleLattice (cobleCoordEquiv.symm (cobleHalfZ a))) :
          RationalSpan ℤ cobleLattice) := rfl
  have hb : (↑(cobleHalfDual b) : RationalSpan ℤ cobleLattice) =
      ((2 : FractionRing ℤ)⁻¹) •
        (↑(toMetricDual ℤ cobleLattice (cobleCoordEquiv.symm (cobleHalfZ b))) :
          RationalSpan ℤ cobleLattice) := rfl
  rw [ha, hb]
  simp only [LinearMap.map_smul, LinearMap.smul_apply]
  rw [rationalizedForm_toMetricDual, coble_pairing_halfZ]
  simp only [smul_eq_mul]
  rw [show cobleCoordEquiv (cobleCoordEquiv.symm (cobleHalfZ b)) a = cobleHalfZ b a from by
    rw [LinearEquiv.apply_symm_apply]]
  ring

theorem cobleHalfZ_zero_coord (i : Fin 11) :
    cobleHalfZ i 0 = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [cobleHalfZ, cobleHalfZMatrix]

/-- The `i`-th diagonal entry of the half-dual matrix is congruent to `1` at the `⟨2⟩` summand
and to `0` elsewhere. -/
theorem cobleHalfZ_diag' (i : Fin 11) :
    2 ∣ cobleHalfZ i i - cobleHalfZ i 0 := by
  fin_cases i <;> simp [cobleHalfZ, cobleHalfZMatrix]

/-- Two fraction-ring quotient classes whose difference is integral have the same class modulo
`1`. -/
theorem fractionValueProjection_congr_int {x y : FractionRing ℤ}
    (h : ∃ m : ℤ, x - y = algebraMap ℤ (FractionRing ℤ) m) :
    fractionValueProjection ℤ x = fractionValueProjection ℤ y := by
  obtain ⟨m, hm⟩ := h
  have h1 : fractionValueProjection ℤ (x - y) = 0 := by
    rw [hm, fractionValueProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, rfl⟩
  rw [map_sub] at h1
  exact sub_eq_zero.mp h1

/-- **`[h/2]`**: the class in `A_{T_Co}` of the half of the `⟨2⟩` generator `h = e₀`. -/
noncomputable def cobleHalfH : metricDual ℤ cobleLattice := cobleHalfDual 0

/-- The class `[h/2]` of the discriminant group of `T_Co`. -/
noncomputable def cobleHalfHCls : cobleLattice.obj.defect :=
  metricDualToDiscriminant ℤ cobleLattice cobleHalfH

/-- Twice the `i`-th dual basis functional is the adjoint of the half-dual vector. -/
theorem adjoint_cobleHalfZ (i : Fin 11) :
    cobleLattice.obj.adjoint (cobleCoordEquiv.symm (cobleHalfZ i)) =
      (2 : ℤ) • cobleBasis.dualBasis i := by
  ext y
  rw [LinearMap.smul_apply, smul_eq_mul, BilinModuleCat.bilinMap_apply, coble_pairing_halfZ,
    Module.Basis.dualBasis_apply, cobleCoordEquiv, Module.Basis.equivFun_apply]

/-- **The discriminant group of `T_Co` is killed by `2`** (`x + x = 0`). `T_Co = ⟨2⟩ ⊕ E(2)` with
`E` even unimodular, so twice any metric-dual vector is an integral vector. -/
theorem cobleDiscriminant_two_smul (x : cobleLattice.obj.defect) : x + x = 0 := by
  obtain ⟨f, rfl⟩ := cobleLattice.obj.defectProjection_surjective x
  obtain ⟨w, hw⟩ : ∃ w, cobleLattice.obj.adjoint w = (2 : ℤ) • f := by
    refine ⟨∑ i, (cobleBasis.dualBasis).repr f i • cobleCoordEquiv.symm (cobleHalfZ i), ?_⟩
    rw [map_sum]
    conv_rhs => rw [show f = ∑ i, (cobleBasis.dualBasis.repr f) i • cobleBasis.dualBasis i from
        (Module.Basis.sum_repr _ f).symm]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, adjoint_cobleHalfZ, smul_comm]
  rw [show cobleLattice.obj.defectProjection f = Submodule.Quotient.mk f from rfl,
    ← two_smul ℤ, ← Submodule.Quotient.mk_smul, ← hw, Submodule.Quotient.mk_eq_zero]
  exact ⟨w, rfl⟩


/-- The classes of the dual basis functionals: a generating set of the discriminant group of
`T_Co`, which is the image of a basis of the value dual. -/
noncomputable def cobleClassGen (i : Fin 11) : cobleLattice.obj.defect :=
  cobleLattice.obj.defectProjection (cobleBasis.dualBasis i)

theorem cobleClassGen_eq (i : Fin 11) :
    cobleClassGen i = metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual i) :=
  (metricDualToDiscriminant_cobleHalfDual i).symm

/-- The generator classes span the discriminant group of `T_Co`. -/
theorem addSubgroup_closure_cobleClassGen :
    AddSubgroup.closure (Set.range cobleClassGen) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, rfl⟩ := cobleLattice.obj.defectProjection_surjective x
  have hf : cobleLattice.obj.defectProjection f =
      ∑ i, (cobleBasis.dualBasis.repr f) i • cobleClassGen i := by
    conv_lhs => rw [show cobleLattice.obj.defectProjection f = Submodule.Quotient.mk f from rfl]
    conv_lhs => rw [show f = ∑ i, (cobleBasis.dualBasis.repr f) i • cobleBasis.dualBasis i from
        (Module.Basis.sum_repr _ f).symm]
    rw [show Submodule.Quotient.mk
        (∑ i, (cobleBasis.dualBasis.repr f) i • cobleBasis.dualBasis i) =
      (Submodule.mkQ (LinearMap.range cobleLattice.obj.adjoint))
        (∑ i, (cobleBasis.dualBasis.repr f) i • cobleBasis.dualBasis i) from rfl, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  rw [hf]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _
    (AddSubgroup.subset_closure (show cobleClassGen i ∈ Set.range cobleClassGen from ⟨i, rfl⟩)) _

/-- The discriminant pairing of two metric-dual classes is the projection of their rationalized
pairing. -/
theorem cobleDiscriminantBilinMap_pairing (x y : metricDual ℤ cobleLattice) :
    discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect
        (metricDualToDiscriminant ℤ cobleLattice x)
        (metricDualToDiscriminant ℤ cobleLattice y) =
      fractionValueProjection ℤ (rationalizedForm ℤ cobleLattice x y) :=
  discriminant_pairing_metricDualToDiscriminant (R := ℤ) coble_isFractionFieldPerfect x y

/-- **`[h/2]` is the characteristic class of the discriminant form of `T_Co`.** -/
theorem cobleHalfH_isCharacteristic :
    IsCharacteristicClassOf
      (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect coble_isEven)
      (discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect) cobleHalfHCls := by
  intro x
  have hgen : ∀ i : Fin 11,
      discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect cobleHalfHCls
          (cobleClassGen i) =
        quadraticModOne
          (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect
            coble_isEven) (cobleClassGen i) := by
    intro i
    obtain ⟨m, hm⟩ := cobleHalfZ_diag' i
    have harg : (2 : ℤ) * cobleHalfZ i 0 - 2 * cobleHalfZ i i = -(4 * m) := by
      linear_combination (-2) * hm
    have hkey : (algebraMap ℤ (FractionRing ℤ) (2 * cobleHalfZ i 0) -
        algebraMap ℤ (FractionRing ℤ) (2 * cobleHalfZ i i)) =
        algebraMap ℤ (FractionRing ℤ) (-(4 * m)) := by
      rw [← map_sub, harg]
    have hconv : algebraMap ℤ (FractionRing ℤ) (-(4 * m)) =
        (-4) * algebraMap ℤ (FractionRing ℤ) m := by
      rw [show -(4 * m) = (-4) * m by ring, map_mul]
      norm_num
    have hcoef : ((2 : FractionRing ℤ)⁻¹ * (2 : FractionRing ℤ)⁻¹ * (-4)) = -1 := by norm_num
    have hzero : (2 : FractionRing ℤ)⁻¹ * (2 : FractionRing ℤ)⁻¹ *
          algebraMap ℤ (FractionRing ℤ) (2 * cobleHalfZ i 0) -
        (2 : FractionRing ℤ)⁻¹ * (2 : FractionRing ℤ)⁻¹ *
          algebraMap ℤ (FractionRing ℤ) (2 * cobleHalfZ i i) =
        algebraMap ℤ (FractionRing ℤ) (-m) := by
      rw [← mul_sub, hkey, hconv,
        show (2 : FractionRing ℤ)⁻¹ * (2 : FractionRing ℤ)⁻¹ *
            ((-4) * algebraMap ℤ (FractionRing ℤ) m) =
          ((2 : FractionRing ℤ)⁻¹ * (2 : FractionRing ℤ)⁻¹ * (-4)) *
            algebraMap ℤ (FractionRing ℤ) m from by ring,
        hcoef]
      rw [neg_one_mul, ← map_neg]
    have hb0 : discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect
        (metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual 0))
        (metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual i)) =
        fractionValueProjection ℤ
          (rationalizedForm ℤ cobleLattice (cobleHalfDual 0) (cobleHalfDual i)) :=
      cobleDiscriminantBilinMap_pairing _ _
    have hq : quadraticModOne
        (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect coble_isEven)
        (metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual i)) =
        fractionValueProjection ℤ
          (rationalizedForm ℤ cobleLattice (cobleHalfDual i) (cobleHalfDual i)) := by
      change doubleFractionModOne ℤ
        (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect coble_isEven
          (metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual i))) = _
      rw [evenDiscriminantQuadraticMap_metricDualToDiscriminant,
        doubleFractionModOne_doubleFractionValueProjection]
    rw [show cobleHalfHCls = metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual 0) from rfl,
      show cobleClassGen i = metricDualToDiscriminant ℤ cobleLattice (cobleHalfDual i) from
        cobleClassGen_eq i, hb0, hq, rationalizedForm_cobleHalfDual, rationalizedForm_cobleHalfDual]
    exact fractionValueProjection_congr_int ⟨-m, hzero⟩
  have hsub : ∀ x y : cobleLattice.obj.defect,
      discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect cobleHalfHCls (x + y) -
        quadraticModOne
          (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect
            coble_isEven) (x + y) =
      (discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect cobleHalfHCls x -
        quadraticModOne
          (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect
            coble_isEven) x) +
      (discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect cobleHalfHCls y -
        quadraticModOne
          (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect
            coble_isEven) y) := by
    intro x y
    rw [map_add,
      quadraticModOne_add _ _
        (fun a b => evenDiscriminantQuadraticMap_polar cobleLattice
          coble_isFractionFieldPerfect coble_isEven a b)
        (fun z => cobleDiscriminant_two_smul z)]
    abel
  have h00 : discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect cobleHalfHCls 0 -
      quadraticModOne
        (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect
          coble_isEven) 0 = 0 := by
    simp [quadraticModOne]
  let K : AddSubgroup cobleLattice.obj.defect :=
    { carrier := {z | discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect
          cobleHalfHCls z - quadraticModOne
            (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect
              coble_isEven) z = 0}
      zero_mem' := h00
      add_mem' := by
        intro a b ha hb
        rw [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hsub, ha, hb, add_zero]
      neg_mem' := by
        intro a ha
        rw [Set.mem_ofPred_eq] at ha ⊢
        have h := hsub a (-a)
        rw [add_neg_cancel, h00, ha, zero_add] at h
        exact h.symm }
  have htop : K = ⊤ := by
    rw [eq_top_iff, ← addSubgroup_closure_cobleClassGen, AddSubgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact sub_eq_zero.mpr (hgen i)
  have hx : x ∈ K := by
    rw [htop]
    exact AddSubgroup.mem_top x
  exact sub_eq_zero.mp hx

/-- **`T_Co` has a characteristic class**: existence, from the general theorem
`exists_isCharacteristicClassOf'` applied to the `2`-elementary discriminant form of `T_Co`. -/
theorem cobleCharacteristic_exists (h2 : ∀ x : cobleLattice.obj.defect, x + x = 0) :
    ∃ w : cobleLattice.obj.defect,
      IsCharacteristicClassOf
        (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect coble_isEven)
        (discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect) w :=
  exists_isCharacteristicClassOf' coble_isFractionFieldPerfect coble_isEven h2

/-- **The characteristic class of `T_Co` is `[h/2]`**: any class satisfying the characteristic
property is `[h/2]`, by uniqueness (`isCharacteristicClassOf_unique'`) applied to
`cobleHalfH_isCharacteristic`. -/
theorem cobleCharacteristic_eq_halfH {w : cobleLattice.obj.defect}
    (hw : IsCharacteristicClassOf
      (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect coble_isEven)
      (discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect) w) :
    w = cobleHalfHCls :=
  isCharacteristicClassOf_unique' coble_isFractionFieldPerfect coble_isEven hw
    cobleHalfH_isCharacteristic

/-- **`T_Co` has exactly one characteristic class, and it is `[h/2]`.**

Existence is the general existence theorem `exists_isCharacteristicClassOf'`, via
`cobleCharacteristic_exists`; uniqueness is `isCharacteristicClassOf_unique'`; and
`cobleHalfH_isCharacteristic` identifies the class with `[h/2]`. -/
theorem cobleHalfH_existsUnique :
    ∃! w : cobleLattice.obj.defect,
      IsCharacteristicClassOf
        (evenDiscriminantQuadraticMap cobleLattice coble_isFractionFieldPerfect coble_isEven)
        (discriminantBilinMap ℤ cobleLattice coble_isFractionFieldPerfect) w := by
  obtain ⟨w₀, hw₀⟩ := cobleCharacteristic_exists cobleDiscriminant_two_smul
  rw [cobleCharacteristic_eq_halfH hw₀] at hw₀
  exact ⟨cobleHalfHCls, hw₀, fun w hw =>
    isCharacteristicClassOf_unique' coble_isFractionFieldPerfect coble_isEven hw hw₀⟩

/-- **Every isometry of `T_Co` fixes `[h/2]`**: the characteristic-class invariance theorem of
`DiscriminantCharacteristic` applied to `T_Co`. -/
theorem cobleActOnDefect_halfH (g : OrthogonalGroup cobleLattice) :
    OrthogonalGroup.actOnDefect g cobleHalfHCls = cobleHalfHCls :=
  actOnDefect_eq_of_isCharacteristicClassOf coble_isFractionFieldPerfect coble_isEven
    cobleHalfH_isCharacteristic g

/-- **`Γ_Co`**: the stabilizer in `O(T_Co)` of the class `[h/2]` of the discriminant group. -/
noncomputable def cobleGammaCo : Subgroup (OrthogonalGroup cobleLattice) :=
  MulAction.stabilizer (OrthogonalGroup cobleLattice) cobleHalfHCls

/-- **`Γ_Co = O(T_Co)`**: since `[h/2]` is the characteristic class of the `2`-elementary
discriminant form of `T_Co`, every isometry fixes it and the stabilizer is all of `O(T_Co)`. -/
theorem cobleGammaCo_eq_top : cobleGammaCo = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [cobleGammaCo, MulAction.mem_stabilizer_iff]
  exact cobleActOnDefect_halfH g

theorem cobleGammaCo_finiteIndex : cobleGammaCo.FiniteIndex where
  index_ne_zero := by
    rw [cobleGammaCo_eq_top, Subgroup.index_top]
    exact one_ne_zero

/-- `Γ_Co` as a finite-index subgroup of `O(T_Co)`. -/
noncomputable def cobleGammaCoSubgroup : FiniteIndexSubgroup cobleLattice :=
  ⟨cobleGammaCo, cobleGammaCo_finiteIndex⟩

/-- **`Õ(T_Co) = ker ρ`**: the isometries acting trivially on the discriminant form. -/
noncomputable abbrev cobleOTilde : Subgroup (OrthogonalGroup cobleLattice) := cobleKernel

/-- `Õ(T_Co)` as a finite-index subgroup of `O(T_Co)`. -/
noncomputable abbrev cobleOTildeSubgroup : FiniteIndexSubgroup cobleLattice := cobleKernelSubgroup

/-- The cusp object `(T_Co, Γ_Co) = (T_Co, O(T_Co))`. -/
noncomputable def cobleCuspGamma : CuspObject (R := ℤ) :=
  ⟨cobleLattice, cobleGammaCoSubgroup⟩

/-- The `O(T_Co)`-orbits of primitive isotropic lines: the 0-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaOne : Type :=
  CuspOrbits cobleLattice cobleGammaCoSubgroup 1

/-- The `O(T_Co)`-orbits of primitive isotropic planes: the 1-cusps of `F_Co`. -/
noncomputable abbrev cobleCuspOrbitsGammaTwo : Type :=
  CuspOrbits cobleLattice cobleGammaCoSubgroup 2

end LeanCategories.Lattices.Valued
