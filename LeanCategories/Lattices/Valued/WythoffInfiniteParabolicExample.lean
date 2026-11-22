/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.WythoffSemifan
public import Mathlib.Data.Matrix.Basic

/-!
# An infinite-`W_J` consumer of the Wythoff semifan

This file instantiates `LeanCategories.Lattices.Valued.aetWythoffSemifan` on a rank-three datum
in which the standard parabolic `W_J` is **infinite**, so the semifan is genuinely not a fan: the
maximal cone `L` is an infinite union of chambers, it is not a chamber, and its stabilizer in `W`
is infinite.

Datum (Alexeev–Engel–Thompson, arXiv:1903.09742v3, §4D, in their sign convention: `B` symmetric,
simple roots with `r_k · r_k < 0` and `r_k · r_k' ≥ 0` for `k ≠ k'`):

* simple roots `α_0, α_1, α_2` with Gram matrix `Bmat = !![-2,3,0; 3,-2,0; 0,0,-2]`:
  `r_k² = -2 < 0`, off-diagonal entries `3, 0, 0 ≥ 0`, `det = 10 ≠ 0`, signature `(1,2)`;
* `J = {0,1}` is inactive and `I = {2}` active;
* `W_J = ⟨s_0, s_1⟩` is infinite: `s_0 s_1` is hyperbolic (`trace 7` on its invariant plane) and
  its powers have `(0,0)`-entry at least `8`;
* the active functional `φ_2 = B(α_2, -)` is `W_J`-invariant (`α_2 ⟂ α_0, α_1`), which discharges
  the hypothesis `hL` of the forward half of Proposition 4.17(1) for this datum.

Nothing here is a finiteness assumption: the general theorems of `WythoffSemifan` are applied with
`W_J` infinite, which is exactly the case that the finite-`W_J` specialization of Remark 4.19
(where the semifan becomes a rational polyhedral fan) excludes.

## Main results

* `wJ_infinite : ¬ Finite WJ`; `phi_two_invariant`, `hL`.
* `genChamberFace_isFace` — `L ∩ ker φ_2` is a face of `L` (Proposition 4.17(4) instance).
* `L_ne_chamber` — `L` is not a chamber (an inactive translate of a chamber point leaves `K`).
* `stab_infinite` — the stabilizer of `L` in `W` is infinite (AET p. 27).
* `orbit_finiteness`, `equivariance`, `faceClosure` — the general theorems, instantiated.

## LC-09 search record

Corpus queries `content:semifan`, `content:"generalized chamber" content:reflection`,
`content:"parabolic subgroup" content:reflection content:chamber`, `content:Wythoff`,
`content:"relevant face"`: no formalization of a generalized Coxeter semifan. The repository's
`Semifan.lean` / `SemifanArrangement.lean` are Looijenga's §6 conical-locus semifan (a different
object). Mathlib's `RootPairing` cannot host this datum: with `[Finite ι]` the Weyl group embeds in
`Equiv.Perm ι`, so an infinite standard parabolic with finitely many simple roots is outside it.
Hence the explicit matrix model.

## References

* V. Alexeev, P. Engel, A. Thompson, *Stable pair compactification of moduli of K3 surfaces of
  degree 2*, arXiv:1903.09742v3, Definition 4.16, Proposition 4.17, Remark 4.19.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued.WythoffInfinite

open Matrix

/-- The ambient space `ℝ³`. -/
abbrev M : Type := Fin 3 → ℝ

/-- The Gram matrix of the simple roots, in AET's sign convention. -/
def Bmat : Matrix (Fin 3) (Fin 3) ℝ := !![-2, 3, 0; 3, -2, 0; 0, 0, -2]

/-- The simple-root functionals `φ_k = B(α_k, -)`. -/
def phi (i : Fin 3) : M →ₗ[ℝ] ℝ where
  toFun x := (Bmat *ᵥ x) i
  map_add' x y := by simp [Matrix.mulVec_add]
  map_smul' c x := by simp [Matrix.mulVec_smul]

/-! ### AET's numerical hypotheses on the datum -/

theorem Bmat_self (i : Fin 3) : Bmat i i = -2 := by
  fin_cases i <;> simp [Bmat]

theorem Bmat_pair {i j : Fin 3} (h : i ≠ j) : 0 ≤ Bmat i j := by
  revert h; fin_cases i <;> fin_cases j <;> simp [Bmat] <;> norm_num

theorem Bmat_det : Bmat.det = 10 := by
  rw [Matrix.det_fin_three]; simp [Bmat]; norm_num

/-! ### The simple reflections -/

def s0Mat : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 3, 0; 0, 1, 0; 0, 0, 1]
def s1Mat : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 3, -1, 0; 0, 0, 1]
def s2Mat : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

theorem s0Mat_sq : s0Mat * s0Mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [s0Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s1Mat_sq : s1Mat * s1Mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [s1Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s2Mat_sq : s2Mat * s2Mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [s2Mat, Matrix.mul_apply, Fin.sum_univ_three]

/-- The linear equivalence of `ℝ³` given by an involutive matrix. -/
def matEquiv (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * A = 1) : M ≃ₗ[ℝ] M :=
  LinearEquiv.ofLinearMap (Matrix.mulVecLin A) (Matrix.mulVecLin A)
    (by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
      rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
      rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec])

theorem matEquiv_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * A = 1) (x : M) :
    matEquiv A hA x = A *ᵥ x := by
  simp [matEquiv, Matrix.mulVecLin_apply]

/-- The reflection in the first simple root. -/
def s0 : M ≃ₗ[ℝ] M := matEquiv s0Mat s0Mat_sq

/-- The reflection in the second simple root. -/
def s1 : M ≃ₗ[ℝ] M := matEquiv s1Mat s1Mat_sq

/-- The reflection in the third (active) simple root. -/
def s2 : M ≃ₗ[ℝ] M := matEquiv s2Mat s2Mat_sq

theorem s0_apply (x : M) : s0 x = s0Mat *ᵥ x := matEquiv_apply _ _ x
theorem s1_apply (x : M) : s1 x = s1Mat *ᵥ x := matEquiv_apply _ _ x
theorem s2_apply (x : M) : s2 x = s2Mat *ᵥ x := matEquiv_apply _ _ x

/-! ### The chamber data of Definition 4.16 -/

/-- The inactive simple roots. -/
def J : Finset (Fin 3) := {0, 1}

/-- The standard parabolic `W_J = ⟨s_0, s_1⟩`. -/
def WJ : Subgroup (M ≃ₗ[ℝ] M) := Subgroup.closure ({s0, s1} : Set (M ≃ₗ[ℝ] M))

/-- The full reflection group `W = ⟨s_0, s_1, s_2⟩`. -/
def W : Subgroup (M ≃ₗ[ℝ] M) := Subgroup.closure ({s0, s1, s2} : Set (M ≃ₗ[ℝ] M))

theorem WJ_le_W : WJ ≤ W :=
  Subgroup.closure_mono (by rintro _ (rfl | rfl) <;> simp [W])

theorem s0_mem_WJ : s0 ∈ WJ := Subgroup.subset_closure (by simp [WJ])
theorem s1_mem_WJ : s1 ∈ WJ := Subgroup.subset_closure (by simp [WJ])

/-- A point of the fundamental chamber. -/
def k₀ : M := ![0, 0, -1]

theorem k₀_mem : k₀ ∈ aetChamber phi := by
  intro i
  fin_cases i <;> simp [phi, Bmat, k₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem chamber_nonempty : (aetChamber phi).Nonempty := ⟨k₀, k₀_mem⟩

/-- A point of the chamber moved out of the chamber by the inactive reflection `s_0`. -/
def y₀ : M := ![1, 1, -1]

theorem y₀_mem : y₀ ∈ aetChamber phi := by
  intro i
  fin_cases i <;>
    simp [phi, Bmat, y₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem phi_zero_s0_y₀ : phi 0 (s0 y₀) = -1 := by
  rw [s0_apply]
  simp [phi, Bmat, s0Mat, y₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  norm_num

theorem s0_y₀_not_mem : s0 y₀ ∉ aetChamber phi := by
  intro h
  have h0 := h 0
  rw [phi_zero_s0_y₀] at h0
  linarith

/-- **`L` is not a chamber**: the chamber point `y₀` is moved out of `K` by `s_0 ∈ W_J`, so the
generalized chamber is a proper union of chambers. -/
theorem L_ne_chamber : ¬ (aetGeneralizedChamber phi WJ ⊆ aetChamber phi) := by
  intro h
  have hmem : s0 y₀ ∈ aetGeneralizedChamber phi WJ :=
    mem_aetGeneralizedChamber.mpr ⟨⟨s0, s0_mem_WJ⟩, y₀, y₀_mem, rfl⟩
  exact s0_y₀_not_mem (h hmem)

/-! ### The active functional is `W_J`-invariant -/

theorem phi_two_s0 (x : M) : phi 2 (s0 x) = phi 2 x := by
  rw [s0_apply]
  show (Bmat *ᵥ (s0Mat *ᵥ x)) 2 = (Bmat *ᵥ x) 2
  simp [Bmat, s0Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem phi_two_s1 (x : M) : phi 2 (s1 x) = phi 2 x := by
  rw [s1_apply]
  show (Bmat *ᵥ (s1Mat *ᵥ x)) 2 = (Bmat *ᵥ x) 2
  simp [Bmat, s1Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The elements of `W` fixing the active functional `φ_2`. -/
def fixingPhi2 : Subgroup (M ≃ₗ[ℝ] M) where
  carrier := {e | ∀ x : M, phi 2 (e x) = phi 2 x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    show phi 2 (a (b x)) = phi 2 x
    rw [ha (b x), hb x]
  inv_mem' := by
    intro a ha x
    have := ha (a⁻¹ x)
    simpa using this.symm

/-- The active functional is invariant under the whole parabolic `W_J`. -/
theorem phi_two_invariant (e : WJ) (x : M) : phi 2 ((e : M ≃ₗ[ℝ] M) x) = phi 2 x :=
  (Subgroup.closure_le fixingPhi2).mpr (by
    rintro _ (rfl | rfl)
    · exact phi_two_s0
    · exact phi_two_s1) e.property x

/-- **The forward half of Proposition 4.17(1) for this datum.** -/
theorem hL : ∀ i, i ∉ J → ∀ g : WJ, ∀ y : M, y ∈ aetChamber phi → 0 ≤ phi i ((g : M ≃ₗ[ℝ] M) y) := by
  intro i hi g y hy
  have hi2 : i = 2 := by
    revert hi; fin_cases i <;> simp [J]
  subst hi2
  rw [phi_two_invariant]
  exact hy 2

/-- **The relevant-face statement for this datum**: `L ∩ ker φ_2` is a face of `L`. -/
theorem genChamberFace_isFace :
    IsConeFace (aetGeneralizedChamberFace phi WJ {2}) (aetGeneralizedChamber phi WJ) :=
  aetGeneralizedChamberFace_isConeFace phi J WJ {2} hL (by intro i hi; simp at hi; subst hi; simp [J])

/-! ### `W_J` is infinite -/

/-- The hyperbolic element `g = s_0 s_1` of `W_J`. -/
def g : M ≃ₗ[ℝ] M := s0 * s1

/-- Its matrix. -/
def gMat : Matrix (Fin 3) (Fin 3) ℝ := s0Mat * s1Mat

theorem g_apply (x : M) : g x = gMat *ᵥ x := by
  rw [g, LinearEquiv.mul_apply, s0_apply, s1_apply, gMat, Matrix.mulVec_mulVec]

theorem gMat_apply_zero (N : Matrix (Fin 3) (Fin 3) ℝ) :
    (gMat * N) 0 0 = 8 * N 0 0 - 3 * N 1 0 := by
  simp [gMat, s0Mat, s1Mat, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem gMat_apply_one (N : Matrix (Fin 3) (Fin 3) ℝ) :
    (gMat * N) 1 0 = 3 * N 0 0 - N 1 0 := by
  simp [gMat, s0Mat, s1Mat, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem g_pow_apply (n : ℕ) (x : M) : (g ^ n) x = (gMat ^ n) *ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, g_apply, Matrix.mulVec_mulVec, ← pow_succ']

/-- The `(0,0)`-entry of the powers of `gMat` grows: it is at least `8` from the first power on,
and the `(1,0)`-entry stays bounded by half of it. -/
theorem gMat_pow_bounds (n : ℕ) :
    0 < (gMat ^ n) 0 0 ∧ 2 * (gMat ^ n) 1 0 ≤ (gMat ^ n) 0 0 ∧
      (n = 0 ∨ 8 ≤ (gMat ^ n) 0 0) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [pow_succ', gMat_apply_zero, gMat_apply_one]
    have hpos : (0 : ℝ) < (gMat ^ n) 0 0 := h1
    have hle : 2 * (gMat ^ n) 1 0 ≤ (gMat ^ n) 0 0 := h2
    have h8 : n = 0 ∨ 8 ≤ (gMat ^ n) 0 0 := h3
    refine ⟨by linarith, by linarith, Or.inr ?_⟩
    rcases h8 with rfl | h8
    · norm_num
    · linarith

theorem g_pow_ne_one {n : ℕ} (hn : 1 ≤ n) : g ^ n ≠ 1 := by
  intro h
  have h00 : (gMat ^ n) 0 0 = 1 := by
    have h1 : ((g ^ n) (Pi.single 0 (1 : ℝ))) 0 = ((1 : M ≃ₗ[ℝ] M) (Pi.single 0 (1 : ℝ))) 0 := by
      rw [h]
    rw [g_pow_apply] at h1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using h1
  obtain ⟨-, -, h8⟩ := gMat_pow_bounds n
  have : n ≠ 0 := by omega
  rcases h8 with h0 | h8
  · exact absurd h0 this
  · linarith

/-- **The standard parabolic `W_J` is infinite**: the powers of the hyperbolic `g = s_0 s_1` are
pairwise distinct elements of `W_J`. -/
theorem wJ_infinite : ¬ Finite WJ := by
  have hmem : ∀ n : ℕ, g ^ n ∈ WJ :=
    fun n => Subgroup.pow_mem WJ (Subgroup.mul_mem WJ s0_mem_WJ s1_mem_WJ) n
  have hinj : Function.Injective (fun n : ℕ => (⟨g ^ n, hmem n⟩ : WJ)) := by
    intro m n hmn
    have h : g ^ m = g ^ n := congrArg Subtype.val hmn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exfalso
      have hd : g ^ (n - m) = 1 := by
        have hstep : g ^ m * g ^ (n - m) = g ^ m * 1 := by
          rw [mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le, h]
        exact mul_left_cancel hstep
      exact g_pow_ne_one (by omega) hd
    · exact heq
    · exfalso
      have hd : g ^ (m - n) = 1 := by
        have hstep : g ^ n * g ^ (m - n) = g ^ n * 1 := by
          rw [mul_one, ← pow_add, Nat.add_sub_cancel' hgt.le, ← h]
        exact mul_left_cancel hstep
      exact g_pow_ne_one (by omega) hd
  intro hfin
  exact Set.infinite_range_of_injective hinj
    (Set.finite_univ.subset (Set.subset_univ (Set.range _)))

/-- **The stabilizer of `L` in `W` is infinite** (AET, p. 27: "`L` has ... an infinite stabilizer
group"). -/
theorem stab_infinite : Set.Infinite {e : M ≃ₗ[ℝ] M | e ∈ W ∧ e '' aetGeneralizedChamber phi WJ
    = aetGeneralizedChamber phi WJ} := by
  set L := aetGeneralizedChamber phi WJ with hLdef
  have hsub : (WJ : Set (M ≃ₗ[ℝ] M)) ⊆
      {e : M ≃ₗ[ℝ] M | e ∈ W ∧ e '' L = L} := by
    intro e he
    refine ⟨WJ_le_W he, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact aetGeneralizedChamber_smul_mem phi WJ hy ⟨e, he⟩
    · intro hx
      refine ⟨((⟨e, he⟩ : WJ)⁻¹ : M ≃ₗ[ℝ] M) x, ?_, ?_⟩
      · have := aetGeneralizedChamber_smul_mem phi WJ hx (⟨e, he⟩ : WJ)⁻¹
        simpa using this
      · simp
  exact Set.Infinite.mono hsub (fun hfin => wJ_infinite hfin.to_subtype)

/-! ### The general theorems, instantiated -/

theorem orbit_finiteness :
    ∃ T : Set (Set M), T.Finite ∧
      ∀ D ∈ aetWythoffSemifan phi J W WJ, ∃ E ∈ T, ∃ e ∈ W, D = e '' E := by
  obtain ⟨T, hT, -, hmem⟩ := aetWythoffSemifan_orbits_finite phi J W WJ
  exact ⟨T, hT, hmem⟩

theorem equivariance (e : M ≃ₗ[ℝ] M) (he : e ∈ W) :
    (fun D => e '' D) '' aetWythoffSemifan phi J W WJ = aetWythoffSemifan phi J W WJ :=
  aetWythoffSemifan_equivariant phi J W WJ e he

/-- **Face closure** for this datum, from the general theorem. -/
theorem faceClosure :
    (∀ (e : M ≃ₗ[ℝ] M), e ∈ W → ∀ (V U : Finset (Fin 3)), AET.IsRelevant J V →
        IsConeFace (e '' aetChamberFace phi (V ∪ U)) (e '' aetChamberFace phi V) ∧
          (e '' aetChamberFace phi (V ∪ U)) ∈ aetWythoffSemifan phi J W WJ) ∧
      (∀ (e : M ≃ₗ[ℝ] M), e ∈ W → ∀ V : Finset (Fin 3), (∀ i ∈ V, i ∉ J) →
        IsConeFace (e '' aetGeneralizedChamberFace phi WJ V)
            (e '' aetGeneralizedChamber phi WJ) ∧
          (e '' aetGeneralizedChamberFace phi WJ V) =
            ⋃ h : WJ, (e * (h : M ≃ₗ[ℝ] M)) ''
              (aetChamber phi ∩ {y | ∀ i ∈ V, phi i ((h : M ≃ₗ[ℝ] M) y) = 0})) :=
  aetWythoffSemifan_faceClosure phi J W WJ hL

end LeanCategories.Lattices.Valued.WythoffInfinite

#print axioms LeanCategories.Lattices.Valued.WythoffInfinite.wJ_infinite
#print axioms LeanCategories.Lattices.Valued.WythoffInfinite.L_ne_chamber
#print axioms LeanCategories.Lattices.Valued.WythoffInfinite.genChamberFace_isFace
#print axioms LeanCategories.Lattices.Valued.WythoffInfinite.stab_infinite
#print axioms LeanCategories.Lattices.Valued.WythoffInfinite.faceClosure
