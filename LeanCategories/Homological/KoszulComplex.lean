/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Koszul complexes for central sequences

Weibel, *An Introduction to Homological Algebra* (1994), §4.5, pp. 111--114
(FC05-C04-U068).

For a finite central sequence `x₁,…,xₙ` in an associative ring, the degree-`p`
Koszul module is free on `p`-element subsets.  On the basis symbol `e_I` the
differential is the alternating sum obtained by deleting one index and
multiplying by the corresponding `x_i`.

This file constructs the actual chain complex together with those exact degree
and differential formulas.  The intrinsic well-definedness obligation `d²=0`
is proved by pairing the two possible deletion orders of each pair of indices.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory
open scoped BigOperators

universe u

variable (R : Type u) [Ring R]

/-- A finite sequence consists of central elements of `R`. -/
def IsCentralSequence {n : ℕ} (x : Fin n → R) : Prop :=
  ∀ (i : Fin n) (r : R), x i * r = r * x i

/-- Basis indices for the degree-`p` Koszul module on `n` generators. -/
abbrev KoszulBasisIndex (n p : ℕ) :=
  {s : Finset (Fin n) // s.card = p}

/-- The free left `R`-module in degree `p` of the combinatorial Koszul complex. -/
abbrev KoszulDegree (n p : ℕ) :=
  KoszulBasisIndex n p →₀ R

/-- Position of `j` in the increasing wedge symbol represented by `s`. -/
def koszulPosition {n p : ℕ} (s : KoszulBasisIndex n p) (j : Fin n) : ℕ :=
  (s.1.filter fun i => i < j).card

/-- Delete an index from a Koszul wedge-basis symbol. -/
def koszulEraseIndex {n p : ℕ} (s : KoszulBasisIndex n (p + 1))
    (j : Fin n) (hj : j ∈ s.1) : KoszulBasisIndex n p :=
  ⟨s.1.erase j, by
    rw [Finset.card_erase_of_mem hj, s.2]
    simp⟩

/-- Deleting a larger index does not change the position of a smaller index. -/
theorem koszulPosition_erase_of_lt {n p : ℕ} (s : KoszulBasisIndex n (p + 1))
    (j k : Fin n) (hj : j ∈ s.1) (hkj : k < j) :
    koszulPosition (koszulEraseIndex s j hj) k = koszulPosition s k := by
  simp only [koszulPosition, koszulEraseIndex]
  rw [Finset.filter_erase]
  have hnot : ¬ j < k := not_lt_of_ge hkj.le
  have hmem : j ∉ s.1.filter (fun i => i < k) := by simp [hnot]
  rw [Finset.erase_eq_self.mpr hmem]

/-- Deleting a smaller index lowers the position of a larger index by one. -/
theorem koszulPosition_erase_add_one_of_lt {n p : ℕ} (s : KoszulBasisIndex n (p + 1))
    (j k : Fin n) (hj : j ∈ s.1) (hjk : j < k) :
    koszulPosition (koszulEraseIndex s j hj) k + 1 = koszulPosition s k := by
  simp only [koszulPosition, koszulEraseIndex]
  rw [Finset.filter_erase]
  have hmem : j ∈ s.1.filter (fun i => i < k) := by simp [hj, hjk]
  have hcard : 0 < (s.1.filter (fun i => i < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

/-- Deleting two distinct indices from a wedge symbol is independent of their deletion order. -/
theorem koszulEraseIndex_comm {n p : ℕ} (s : KoszulBasisIndex n (p + 2))
    (j k : Fin n) (hj : j ∈ s.1) (hk : k ∈ s.1) (hne : j ≠ k) :
    koszulEraseIndex (koszulEraseIndex s j hj) k (Finset.mem_erase.mpr ⟨hne.symm, hk⟩) =
      koszulEraseIndex (koszulEraseIndex s k hk) j (Finset.mem_erase.mpr ⟨hne, hj⟩) := by
  apply Subtype.ext
  simp only [koszulEraseIndex]
  rw [Finset.erase_right_comm]

/-- Coefficient of the basis symbol obtained by deleting `j`. -/
def koszulBoundaryCoefficient {n p : ℕ} (x : Fin n → R)
    (s : KoszulBasisIndex n p) (j : Fin n) : R :=
  ((-1 : R) ^ koszulPosition s j) * x j

/-- The two coefficient products attached to deleting distinct indices in opposite orders differ
by a sign.  Centrality of the sequence is exactly what is needed to exchange the two `x` factors. -/
theorem koszulBoundaryCoefficient_swap {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulBasisIndex n (p + 2))
    (j k : Fin n) (hj : j ∈ s.1) (hk : k ∈ s.1) (hne : j ≠ k) :
    koszulBoundaryCoefficient R x s j *
        koszulBoundaryCoefficient R x (koszulEraseIndex s j hj) k =
      - (koszulBoundaryCoefficient R x s k *
        koszulBoundaryCoefficient R x (koszulEraseIndex s k hk) j) := by
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hkpos := koszulPosition_erase_add_one_of_lt s j k hj hjk
    have hjpos := koszulPosition_erase_of_lt s k j hk hjk
    simp only [koszulBoundaryCoefficient, hjpos]
    rw [← hkpos, pow_succ]
    have hcomm := hx j (x k)
    have hjSign := hx j ((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k)
    have hkSign := hx k ((-1 : R) ^ koszulPosition s j)
    have hsign := (Commute.pow_pow_self (-1 : R)
      (koszulPosition s j) (koszulPosition (koszulEraseIndex s j hj) k)).eq
    have hreorder :
        ((-1 : R) ^ koszulPosition s j) *
            (x j * (((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k) * x k)) =
          ((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k) *
            (x k * (((-1 : R) ^ koszulPosition s j) * x j)) := by
      calc
        _ = ((-1 : R) ^ koszulPosition s j) *
            ((x j * ((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k)) * x k) := by
              rw [mul_assoc]
        _ = ((-1 : R) ^ koszulPosition s j) *
            (((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k * x j) * x k) := by
              rw [hjSign]
        _ = (((-1 : R) ^ koszulPosition s j) *
              ((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k)) * (x j * x k) := by
              simp only [mul_assoc]
        _ = (((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k) *
              ((-1 : R) ^ koszulPosition s j)) * (x k * x j) := by rw [hsign, hcomm]
        _ = ((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k) *
            ((((-1 : R) ^ koszulPosition s j) * x k) * x j) := by
              simp only [mul_assoc]
        _ = ((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k) *
            ((x k * ((-1 : R) ^ koszulPosition s j)) * x j) := by rw [← hkSign]
        _ = ((-1 : R) ^ koszulPosition (koszulEraseIndex s j hj) k) *
            (x k * (((-1 : R) ^ koszulPosition s j) * x j)) := by rw [mul_assoc]
    simpa only [mul_assoc, mul_neg, neg_mul, neg_neg, one_mul] using hreorder
  · have hjpos := koszulPosition_erase_add_one_of_lt s k j hk hkj
    have hkpos := koszulPosition_erase_of_lt s j k hj hkj
    simp only [koszulBoundaryCoefficient, hkpos]
    rw [← hjpos, pow_succ]
    have hcomm := hx j (x k)
    have hjSign := hx j ((-1 : R) ^ koszulPosition s k)
    have hkSign := hx k ((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j)
    have hsign := (Commute.pow_pow_self (-1 : R)
      (koszulPosition (koszulEraseIndex s k hk) j) (koszulPosition s k)).eq
    have hreorder :
        ((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j) *
            (x j * (((-1 : R) ^ koszulPosition s k) * x k)) =
          ((-1 : R) ^ koszulPosition s k) *
            (x k * (((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j) * x j)) := by
      calc
        _ = ((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j) *
            ((x j * ((-1 : R) ^ koszulPosition s k)) * x k) := by rw [mul_assoc]
        _ = ((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j) *
            (((-1 : R) ^ koszulPosition s k * x j) * x k) := by rw [hjSign]
        _ = (((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j) *
              ((-1 : R) ^ koszulPosition s k)) * (x j * x k) := by simp only [mul_assoc]
        _ = (((-1 : R) ^ koszulPosition s k) *
              ((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j)) * (x k * x j) := by
              rw [hsign, hcomm]
        _ = ((-1 : R) ^ koszulPosition s k) *
            ((((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j) * x k) * x j) := by
              simp only [mul_assoc]
        _ = ((-1 : R) ^ koszulPosition s k) *
            ((x k * ((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j)) * x j) := by
              rw [← hkSign]
        _ = ((-1 : R) ^ koszulPosition s k) *
            (x k * (((-1 : R) ^ koszulPosition (koszulEraseIndex s k hk) j) * x j)) := by
              rw [mul_assoc]
    simpa only [mul_assoc, mul_neg, neg_mul, neg_neg, one_mul] using congrArg Neg.neg hreorder

/-- The alternating boundary of a degree-`p+1` basis symbol. -/
noncomputable def koszulBoundaryData {n p : ℕ} (x : Fin n → R)
    (s : KoszulBasisIndex n (p + 1)) : KoszulDegree R n p :=
  ∑ j : s.1,
    Finsupp.single (koszulEraseIndex s j.1 j.2)
      (koszulBoundaryCoefficient R x s j.1)

/-- The Koszul differential from degree `p+1` to degree `p`, obtained by linear extension of the
alternating deletion formula on basis wedges. -/
noncomputable def koszulBoundaryLinearMap {n p : ℕ} (x : Fin n → R) :
    KoszulDegree R n (p + 1) →ₗ[R] KoszulDegree R n p :=
  Finsupp.linearCombination R (fun s => koszulBoundaryData R x s)

@[simp]
theorem koszulBoundaryLinearMap_single {n p : ℕ} (x : Fin n → R)
    (s : KoszulBasisIndex n (p + 1)) (r : R) :
    koszulBoundaryLinearMap R x (Finsupp.single s r) = r • koszulBoundaryData R x s := by
  simp [koszulBoundaryLinearMap]

/-- An ordered pair of distinct indices of a wedge symbol, represented as two successive
deletions. -/
abbrev KoszulDeletionPair {n p : ℕ} (s : KoszulBasisIndex n (p + 2)) :=
  Σ j : s.1, {k : Fin n // k ∈ s.1.erase j.1}

/-- Swap the order of two successive deletions. -/
def koszulDeletionPairSwap {n p : ℕ} (s : KoszulBasisIndex n (p + 2))
    (a : KoszulDeletionPair s) : KoszulDeletionPair s :=
  ⟨⟨a.2.1, Finset.mem_of_mem_erase a.2.2⟩,
    ⟨a.1.1, Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase a.2.2).symm, a.1.2⟩⟩⟩

theorem koszulDeletionPairSwap_swap {n p : ℕ} (s : KoszulBasisIndex n (p + 2))
    (a : KoszulDeletionPair s) :
    koszulDeletionPairSwap s (koszulDeletionPairSwap s a) = a := by
  rcases a with ⟨j, k⟩
  rfl

theorem koszulDeletionPairSwap_ne {n p : ℕ} (s : KoszulBasisIndex n (p + 2))
    (a : KoszulDeletionPair s) : koszulDeletionPairSwap s a ≠ a := by
  intro h
  have hfirst := congrArg (fun z : KoszulDeletionPair s => z.1.1) h
  exact (Finset.ne_of_mem_erase a.2.2) hfirst

/-- The summand obtained by deleting the ordered pair `a=(j,k)` from a basis wedge. -/
noncomputable def koszulSecondBoundaryTerm {n p : ℕ} (x : Fin n → R)
    (s : KoszulBasisIndex n (p + 2)) (a : KoszulDeletionPair s) :
    KoszulDegree R n p :=
  Finsupp.single
    (koszulEraseIndex (koszulEraseIndex s a.1.1 a.1.2) a.2.1 a.2.2)
    (koszulBoundaryCoefficient R x s a.1.1 *
      koszulBoundaryCoefficient R x (koszulEraseIndex s a.1.1 a.1.2) a.2.1)

theorem koszulSecondBoundaryTerm_add_swap {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulBasisIndex n (p + 2))
    (a : KoszulDeletionPair s) :
    koszulSecondBoundaryTerm R x s a +
        koszulSecondBoundaryTerm R x s (koszulDeletionPairSwap s a) = 0 := by
  rcases a with ⟨j, k⟩
  have hne : j.1 ≠ k.1 := (Finset.ne_of_mem_erase k.2).symm
  have herase := koszulEraseIndex_comm s j.1 k.1 j.2 (Finset.mem_of_mem_erase k.2) hne
  have hcoeff := koszulBoundaryCoefficient_swap R x hx s j.1 k.1 j.2
    (Finset.mem_of_mem_erase k.2) hne
  simp only [koszulSecondBoundaryTerm, koszulDeletionPairSwap]
  rw [herase, hcoeff]
  simp

theorem koszulBoundaryLinearMap_boundaryData {n p : ℕ} (x : Fin n → R)
    (s : KoszulBasisIndex n (p + 2)) :
    koszulBoundaryLinearMap R x (koszulBoundaryData R x s) =
      ∑ a : KoszulDeletionPair s, koszulSecondBoundaryTerm R x s a := by
  rw [koszulBoundaryData]
  simp only [map_sum, koszulBoundaryLinearMap_single]
  simp_rw [koszulBoundaryData, Finset.smul_sum, Finsupp.smul_single']
  change (∑ j : s.1, ∑ k : {k : Fin n // k ∈ s.1.erase j.1},
      Finsupp.single (koszulEraseIndex (koszulEraseIndex s j.1 j.2) k.1 k.2)
        (koszulBoundaryCoefficient R x s j.1 *
          koszulBoundaryCoefficient R x (koszulEraseIndex s j.1 j.2) k.1)) =
    ∑ a : KoszulDeletionPair s, koszulSecondBoundaryTerm R x s a
  have huniv : (Finset.univ : Finset (KoszulDeletionPair s)) =
      (Finset.univ : Finset s.1).sigma (fun j =>
        (Finset.univ : Finset {k : Fin n // k ∈ s.1.erase j.1})) := by
    ext a
    simp
  rw [show (∑ a : KoszulDeletionPair s, koszulSecondBoundaryTerm R x s a) =
      (Finset.univ : Finset (KoszulDeletionPair s)).sum
        (fun a => koszulSecondBoundaryTerm R x s a) by rfl, huniv, Finset.sum_sigma]
  rfl

theorem koszulSecondBoundary_sum_eq_zero {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulBasisIndex n (p + 2)) :
    ∑ a : KoszulDeletionPair s, koszulSecondBoundaryTerm R x s a = 0 := by
  exact Finset.sum_involution (s := Finset.univ)
    (fun a _ => koszulDeletionPairSwap s a)
    (fun a _ => koszulSecondBoundaryTerm_add_swap R x hx s a)
    (fun a _ _ => koszulDeletionPairSwap_ne s a)
    (fun a _ => Finset.mem_univ _)
    (fun a _ => koszulDeletionPairSwap_swap s a)

/-- Consecutive Koszul differentials compose to zero. -/
theorem koszulBoundaryLinearMap_comp {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) :
    (koszulBoundaryLinearMap R x (p := p)).comp
        (koszulBoundaryLinearMap R x (p := p + 1)) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  simp only [LinearMap.comp_apply, koszulBoundaryLinearMap_single, LinearMap.zero_apply,
    map_smul]
  rw [koszulBoundaryLinearMap_boundaryData R x s,
    koszulSecondBoundary_sum_eq_zero R x hx s, smul_zero]

/-- The canonical finite Koszul chain complex of a central sequence. -/
noncomputable def koszulComplex {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (fun p => ModuleCat.of R (KoszulDegree R n p))
    (fun p => ModuleCat.ofHom (koszulBoundaryLinearMap R x (p := p)))
    (fun p => by
      apply ModuleCat.hom_ext
      change (koszulBoundaryLinearMap R x (p := p)).comp
          (koszulBoundaryLinearMap R x (p := p + 1)) = 0
      exact koszulBoundaryLinearMap_comp R x hx)

@[simp]
theorem koszulComplex_X {n : ℕ} (x : Fin n → R) (hx : IsCentralSequence R x) (p : ℕ) :
    (koszulComplex R x hx).X p = ModuleCat.of R (KoszulDegree R n p) := rfl

@[simp]
theorem koszulComplex_d {n : ℕ} (x : Fin n → R) (hx : IsCentralSequence R x) (p : ℕ) :
    (koszulComplex R x hx).d (p + 1) p =
      ModuleCat.ofHom (koszulBoundaryLinearMap R x (p := p)) := by
  simp [koszulComplex]

/-- Source-faithful realization of the Koszul complex of a finite central sequence. -/
structure KoszulComplexRealization {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) where
  /-- The realized chain complex. -/
  complex : ChainComplex (ModuleCat R) ℕ
  /-- Degree `p` is the free module on `p`-element wedge symbols. -/
  degreeIso : ∀ p : ℕ,
    complex.X p ≅ ModuleCat.of R (KoszulDegree R n p)
  /-- Differential on a basis symbol is the alternating deletion formula. -/
  differential_basis : ∀ (p : ℕ) (s : KoszulBasisIndex n (p + 1)),
    (degreeIso p).hom
        (complex.d (p + 1) p
          ((degreeIso (p + 1)).inv (Finsupp.single s 1))) =
      koszulBoundaryData R x s

/-- The canonical realization supplied by `koszulComplex`. -/
noncomputable def canonicalKoszulComplexRealization {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) : KoszulComplexRealization R x hx where
  complex := koszulComplex R x hx
  degreeIso := fun _ => Iso.refl _
  differential_basis := by
    intro p s
    simp only [koszulComplex, ChainComplex.of_d, Iso.refl_hom, Iso.refl_inv]
    change LinearMap.id
        (koszulBoundaryLinearMap R x (LinearMap.id (Finsupp.single s 1))) =
      koszulBoundaryData R x s
    rw [LinearMap.id_apply, LinearMap.id_apply]
    simpa only [one_smul] using koszulBoundaryLinearMap_single R x s (1 : R)

/-- The one-element sequence used for `K(x) : 0 → R → R → 0`. -/
def oneElementKoszulSequence (x : R) : Fin 1 → R :=
  fun _ => x

end LeanCategories.Homological
