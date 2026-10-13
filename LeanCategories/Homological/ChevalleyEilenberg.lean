/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The Chevalley--Eilenberg complex

Weibel, *An Introduction to Homological Algebra* (1994), §7.7, pp. 238--241
(FC05-C07-U047, FC05-C07-U048).

For a Lie algebra `L` over a commutative ring `k`, put
`U = U(L)` and `V_p(L) = U ⊗_k Λ^p L`.  Mathlib already owns these degree
objects and the enveloping-algebra augmentation.  This file records a
source-faithful realization of the Chevalley--Eilenberg differential on pure
wedges.

Definition 7.7.1 is the all-degree descended action-plus-bracket map itself.
Weibel's immediately following Exercise 7.7.1 asks separately for the
square-zero assertion; exercises are outside the admitted foundational corpus,
so that assertion is not part of FC05-C07-U048.  The projective-resolution
statement is the separate Theorem 7.7.2 obligation and is not asserted here.
-/

@[expose] public section

namespace LeanCategories.Homological

open scoped BigOperators TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (k L : Type u) [CommRing k] [LieRing L] [LieAlgebra k L]

/-- The pure wedge `x₀ ∧ ⋯ ∧ x_{p-1}` as an element of `Λ^p L`. -/
def chevalleyEilenbergWedge {p : ℕ} (x : Fin p → L) :
    ⋀[k]^p L :=
  ⟨ExteriorAlgebra.ιMulti k p x,
    ExteriorAlgebra.ιMulti_range k p ⟨x, rfl⟩⟩

@[simp]
theorem chevalleyEilenbergWedge_eq_ιMulti {p : ℕ} (x : Fin p → L) :
    chevalleyEilenbergWedge k L x = exteriorPower.ιMulti k p x := by
  apply Subtype.ext
  rfl

/-- A pure tensor `u ⊗ (x₀ ∧ ⋯ ∧ x_{p-1})` in `V_p(L)`. -/
def chevalleyEilenbergPure {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin p → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  u ⊗ₜ[k] chevalleyEilenbergWedge k L x

/-- The action summand before alternation: `x` acts by the image of `x` in
`U(L)` on the left tensor factor, while the remaining `p` inputs form their
pure wedge. -/
noncomputable def chevalleyEilenbergActionSeed (p : ℕ) :
    L →ₗ[k] L [⋀^Fin p]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) where
  toFun x :=
    (TensorProduct.mk k _ _ (UniversalEnvelopingAlgebra.ι k x)).compAlternatingMap
      (exteriorPower.ιMulti k p)
  map_add' x y := by
    ext v
    simp
  map_smul' r x := by
    ext v
    simp [TensorProduct.smul_tmul']

/-- The alternating action part of the Chevalley--Eilenberg differential in
degree `p + 1`. Mathlib's alternating uncurrying supplies exactly the source
sum `∑ i, (-1)^i ι(x_i) ⊗ x_0∧⋯∧x̂_i∧⋯`. -/
noncomputable def chevalleyEilenbergActionAlternating (p : ℕ) :
    L [⋀^Fin (p + 1)]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  AlternatingMap.alternatizeUncurryFin (chevalleyEilenbergActionSeed k L p)

@[simp]
theorem chevalleyEilenbergActionAlternating_apply (p : ℕ) (x : Fin (p + 1) → L) :
    chevalleyEilenbergActionAlternating k L p x =
      ∑ i : Fin (p + 1), ((-1 : ℤ) ^ i.val) •
        chevalleyEilenbergPure k L
          (UniversalEnvelopingAlgebra.ι k (x i)) (i.removeNth x) := by
  simp [chevalleyEilenbergActionAlternating, chevalleyEilenbergActionSeed,
    AlternatingMap.alternatizeUncurryFin_apply, chevalleyEilenbergPure,
    chevalleyEilenbergWedge_eq_ιMulti]

/-- Delete the `i`th factor from a wedge tuple. -/
def chevalleyEilenbergOmit {p : ℕ} (x : Fin (p + 1) → L)
    (i : Fin (p + 1)) : Fin p → L :=
  i.removeNth x

/-- Replace the `i`th surviving factor by `[x_i,x_j]` after deleting the
`j`th factor, for `i < j`.

Putting the bracket in the original `i`th position changes the standard
front-loaded bracket sign `(-1)^(i+j)` into `(-1)^j` in zero-based indexing. -/
def chevalleyEilenbergBracketTuple {p : ℕ} (x : Fin (p + 1) → L)
    (i j : Fin (p + 1)) (hij : i < j) : Fin p → L :=
  let i' : Fin p :=
    ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
  Function.update (j.removeNth x) i' ⁅x i, x j⁆

/-- The action part of the Chevalley--Eilenberg boundary on a pure wedge. -/
noncomputable def chevalleyEilenbergActionBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  ∑ i : Fin (p + 1),
    ((-1 : ℤ) ^ i.val) •
      chevalleyEilenbergPure k L
        (u * UniversalEnvelopingAlgebra.ι k (x i))
        (chevalleyEilenbergOmit L x i)

/-- The bracket part of the Chevalley--Eilenberg boundary on a pure wedge.
The bracket is kept in the original `i`th position, hence the equivalent
zero-based sign `(-1)^j`. -/
noncomputable def chevalleyEilenbergBracketBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
    if hij : i < j then
      ((-1 : ℤ) ^ j.val) •
        chevalleyEilenbergPure k L u
          (chevalleyEilenbergBracketTuple L x i j hij)
    else 0

/-- Weibel's full Chevalley--Eilenberg boundary formula on a pure wedge. -/
noncomputable def chevalleyEilenbergBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  chevalleyEilenbergActionBoundary k L u x +
    chevalleyEilenbergBracketBoundary k L u x

/-- One exterior generator acting on an already-computed adjoint derivative.
The first component of the state is the untouched exterior tail. -/
noncomputable def chevalleyEilenbergAdjointStep (x : L) :
    L →ₗ[k] (ExteriorAlgebra k L × ExteriorAlgebra k L) →ₗ[k]
      ExteriorAlgebra k L where
  toFun y :=
    { toFun := fun z =>
        ExteriorAlgebra.ι k ⁅x, y⁆ * z.1 + ExteriorAlgebra.ι k y * z.2
      map_add' := by
        intro a b
        simp only [Prod.fst_add, Prod.snd_add, mul_add]
        abel
      map_smul' := by
        intro r a
        change
          ExteriorAlgebra.ι k ⁅x, y⁆ *
                (algebraMap k (ExteriorAlgebra k L) r * a.1) +
              ExteriorAlgebra.ι k y *
                (algebraMap k (ExteriorAlgebra k L) r * a.2) =
            algebraMap k (ExteriorAlgebra k L) r *
              (ExteriorAlgebra.ι k ⁅x, y⁆ * a.1 +
                ExteriorAlgebra.ι k y * a.2)
        rw [mul_add]
        congr 1 <;> rw [← mul_assoc, ← Algebra.commutes, mul_assoc] }
  map_add' := by
    intro y z
    apply LinearMap.ext
    intro a
    simp [add_mul, lie_add]
    abel
  map_smul' := by
    intro r y
    apply LinearMap.ext
    intro a
    simp [Algebra.smul_def, lie_smul, mul_assoc, mul_add]

theorem chevalleyEilenbergAdjointStep_quadratic (x y : L)
    (w a : ExteriorAlgebra k L) :
    chevalleyEilenbergAdjointStep k L x y
        (ExteriorAlgebra.ι k y * w,
          chevalleyEilenbergAdjointStep k L x y (w, a)) = 0 := by
  change
    ExteriorAlgebra.ι k ⁅x, y⁆ * (ExteriorAlgebra.ι k y * w) +
        ExteriorAlgebra.ι k y *
          (ExteriorAlgebra.ι k ⁅x, y⁆ * w + ExteriorAlgebra.ι k y * a) = 0
  have hanti := ExteriorAlgebra.ι_add_mul_swap (R := k) ⁅x, y⁆ y
  have hsq := ExteriorAlgebra.ι_sq_zero (R := k) y
  calc
    _ = (ExteriorAlgebra.ι k ⁅x, y⁆ * ExteriorAlgebra.ι k y +
          ExteriorAlgebra.ι k y * ExteriorAlgebra.ι k ⁅x, y⁆) * w +
        (ExteriorAlgebra.ι k y * ExteriorAlgebra.ι k y) * a := by
          simp only [mul_add, add_mul, mul_assoc]
          abel
    _ = 0 := by rw [hanti, hsq]; simp

/-- The adjoint action of `L` on its exterior algebra, acting on one exterior
factor at a time. -/
noncomputable def chevalleyEilenbergExteriorAdjoint (x : L) :
    ExteriorAlgebra k L →ₗ[k] ExteriorAlgebra k L :=
  CliffordAlgebra.foldr' (0 : QuadraticForm k L)
    (chevalleyEilenbergAdjointStep k L x)
    (by
      intro y w a
      simpa using chevalleyEilenbergAdjointStep_quadratic k L x y w a) 0

@[simp]
theorem chevalleyEilenbergExteriorAdjoint_ι_mul (x y : L)
    (w : ExteriorAlgebra k L) :
    chevalleyEilenbergExteriorAdjoint k L x (ExteriorAlgebra.ι k y * w) =
      ExteriorAlgebra.ι k ⁅x, y⁆ * w +
        ExteriorAlgebra.ι k y * chevalleyEilenbergExteriorAdjoint k L x w := by
  rw [chevalleyEilenbergExteriorAdjoint, CliffordAlgebra.foldr'_ι_mul]
  rfl

@[simp]
theorem chevalleyEilenbergExteriorAdjoint_algebraMap (x : L) (r : k) :
    chevalleyEilenbergExteriorAdjoint k L x
        (algebraMap k (ExteriorAlgebra k L) r) = 0 := by
  rw [chevalleyEilenbergExteriorAdjoint, CliffordAlgebra.foldr'_algebraMap]
  simp

theorem chevalleyEilenbergExteriorAdjoint_add (x y : L)
    (w : ExteriorAlgebra k L) :
    chevalleyEilenbergExteriorAdjoint k L (x + y) w =
      chevalleyEilenbergExteriorAdjoint k L x w +
        chevalleyEilenbergExteriorAdjoint k L y w := by
  induction w using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp [map_add, ha, hb, add_left_comm, add_comm]
  | ι_mul z w hw =>
      simp only [chevalleyEilenbergExteriorAdjoint_ι_mul, add_lie, map_add, hw]
      simp only [add_mul, mul_add]
      abel

theorem chevalleyEilenbergExteriorAdjoint_smul (r : k) (x : L)
    (w : ExteriorAlgebra k L) :
    chevalleyEilenbergExteriorAdjoint k L (r • x) w =
      r • chevalleyEilenbergExteriorAdjoint k L x w := by
  induction w using CliffordAlgebra.left_induction with
  | algebraMap s => simp
  | add a b ha hb => simp [map_add, ha, hb, smul_add]
  | ι_mul w z hw =>
      simp only [chevalleyEilenbergExteriorAdjoint_ι_mul, smul_lie, map_smul, hw]
      change
        (algebraMap k (ExteriorAlgebra k L) r * ExteriorAlgebra.ι k ⁅x, z⁆) * w +
            ExteriorAlgebra.ι k z *
              (algebraMap k (ExteriorAlgebra k L) r *
                chevalleyEilenbergExteriorAdjoint k L x w) =
          algebraMap k (ExteriorAlgebra k L) r *
            (ExteriorAlgebra.ι k ⁅x, z⁆ * w +
              ExteriorAlgebra.ι k z * chevalleyEilenbergExteriorAdjoint k L x w)
      rw [mul_add, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι k z),
        ← Algebra.commutes r (ExteriorAlgebra.ι k z), mul_assoc]

/-- The exterior adjoint derivation replaces one factor at a time by its
bracket with the acting element. -/
theorem chevalleyEilenbergExteriorAdjoint_ιMulti_replace :
    ∀ (p : ℕ) (x : L) (v : Fin p → L),
      chevalleyEilenbergExteriorAdjoint k L x
          (ExteriorAlgebra.ιMulti k p v) =
        ∑ i : Fin p,
          ExteriorAlgebra.ιMulti k p (Function.update v i ⁅x, v i⁆) := by
  intro p
  induction p with
  | zero =>
      intro x v
      simpa using chevalleyEilenbergExteriorAdjoint_algebraMap k L x (1 : k)
  | succ p ih =>
      intro x v
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        chevalleyEilenbergExteriorAdjoint_ι_mul, ih,
        Fin.sum_univ_succ]
      simp only [Function.update_self, ExteriorAlgebra.ιMulti_succ_apply]
      rw [Finset.mul_sum]
      have hzeroTail :
          Matrix.vecTail (Function.update v 0 ⁅x, v 0⁆) = Matrix.vecTail v := by
        funext j
        change Function.update v 0 ⁅x, v 0⁆ j.succ = v j.succ
        rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rw [hzeroTail]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have htail :
          Matrix.vecTail (Function.update v i.succ ⁅x, v i.succ⁆) =
            Function.update (Matrix.vecTail v) i ⁅x, v i.succ⁆ := by
        funext j
        change
          Function.update v i.succ ⁅x, v i.succ⁆ j.succ =
            Function.update (Matrix.vecTail v) i ⁅x, v i.succ⁆ j
        by_cases hji : j = i
        · subst j
          rw [Function.update_self, Function.update_self]
        · have hs : j.succ ≠ i.succ := (Fin.succ_injective _).ne hji
          rw [Function.update_of_ne hs, Function.update_of_ne hji]
          rfl
      rw [htail]
      have hhead :
          Function.update v i.succ ⁅x, v i.succ⁆ 0 = v 0 :=
        Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
      rw [hhead]
      rfl

/-- Moving the replaced factor to the front gives the zero-based sign used in
Weibel's bracket summand. -/
theorem chevalleyEilenbergExteriorAdjoint_ιMulti_front (p : ℕ) (x : L)
    (v : Fin (p + 1) → L) :
    chevalleyEilenbergExteriorAdjoint k L x
        (ExteriorAlgebra.ιMulti k (p + 1) v) =
      ∑ i : Fin (p + 1), ((-1 : ℤ) ^ i.val) •
        ExteriorAlgebra.ιMulti k (p + 1)
          (Fin.cons ⁅x, v i⁆ (i.removeNth v)) := by
  rw [chevalleyEilenbergExteriorAdjoint_ιMulti_replace k L (p + 1) x v]
  apply Finset.sum_congr rfl
  intro i hi
  have hins :
      Function.update v i ⁅x, v i⁆ =
        i.insertNth ⁅x, v i⁆ (i.removeNth v) := by
    symm
    exact Fin.insertNth_removeNth i ⁅x, v i⁆ v
  rw [hins, AlternatingMap.map_insertNth]
  rfl

/-- Left exterior multiplication by one Lie-algebra generator. -/
noncomputable def chevalleyEilenbergExteriorWedgeLeft (x : L) :
    ExteriorAlgebra k L →ₗ[k] ExteriorAlgebra k L :=
  LinearMap.mulLeft k (ExteriorAlgebra.ι k x)

@[simp]
theorem chevalleyEilenbergExteriorWedgeLeft_apply (x : L)
    (w : ExteriorAlgebra k L) :
    chevalleyEilenbergExteriorWedgeLeft k L x w =
      ExteriorAlgebra.ι k x * w := by
  rfl

theorem chevalleyEilenbergBracketTuple_cons_head (p : ℕ) (x : L)
    (v : Fin (p + 1) → L) (j : Fin (p + 1)) :
    chevalleyEilenbergBracketTuple L (Fin.cons x v) 0 j.succ
        (Fin.succ_pos j) =
      Fin.cons ⁅x, v j⁆ (j.removeNth v) := by
  funext q
  refine Fin.cases ?_ (fun r => ?_) q
  · simp [chevalleyEilenbergBracketTuple]
  · simp [chevalleyEilenbergBracketTuple, Fin.removeNth_apply]

theorem chevalleyEilenbergBracketTuple_cons_tail (p : ℕ) (x : L)
    (v : Fin (p + 1) → L) (i j : Fin (p + 1)) (hij : i < j) :
    chevalleyEilenbergBracketTuple L (Fin.cons x v) i.succ j.succ
        (Fin.succ_lt_succ_iff.mpr hij) =
      Fin.cons x (chevalleyEilenbergBracketTuple L v i j hij) := by
  funext q
  refine Fin.cases ?_ (fun r => ?_) q
  · simp [chevalleyEilenbergBracketTuple, Fin.removeNth_apply]
  · unfold chevalleyEilenbergBracketTuple
    dsimp only
    simp only [Fin.cons_succ]
    let ii : Fin p :=
      ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
    have hidx :
        (⟨i.succ.val,
          lt_of_lt_of_le (Fin.succ_lt_succ_iff.mpr hij)
            (Nat.le_of_lt_succ j.succ.isLt)⟩ : Fin (p + 1)) = ii.succ := by
      apply Fin.ext
      rfl
    rw [hidx]
    by_cases hr : r = ii
    · subst r
      simp [ii]
    · have hrs : r.succ ≠ ii.succ := by
        intro h
        apply hr
        exact Fin.succ_injective _ h
      rw [Function.update_of_ne hrs, Function.update_of_ne hr]
      simp [Fin.removeNth_apply]

/-- The exterior-algebra form of Weibel's bracket summand. -/
noncomputable def chevalleyEilenbergExteriorBracketBoundary {p : ℕ}
    (x : Fin (p + 1) → L) : ExteriorAlgebra k L :=
  ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
    if hij : i < j then
      ((-1 : ℤ) ^ j.val) •
        ExteriorAlgebra.ιMulti k p
          (chevalleyEilenbergBracketTuple L x i j hij)
    else 0

theorem chevalleyEilenbergExteriorBracketBoundary_cons_head
    (p : ℕ) (x : L) (v : Fin (p + 1) → L) :
    (∑ j : Fin (p + 2),
      if hij : (0 : Fin (p + 2)) < j then
        ((-1 : ℤ) ^ j.val) •
          ExteriorAlgebra.ιMulti k (p + 1)
            (chevalleyEilenbergBracketTuple L (Fin.cons x v) 0 j hij)
      else 0) =
      -chevalleyEilenbergExteriorAdjoint k L x
        (ExteriorAlgebra.ιMulti k (p + 1) v) := by
  rw [Fin.sum_univ_succ]
  simp only [lt_self_iff_false, ↓reduceDIte, zero_add]
  simp_rw [chevalleyEilenbergBracketTuple_cons_head]
  rw [chevalleyEilenbergExteriorAdjoint_ιMulti_front]
  simp only [Fin.val_succ, pow_succ, mul_smul, neg_one_smul]
  simp

theorem chevalleyEilenbergExteriorBracketBoundary_cons_tail
    (p : ℕ) (x : L) (v : Fin (p + 1) → L) :
    (∑ i : Fin (p + 1), ∑ j : Fin (p + 2),
      if hij : i.succ < j then
        ((-1 : ℤ) ^ j.val) •
          ExteriorAlgebra.ιMulti k (p + 1)
            (chevalleyEilenbergBracketTuple L (Fin.cons x v) i.succ j hij)
      else 0) =
      -chevalleyEilenbergExteriorWedgeLeft k L x
        (chevalleyEilenbergExteriorBracketBoundary k L v) := by
  rw [chevalleyEilenbergExteriorBracketBoundary, map_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.sum_univ_succ]
  simp only [not_lt_zero, ↓reduceDIte, zero_add]
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · rw [dif_pos (Fin.succ_lt_succ_iff.mpr hij), dif_pos hij]
    rw [chevalleyEilenbergBracketTuple_cons_tail]
    change
      ((-1 : ℤ) ^ j.succ.val) •
          ExteriorAlgebra.ιMulti k (p + 1)
            (Fin.cons x (chevalleyEilenbergBracketTuple L v i j hij)) =
        -chevalleyEilenbergExteriorWedgeLeft k L x
          (((-1 : ℤ) ^ j.val) •
            ExteriorAlgebra.ιMulti k p
              (chevalleyEilenbergBracketTuple L v i j hij))
    rw [map_zsmul]
    rw [ExteriorAlgebra.ιMulti_succ_apply,
      chevalleyEilenbergExteriorWedgeLeft_apply]
    simp [Matrix.vecTail, pow_succ]
  · have hs : ¬i.succ < j.succ := by
      simpa only [Fin.succ_lt_succ_iff] using hij
    rw [dif_neg hs, dif_neg hij, map_zero]
    simp

theorem chevalleyEilenbergExteriorBracketBoundary_cons
    (p : ℕ) (x : L) (v : Fin (p + 1) → L) :
    chevalleyEilenbergExteriorBracketBoundary k L (Fin.cons x v) =
      -chevalleyEilenbergExteriorWedgeLeft k L x
          (chevalleyEilenbergExteriorBracketBoundary k L v) -
        chevalleyEilenbergExteriorAdjoint k L x
          (ExteriorAlgebra.ιMulti k (p + 1) v) := by
  rw [chevalleyEilenbergExteriorBracketBoundary, Fin.sum_univ_succ,
    chevalleyEilenbergExteriorBracketBoundary_cons_head,
    chevalleyEilenbergExteriorBracketBoundary_cons_tail]
  abel

/-- The recursive bracket-only step on the exterior algebra.  If the tail
`w` has bracket boundary `b`, then the boundary of `x ∧ w` is
`-x ∧ b - A_x(w)`, where `A_x` is the exterior adjoint action. -/
noncomputable def chevalleyEilenbergExteriorBracketStep :
    L →ₗ[k] (ExteriorAlgebra k L × ExteriorAlgebra k L) →ₗ[k]
      ExteriorAlgebra k L where
  toFun x :=
    { toFun := fun z =>
        -(ExteriorAlgebra.ι k x * z.2 +
          chevalleyEilenbergExteriorAdjoint k L x z.1)
      map_add' := by
        intro a b
        simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add]
        abel
      map_smul' := by
        intro r a
        change
          -(ExteriorAlgebra.ι k x *
                (algebraMap k (ExteriorAlgebra k L) r * a.2) +
              chevalleyEilenbergExteriorAdjoint k L x (r • a.1)) =
            algebraMap k (ExteriorAlgebra k L) r *
              -(ExteriorAlgebra.ι k x * a.2 +
                chevalleyEilenbergExteriorAdjoint k L x a.1)
        rw [map_smul, Algebra.smul_def, mul_neg, mul_add]
        congr 1
        rw [← mul_assoc, ← Algebra.commutes r (ExteriorAlgebra.ι k x),
          mul_assoc] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change
      -(ExteriorAlgebra.ι k (x + y) * z.2 +
          chevalleyEilenbergExteriorAdjoint k L (x + y) z.1) =
        -(ExteriorAlgebra.ι k x * z.2 +
            chevalleyEilenbergExteriorAdjoint k L x z.1) +
          -(ExteriorAlgebra.ι k y * z.2 +
            chevalleyEilenbergExteriorAdjoint k L y z.1)
    rw [map_add, add_mul, chevalleyEilenbergExteriorAdjoint_add]
    abel
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    change
      -(ExteriorAlgebra.ι k (r • x) * z.2 +
          chevalleyEilenbergExteriorAdjoint k L (r • x) z.1) =
        r • -(ExteriorAlgebra.ι k x * z.2 +
            chevalleyEilenbergExteriorAdjoint k L x z.1)
    simp [chevalleyEilenbergExteriorAdjoint_smul, Algebra.smul_def,
      mul_assoc, mul_add]

@[simp]
theorem chevalleyEilenbergExteriorBracketStep_apply (x : L)
    (w b : ExteriorAlgebra k L) :
    chevalleyEilenbergExteriorBracketStep k L x (w, b) =
      -(ExteriorAlgebra.ι k x * b +
        chevalleyEilenbergExteriorAdjoint k L x w) := by
  simp [chevalleyEilenbergExteriorBracketStep]

theorem chevalleyEilenbergExteriorBracketStep_quadratic (x : L)
    (w b : ExteriorAlgebra k L) :
    chevalleyEilenbergExteriorBracketStep k L x
        (ExteriorAlgebra.ι k x * w,
          chevalleyEilenbergExteriorBracketStep k L x (w, b)) = 0 := by
  rw [chevalleyEilenbergExteriorBracketStep_apply,
    chevalleyEilenbergExteriorBracketStep_apply,
    chevalleyEilenbergExteriorAdjoint_ι_mul]
  rw [lie_self, map_zero, zero_mul, zero_add]
  have hsq := ExteriorAlgebra.ι_sq_zero (R := k) x
  calc
    _ = (ExteriorAlgebra.ι k x * ExteriorAlgebra.ι k x) * b := by
      simp only [mul_neg, mul_add, neg_add_rev, neg_neg, mul_assoc]
      abel
    _ = 0 := by rw [hsq, zero_mul]

/-- The bracket part of the Chevalley--Eilenberg differential, descended
directly to the exterior algebra. -/
noncomputable def chevalleyEilenbergExteriorBracketDifferential :
    ExteriorAlgebra k L →ₗ[k] ExteriorAlgebra k L :=
  CliffordAlgebra.foldr' (0 : QuadraticForm k L)
    (chevalleyEilenbergExteriorBracketStep k L)
    (by
      intro x w b
      simpa using
        chevalleyEilenbergExteriorBracketStep_quadratic k L x w b) 0

@[simp]
theorem chevalleyEilenbergExteriorBracketDifferential_ι_mul (x : L)
    (w : ExteriorAlgebra k L) :
    chevalleyEilenbergExteriorBracketDifferential k L
        (ExteriorAlgebra.ι k x * w) =
      -(ExteriorAlgebra.ι k x *
          chevalleyEilenbergExteriorBracketDifferential k L w +
        chevalleyEilenbergExteriorAdjoint k L x w) := by
  rw [chevalleyEilenbergExteriorBracketDifferential,
    CliffordAlgebra.foldr'_ι_mul,
    chevalleyEilenbergExteriorBracketStep_apply]

@[simp]
theorem chevalleyEilenbergExteriorBracketDifferential_algebraMap (r : k) :
    chevalleyEilenbergExteriorBracketDifferential k L
        (algebraMap k (ExteriorAlgebra k L) r) = 0 := by
  rw [chevalleyEilenbergExteriorBracketDifferential,
    CliffordAlgebra.foldr'_algebraMap]
  simp

/-- The recursively descended bracket differential is exactly Weibel's
displayed pair sum on every pure wedge. -/
theorem chevalleyEilenbergExteriorBracketDifferential_ιMulti :
    ∀ (p : ℕ) (v : Fin (p + 1) → L),
      chevalleyEilenbergExteriorBracketDifferential k L
          (ExteriorAlgebra.ιMulti k (p + 1) v) =
        chevalleyEilenbergExteriorBracketBoundary k L v := by
  intro p
  induction p with
  | zero =>
      intro v
      rw [← Fin.cons_self_tail v, ExteriorAlgebra.ιMulti_succ_apply,
        chevalleyEilenbergExteriorBracketDifferential_ι_mul]
      simp only [Fin.cons_zero, ExteriorAlgebra.ιMulti_zero_apply]
      have hone :
          (1 : ExteriorAlgebra k L) =
            algebraMap k (ExteriorAlgebra k L) 1 := by simp
      rw [hone, chevalleyEilenbergExteriorBracketDifferential_algebraMap,
        chevalleyEilenbergExteriorAdjoint_algebraMap]
      simp [chevalleyEilenbergExteriorBracketBoundary, Fin.eq_zero]
  | succ p ih =>
      intro v
      rw [← Fin.cons_self_tail v, ExteriorAlgebra.ιMulti_succ_apply,
        chevalleyEilenbergExteriorBracketDifferential_ι_mul, ih,
        chevalleyEilenbergExteriorBracketBoundary_cons,
        chevalleyEilenbergExteriorWedgeLeft_apply]
      simp only [Fin.cons_zero]
      abel

/-- The bracket summand as an alternating map into the homogeneous degree
`p` exterior power.  Homogeneity follows from the explicit Weibel formula. -/
noncomputable def chevalleyEilenbergBracketAlternating (p : ℕ) :
    L [⋀^Fin (p + 1)]→ₗ[k] (⋀[k]^p L) :=
  ((chevalleyEilenbergExteriorBracketDifferential k L).compAlternatingMap
      (ExteriorAlgebra.ιMulti k (p + 1))).codRestrict
    (⋀[k]^p L) (by
      intro v
      rw [LinearMap.compAlternatingMap_apply,
        chevalleyEilenbergExteriorBracketDifferential_ιMulti]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.sum_mem
      intro j hj
      split_ifs with hij
      · exact zsmul_mem
          (ExteriorAlgebra.ιMulti_range k p ⟨_, rfl⟩) _
      · exact Submodule.zero_mem _)

@[simp]
theorem chevalleyEilenbergBracketAlternating_coe (p : ℕ)
    (v : Fin (p + 1) → L) :
    ((chevalleyEilenbergBracketAlternating k L p v : ⋀[k]^p L) :
        ExteriorAlgebra k L) =
      chevalleyEilenbergExteriorBracketBoundary k L v := by
  change
    chevalleyEilenbergExteriorBracketDifferential k L
        (ExteriorAlgebra.ιMulti k (p + 1) v) =
      chevalleyEilenbergExteriorBracketBoundary k L v
  exact chevalleyEilenbergExteriorBracketDifferential_ιMulti k L p v

@[simp]
theorem chevalleyEilenbergBracketAlternating_apply (p : ℕ)
    (v : Fin (p + 1) → L) :
    chevalleyEilenbergBracketAlternating k L p v =
      ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
        if hij : i < j then
          ((-1 : ℤ) ^ j.val) •
            chevalleyEilenbergWedge k L
              (chevalleyEilenbergBracketTuple L v i j hij)
        else 0 := by
  apply Subtype.ext
  rw [chevalleyEilenbergBracketAlternating_coe]
  rw [chevalleyEilenbergExteriorBracketBoundary]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · rw [dif_pos hij, dif_pos hij]
    rfl
  · rw [dif_neg hij, dif_neg hij]
    rfl

/-- The exterior-valued bracket term embedded in `U(L) ⊗ Λ^p L` by
`w ↦ 1 ⊗ w`. -/
noncomputable def chevalleyEilenbergBracketTensorAlternating (p : ℕ) :
    L [⋀^Fin (p + 1)]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  (TensorProduct.mk k (UniversalEnvelopingAlgebra k L) (⋀[k]^p L) 1).compAlternatingMap
    (chevalleyEilenbergBracketAlternating k L p)

/-- The complete action-plus-bracket formula before descending through
`Λ^{p+1}L`. -/
noncomputable def chevalleyEilenbergAlternating (p : ℕ) :
    L [⋀^Fin (p + 1)]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  chevalleyEilenbergActionAlternating k L p +
    chevalleyEilenbergBracketTensorAlternating k L p

/-- The descended `k`-linear Chevalley--Eilenberg differential on the
exterior-power factor. -/
noncomputable def chevalleyEilenbergExteriorDifferential (p : ℕ) :
    (⋀[k]^(p + 1) L) →ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  exteriorPower.alternatingMapLinearEquiv
    (chevalleyEilenbergAlternating k L p)

@[simp]
theorem chevalleyEilenbergExteriorDifferential_ιMulti (p : ℕ)
    (x : Fin (p + 1) → L) :
    chevalleyEilenbergExteriorDifferential k L p
        (exteriorPower.ιMulti k _ x) =
      chevalleyEilenbergAlternating k L p x := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- Currying the differential with respect to the left `U(L)`-action. -/
noncomputable def chevalleyEilenbergDifferentialCurry (p : ℕ) :
    UniversalEnvelopingAlgebra k L →ₗ[UniversalEnvelopingAlgebra k L]
      ((⋀[k]^(p + 1) L) →ₗ[k]
        (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L))) where
  toFun u := u • chevalleyEilenbergExteriorDifferential k L p
  map_add' u v := by
    rw [add_smul]
  map_smul' u v := by
    simp only [smul_eq_mul, RingHom.id_apply, mul_smul]

/-- Weibel Definition 7.7.1: the `U(L)`-linear differential
`U(L) ⊗ Λ^{p+1}L → U(L) ⊗ Λ^pL`. -/
noncomputable def chevalleyEilenbergDifferential (p : ℕ) :
    (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^(p + 1) L))
      →ₗ[UniversalEnvelopingAlgebra k L]
    (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  TensorProduct.AlgebraTensorModule.lift
    (chevalleyEilenbergDifferentialCurry k L p)

@[simp]
theorem chevalleyEilenbergDifferential_tmul (p : ℕ)
    (u : UniversalEnvelopingAlgebra k L) (w : ⋀[k]^(p + 1) L) :
    chevalleyEilenbergDifferential k L p (u ⊗ₜ[k] w) =
      u • chevalleyEilenbergExteriorDifferential k L p w := by
  rfl

@[simp]
theorem chevalleyEilenbergDifferential_pure (p : ℕ)
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    chevalleyEilenbergDifferential k L p
        (u ⊗ₜ[k] exteriorPower.ιMulti k _ x) =
      u • chevalleyEilenbergAlternating k L p x := by
  rw [chevalleyEilenbergDifferential_tmul,
    chevalleyEilenbergExteriorDifferential_ιMulti]

@[simp]
theorem chevalleyEilenbergUEASmul_tmul
    (u v : UniversalEnvelopingAlgebra k L) (w : ⋀[k]^p L) :
    u • (v ⊗ₜ[k] w) = (u * v) ⊗ₜ[k] w := by
  rw [TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor]
  simp

@[simp]
theorem chevalleyEilenbergUEASmul_zsmul
    (u : UniversalEnvelopingAlgebra k L) (n : ℤ)
    (z : UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :
    u • (n • z) = n • (u • z) :=
  (DistribSMul.toAddMonoidHom _ u).map_zsmul n z

/-- On every pure wedge, the descended differential is exactly Weibel's
displayed all-degree action-plus-bracket formula. -/
@[simp]
theorem chevalleyEilenbergDifferential_pure_boundary (p : ℕ)
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    chevalleyEilenbergDifferential k L p
        (u ⊗ₜ[k] exteriorPower.ιMulti k _ x) =
      chevalleyEilenbergBoundary k L u x := by
  classical
  rw [chevalleyEilenbergDifferential_pure]
  simp only [chevalleyEilenbergAlternating, AlternatingMap.add_apply,
    smul_add, chevalleyEilenbergBoundary]
  congr 1
  · rw [chevalleyEilenbergActionAlternating_apply,
      chevalleyEilenbergActionBoundary, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [chevalleyEilenbergUEASmul_zsmul]
    simp [chevalleyEilenbergPure, chevalleyEilenbergOmit]
  · rw [chevalleyEilenbergBracketTensorAlternating,
      LinearMap.compAlternatingMap_apply,
      chevalleyEilenbergBracketAlternating_apply,
      chevalleyEilenbergBracketBoundary]
    change
      u • (1 ⊗ₜ[k] (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
        if hij : i < j then
          ((-1 : ℤ) ^ j.val) • chevalleyEilenbergWedge k L
            (chevalleyEilenbergBracketTuple L x i j hij)
        else 0)) =
      ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
        if hij : i < j then
          ((-1 : ℤ) ^ j.val) • chevalleyEilenbergPure k L u
            (chevalleyEilenbergBracketTuple L x i j hij)
        else 0
    rw [chevalleyEilenbergUEASmul_tmul, mul_one, TensorProduct.tmul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [TensorProduct.tmul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij]
      exact map_zsmul (TensorProduct.mk k _ _ u)
        ((-1 : ℤ) ^ j.val)
          (chevalleyEilenbergWedge k L
            (chevalleyEilenbergBracketTuple L x i j hij))
    · rw [dif_neg hij, dif_neg hij]
      simp

end LeanCategories.Homological
