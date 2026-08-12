/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.RootBase

/-!
# Existence of a base of simple roots

`RootBase.lean` says what a base of simple roots is and derives the shape restrictions on its
graph, but leaves the existence question open. This file settles it for an even negative
definite root lattice, by the classical construction from a separating functional.

* `exists_forall_apply_ne_zero` supplies the functional. The root set of a definite lattice is
  finite, and the form of a definite lattice separates every nonzero vector from zero, so a
  finite induction produces one functional `f` that vanishes on no root. The induction step
  replaces `f` by `t • f + g`, and only finitely many integers `t` are excluded, one for each
  vector already separated by `f`.
* `positiveRoots L f` is the set of roots on which `f` is positive. Every root lies there or has
  its negative there, because `f` vanishes on no root.
* `IsIndecomposableRoot L f x` says `x` is a positive root that is not a sum of two positive
  roots, and `simpleRootSet L f` collects these.

The three conditions of `IsRootBase` come out as follows.

* Pairings. This repository takes its root lattices negative definite, so a root has
  self-pairing `-2` and the difference of two roots that pair to `-1` is again a root. If two
  distinct indecomposable positive roots paired to `-1`, that difference would be a positive
  root witnessing a decomposition of one of them, so the pairing lies in `{0, 1}`.
* Spanning. A positive root that is not indecomposable splits into two positive roots of
  strictly smaller value of `f`, so induction on `(f x).toNat` puts every positive root in the
  span of `simpleRootSet L f`. Negation covers the remaining roots, and the roots span.
* Independence. A vanishing integer combination splits into its positive and its negative part.
  The two parts are equal as vectors, so the self-pairing of the positive part is a sum of
  products of non-negative pairings, hence non-negative, which a negative definite form allows
  only for the zero vector. Applying `f` to that zero vector then empties both parts.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

/-- A finite set of vectors, each of which some linear functional does not kill, is avoided by a
single linear functional. The induction step tilts the functional already built for the smaller
set by a multiple of one that survives on the new vector; only one integer multiple is lost per
vector of the smaller set. -/
theorem exists_forall_apply_ne_zero {M : Type*} [AddCommGroup M] [Module ℤ M] (S : Finset M)
    (h : ∀ x ∈ S, ∃ g : M →ₗ[ℤ] ℤ, g x ≠ 0) : ∃ f : M →ₗ[ℤ] ℤ, ∀ x ∈ S, f x ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨f, hf⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    by_cases hfa : f a = 0
    · obtain ⟨g, hg⟩ := h a (Finset.mem_insert_self a S)
      obtain ⟨t, -, ht⟩ := (Set.infinite_univ (α := ℤ)).exists_notMem_finset
        (S.image fun x => -g x / f x)
      refine ⟨t • f + g, fun x hx hzero => ?_⟩
      have hval : t * f x + g x = 0 := by simpa [smul_eq_mul] using hzero
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · rw [hfa, mul_zero, zero_add] at hval
        exact hg hval
      · refine ht (Finset.mem_image.mpr ⟨x, hxS, ?_⟩)
        have hfx : f x ≠ 0 := hf x hxS
        have hne : -g x = t * f x := by omega
        rw [hne, Int.mul_ediv_cancel _ hfx]
    · refine ⟨f, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact hfa
      · exact hf x hxS

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- The pairing negates in its left argument. -/
theorem pairing_neg_left (L : FiniteProjectiveLatticeCat ℤ ℤ) (x y : L.obj.obj.carrier) :
    L.obj.obj.pairing (-x) y = -L.obj.obj.pairing x y := by
  rw [pairing_comm L (-x) y, pairing_neg_right, pairing_comm L y x]

/-- Negation preserves the self-pairing of a vector. -/
theorem pairing_neg_self (L : FiniteProjectiveLatticeCat ℤ ℤ) (x : L.obj.obj.carrier) :
    L.obj.obj.pairing (-x) (-x) = L.obj.obj.pairing x x := by
  rw [pairing_neg_left, pairing_neg_right, neg_neg]

/-- The negative of a root is a root. -/
theorem isRoot_neg (L : FiniteProjectiveLatticeCat ℤ ℤ) {x : L.obj.obj.carrier}
    (hx : IsRoot L.obj x) : IsRoot L.obj (-x) := by
  have h := L.pairing_neg_self x
  rcases hx with hv | hv | hv | hv
  · exact Or.inl (by rw [h, hv])
  · exact Or.inr (Or.inl (by rw [h, hv]))
  · exact Or.inr (Or.inr (Or.inl (by rw [h, hv])))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, hv])))

/-- Every root of a lattice is separated from zero by the form itself, so a finite root set of a
lattice admits a linear functional vanishing on none of its members. -/
theorem exists_forall_root_apply_ne_zero (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : isDefiniteLattice L) :
    ∃ f : L.obj.obj.carrier →ₗ[ℤ] ℤ, ∀ x ∈ L.rootSet, f x ≠ 0 := by
  classical
  have hsep : ∀ x ∈ (L.rootSet_finite_of_isDefinite hL).toFinset,
      ∃ g : L.obj.obj.carrier →ₗ[ℤ] ℤ, g x ≠ 0 := by
    intro x hx
    refine ⟨L.obj.obj.bilinMap x, ?_⟩
    have hroot := (L.rootSet_finite_of_isDefinite hL).mem_toFinset.mp hx
    rw [BilinModuleCat.bilinMap_apply]
    rcases hroot with hv | hv | hv | hv <;> rw [hv] <;> decide
  obtain ⟨f, hf⟩ := exists_forall_apply_ne_zero _ hsep
  exact ⟨f, fun x hx => hf x ((L.rootSet_finite_of_isDefinite hL).mem_toFinset.mpr hx)⟩

/-- The roots on which a linear functional takes a positive value. -/
def positiveRoots (L : FiniteProjectiveLatticeCat ℤ ℤ) (f : L.obj.obj.carrier →ₗ[ℤ] ℤ) :
    Set L.obj.obj.carrier :=
  {x | IsRoot L.obj x ∧ 0 < f x}

/-- Membership in the positive roots is the root condition together with positivity. -/
@[simp]
theorem mem_positiveRoots {f : L.obj.obj.carrier →ₗ[ℤ] ℤ} {x : L.obj.obj.carrier} :
    x ∈ positiveRoots L f ↔ IsRoot L.obj x ∧ 0 < f x :=
  Iff.rfl

/-- A positive root that is not a sum of two positive roots. -/
def IsIndecomposableRoot (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (f : L.obj.obj.carrier →ₗ[ℤ] ℤ) (x : L.obj.obj.carrier) : Prop :=
  x ∈ positiveRoots L f ∧ ∀ y ∈ positiveRoots L f, ∀ z ∈ positiveRoots L f, x ≠ y + z

/-- The indecomposable positive roots. This is the candidate base of simple roots. -/
def simpleRootSet (L : FiniteProjectiveLatticeCat ℤ ℤ) (f : L.obj.obj.carrier →ₗ[ℤ] ℤ) :
    Set L.obj.obj.carrier :=
  {x | IsIndecomposableRoot L f x}

/-- Membership in the simple roots is indecomposability. -/
@[simp]
theorem mem_simpleRootSet {f : L.obj.obj.carrier →ₗ[ℤ] ℤ} {x : L.obj.obj.carrier} :
    x ∈ simpleRootSet L f ↔ IsIndecomposableRoot L f x :=
  Iff.rfl

/-- A functional that vanishes on no root cuts the root set into two opposite halves. -/
theorem mem_positiveRoots_or_neg (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (f : L.obj.obj.carrier →ₗ[ℤ] ℤ) (hf : ∀ x ∈ L.rootSet, f x ≠ 0)
    {x : L.obj.obj.carrier} (hx : IsRoot L.obj x) :
    x ∈ positiveRoots L f ∨ -x ∈ positiveRoots L f := by
  have hne := hf x hx
  have hneg : f (-x) = -f x := map_neg f x
  rcases lt_or_gt_of_ne hne with hv | hv
  · exact Or.inr ⟨L.isRoot_neg hx, by omega⟩
  · exact Or.inl ⟨hx, hv⟩

/-- A positive root of an even negative definite lattice has self-pairing `-2`. -/
theorem pairing_self_of_mem_positiveRoots (hL : IsNegativeDefiniteLattice L) (hE : IsEven L.obj)
    {f : L.obj.obj.carrier →ₗ[ℤ] ℤ} {x : L.obj.obj.carrier} (hx : x ∈ positiveRoots L f) :
    L.obj.obj.pairing x x = -2 :=
  (L.isRoot_iff_pairing_eq_neg_two hL hE x).mp hx.1

/-- The pairing condition of a base. Two distinct indecomposable positive roots pair in
`{0, 1}`: a pairing of `-1` would make their difference a root, and one of that difference and
its negative is positive, which decomposes one of the two. -/
theorem pairing_eq_zero_or_one_of_isIndecomposableRoot (hL : IsNegativeDefiniteLattice L)
    (hE : IsEven L.obj) {f : L.obj.obj.carrier →ₗ[ℤ] ℤ} (hf : ∀ x ∈ L.rootSet, f x ≠ 0)
    {x y : L.obj.obj.carrier} (hx : IsIndecomposableRoot L f x)
    (hy : IsIndecomposableRoot L f y) (hne : x ≠ y) :
    L.obj.obj.pairing x y = 0 ∨ L.obj.obj.pairing x y = 1 := by
  have hx2 := pairing_self_of_mem_positiveRoots hL hE hx.1
  have hy2 := pairing_self_of_mem_positiveRoots hL hE hy.1
  have hfx := hx.1.2
  have hfy := hy.1.2
  have hopp : x ≠ -y := by
    intro hv
    rw [hv, map_neg] at hfx
    omega
  have hbound := L.abs_pairing_le_one_of_isNegativeDefinite hL hx2 hy2 hne hopp
  rw [abs_le] at hbound
  have hcases : L.obj.obj.pairing x y = -1 ∨ L.obj.obj.pairing x y = 0 ∨
      L.obj.obj.pairing x y = 1 := by omega
  rcases hcases with hv | hv | hv
  · exfalso
    have hw : L.obj.obj.pairing (x - y) (x - y) = -2 := by
      rw [pairing_sub_self, hx2, hy2, hv]; ring
    have hwroot : IsRoot L.obj (x - y) := Or.inr (Or.inl hw)
    have hfxy : f (x - y) = f x - f y := map_sub f x y
    have hfyx : f (y - x) = f y - f x := map_sub f y x
    rcases lt_or_gt_of_ne (hf _ hwroot) with hlt | hgt
    · refine hy.2 (y - x) ⟨?_, by omega⟩ x hx.1 (by abel)
      have hyx : y - x = -(x - y) := by abel
      rw [hyx]
      exact L.isRoot_neg hwroot
    · exact hx.2 (x - y) ⟨hwroot, hgt⟩ y hy.1 (by abel)
  · exact Or.inl hv
  · exact Or.inr hv

/-- Spanning, in the form the induction produces. Every positive root lies in the span of the
indecomposable positive roots: a decomposable one splits into two positive roots on which `f`
takes strictly smaller values. -/
theorem mem_span_simpleRootSet {f : L.obj.obj.carrier →ₗ[ℤ] ℤ} {x : L.obj.obj.carrier}
    (hx : x ∈ positiveRoots L f) :
    x ∈ Submodule.span ℤ (simpleRootSet L f) := by
  have key : ∀ n : ℕ, ∀ x ∈ positiveRoots L f, (f x).toNat ≤ n →
      x ∈ Submodule.span ℤ (simpleRootSet L f) := by
    intro n
    induction n with
    | zero =>
      intro x hx hn
      have hpos := hx.2
      omega
    | succ n ih =>
      intro x hx hn
      by_cases hind : IsIndecomposableRoot L f x
      · exact Submodule.subset_span hind
      · have hdec : ∃ y ∈ positiveRoots L f, ∃ z ∈ positiveRoots L f, x = y + z := by
          by_contra hcon
          exact hind ⟨hx, fun y hy z hz hxyz => hcon ⟨y, hy, z, hz, hxyz⟩⟩
        obtain ⟨y, hy, z, hz, rfl⟩ := hdec
        have hfyz : f (y + z) = f y + f z := map_add f y z
        have hy2 := hy.2
        have hz2 := hz.2
        exact Submodule.add_mem _ (ih y hy (by omega)) (ih z hz (by omega))
  exact key (f x).toNat x hx le_rfl

/-- The indecomposable positive roots span the lattice, since the roots do and every root is a
positive root or the negative of one. -/
theorem span_simpleRootSet_eq_top {f : L.obj.obj.carrier →ₗ[ℤ] ℤ}
    (hf : ∀ x ∈ L.rootSet, f x ≠ 0)
    (hspan : Submodule.span ℤ L.rootSet = ⊤) :
    Submodule.span ℤ (simpleRootSet L f) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← hspan, Submodule.span_le]
  intro x hx
  rcases L.mem_positiveRoots_or_neg f hf hx with hv | hv
  · exact mem_span_simpleRootSet hv
  · have hmem := mem_span_simpleRootSet hv
    simpa using Submodule.neg_mem _ hmem

/-- Independence of the indecomposable positive roots. A vanishing integer combination splits
into a positive part and a negative part that are equal as vectors, so the self-pairing of the
positive part is a sum of products of non-negative pairings. Negative definiteness makes that
part zero, and then `f` forces both parts to be empty. -/
theorem linearIndepOn_simpleRootSet (hL : IsNegativeDefiniteLattice L) (hE : IsEven L.obj)
    {f : L.obj.obj.carrier →ₗ[ℤ] ℤ} (hf : ∀ x ∈ L.rootSet, f x ≠ 0) :
    LinearIndepOn ℤ id (simpleRootSet L f) := by
  classical
  refine linearIndependent_iff'.mpr ?_
  intro S g hsum i hi
  have hsum' : ∑ y ∈ S, g y • (y : L.obj.obj.carrier) = 0 := by
    simp only [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id]
    simpa using hsum
  have hpos : ∀ y : simpleRootSet L f, 0 < f (y : L.obj.obj.carrier) := fun y => y.2.1.2
  have hnn : ∀ y z : simpleRootSet L f, y ≠ z →
      0 ≤ L.obj.obj.pairing (y : L.obj.obj.carrier) z := by
    intro y z hyz
    rcases pairing_eq_zero_or_one_of_isIndecomposableRoot hL hE hf y.2 z.2
      (Subtype.coe_injective.ne hyz) with hv | hv <;> omega
  have hNsub : ∑ y ∈ S.filter (fun y => g y < 0), g y • (y : L.obj.obj.carrier)
      = ∑ y ∈ S.filter (fun y => ¬ 0 < g y), g y • (y : L.obj.obj.carrier) := by
    refine Finset.sum_subset (fun y hy => ?_) (fun y hy hy' => ?_)
    · simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, by omega⟩
    · simp only [Finset.mem_filter, not_and, not_lt] at hy hy'
      have hzero : g y = 0 := le_antisymm (by omega) (hy' hy.1)
      rw [hzero, zero_smul]
  have hsplit : ∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier)
      + ∑ y ∈ S.filter (fun y => g y < 0), g y • (y : L.obj.obj.carrier) = 0 := by
    rw [hNsub, Finset.sum_filter_add_sum_filter_not]
    exact hsum'
  have hvw : ∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier)
      = ∑ y ∈ S.filter (fun y => g y < 0), (-g y) • (y : L.obj.obj.carrier) := by
    simp only [neg_zsmul, Finset.sum_neg_distrib]
    exact eq_neg_iff_add_eq_zero.mpr hsplit
  have hcross : L.obj.obj.pairing
        (∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier))
        (∑ z ∈ S.filter (fun y => g y < 0), (-g z) • (z : L.obj.obj.carrier))
      = ∑ y ∈ S.filter (fun y => 0 < g y), ∑ z ∈ S.filter (fun y => g y < 0),
          g y * (-g z) * L.obj.obj.pairing (y : L.obj.obj.carrier) z := by
    rw [pairing_sum_left]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [pairing_sum_right]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [BilinModuleCat.pairing_zsmul_left, BilinModuleCat.pairing_zsmul_right, smul_eq_mul,
      smul_eq_mul, mul_assoc]
  have hnonneg : 0 ≤ L.obj.obj.pairing
      (∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier))
      (∑ z ∈ S.filter (fun y => g y < 0), (-g z) • (z : L.obj.obj.carrier)) := by
    rw [hcross]
    refine Finset.sum_nonneg fun y hy => Finset.sum_nonneg fun z hz => ?_
    simp only [Finset.mem_filter] at hy hz
    have hyz : y ≠ z := by
      intro hv
      rw [hv] at hy
      omega
    exact mul_nonneg (mul_nonneg (by omega) (by omega)) (hnn y z hyz)
  have heq : L.obj.obj.pairing
        (∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier))
        (∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier))
      = L.obj.obj.pairing
        (∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier))
        (∑ z ∈ S.filter (fun y => g y < 0), (-g z) • (z : L.obj.obj.carrier)) := by
    rw [← hvw]
  have hv0 : ∑ y ∈ S.filter (fun y => 0 < g y), g y • (y : L.obj.obj.carrier) = 0 := by
    by_contra hne
    have hlt := L.pairing_self_neg hL hne
    rw [heq] at hlt
    omega
  have hw0 : ∑ y ∈ S.filter (fun y => g y < 0), (-g y) • (y : L.obj.obj.carrier) = 0 := by
    rw [← hvw, hv0]
  have hP0 : S.filter (fun y => 0 < g y) = ∅ := by
    by_contra hPne
    obtain ⟨y0, hy0⟩ := Finset.nonempty_of_ne_empty hPne
    have hfv : ∑ y ∈ S.filter (fun y => 0 < g y), g y * f (y : L.obj.obj.carrier) = 0 := by
      have hmap := congrArg f hv0
      rw [map_sum, map_zero] at hmap
      refine hmap.symm.trans (Finset.sum_congr rfl fun y _ => ?_) |>.symm
      rw [map_zsmul, smul_eq_mul]
    have hterm : ∀ y ∈ S.filter (fun y => 0 < g y), 0 < g y * f (y : L.obj.obj.carrier) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      exact mul_pos hy.2 (hpos y)
    have := Finset.sum_pos hterm ⟨y0, hy0⟩
    omega
  have hN0 : S.filter (fun y => g y < 0) = ∅ := by
    by_contra hNne
    obtain ⟨y0, hy0⟩ := Finset.nonempty_of_ne_empty hNne
    have hfv : ∑ y ∈ S.filter (fun y => g y < 0), (-g y) * f (y : L.obj.obj.carrier) = 0 := by
      have hmap := congrArg f hw0
      rw [map_sum, map_zero] at hmap
      refine hmap.symm.trans (Finset.sum_congr rfl fun y _ => ?_) |>.symm
      rw [map_zsmul, smul_eq_mul]
    have hterm : ∀ y ∈ S.filter (fun y => g y < 0), 0 < (-g y) * f (y : L.obj.obj.carrier) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      exact mul_pos (by omega) (hpos y)
    have := Finset.sum_pos hterm ⟨y0, hy0⟩
    omega
  by_contra hgi
  rcases lt_trichotomy (g i) 0 with hv | hv | hv
  · have hmem : i ∈ S.filter (fun y => g y < 0) := Finset.mem_filter.mpr ⟨hi, hv⟩
    rw [hN0] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  · exact hgi hv
  · have hmem : i ∈ S.filter (fun y => 0 < g y) := Finset.mem_filter.mpr ⟨hi, hv⟩
    rw [hP0] at hmem
    exact absurd hmem (Finset.notMem_empty i)

/-- The indecomposable positive roots of an even negative definite lattice whose roots span form
a base of simple roots. -/
theorem isRootBase_simpleRootSet (hL : IsNegativeDefiniteLattice L) (hE : IsEven L.obj)
    {f : L.obj.obj.carrier →ₗ[ℤ] ℤ} (hf : ∀ x ∈ L.rootSet, f x ≠ 0)
    (hspan : Submodule.span ℤ L.rootSet = ⊤) : IsRootBase L (simpleRootSet L f) where
  pairing_self _ hx := pairing_self_of_mem_positiveRoots hL hE hx.1
  pairing_ne _ hx _ hy hne := pairing_eq_zero_or_one_of_isIndecomposableRoot hL hE hf hx hy hne
  linearIndepOn := linearIndepOn_simpleRootSet hL hE hf
  span_eq_top := span_simpleRootSet_eq_top hf hspan

/-- Existence of a base of simple roots for an even negative definite lattice whose roots span
it. -/
theorem exists_isRootBase_of_span (hL : IsNegativeDefiniteLattice L) (hE : IsEven L.obj)
    (hspan : Submodule.span ℤ L.rootSet = ⊤) :
    ∃ B : Set L.obj.obj.carrier, IsRootBase L B := by
  obtain ⟨f, hf⟩ := L.exists_forall_root_apply_ne_zero (Or.inr hL)
  exact ⟨simpleRootSet L f, isRootBase_simpleRootSet hL hE hf hspan⟩

end FiniteProjectiveLatticeCat

/-- Every even negative definite root lattice has a base of simple roots. The rank of the
lattice is therefore the number of simple roots, and the shape restrictions of `RootBase.lean`
apply to a graph that is now known to exist. -/
theorem exists_isRootBase (L : RootLatticeCat)
    (hL : IsNegativeDefiniteLattice L.obj.obj) (hE : IsEven L.obj.obj.obj) :
    ∃ B : Set L.obj.obj.obj.obj.carrier, FiniteProjectiveLatticeCat.IsRootBase L.obj.obj B :=
  FiniteProjectiveLatticeCat.exists_isRootBase_of_span hL hE L.property

end LeanCategories.Lattices.Valued
