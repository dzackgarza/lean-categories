/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.SimplyLaced
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Bases of simple roots

`SimplyLaced.lean` reduces the roots of an even negative definite lattice to the single level
set `-2` and bounds the pairing of two roots that are neither equal nor opposite. The bound
stops short of a diagram because the full root set carries `-x` next to every `x`, and
`b(x, -x) = 2`. The classification statements are about a subset that omits one root of each
opposite pair. This file introduces that subset.

* `IsRootBase L B` is the predicate on a set `B` of vectors: every member has self-pairing `-2`,
  distinct members pair in `{0, 1}`, and `B` is a `ℤ`-basis of the lattice. Since a base spans
  and is independent, `IsRootBase.basis` presents it as a `Module.Basis`, so the rank of the
  lattice is the number of simple roots. `IsRootBase.neg_notMem` derives the absence of opposite
  pairs, which is why the condition is not carried as a separate field: `b(x, -x) = 2` already
  violates the pairing condition.
* `rootBaseGraph` is the graph of a base, and `IsRootBase.pairing_eq_one_of_adj` is the simple
  lacing statement, now with no side hypothesis: every edge carries pairing exactly `1`.
* `IsRootBase.sum_smul_pairing_neg` is the one argument the shape restrictions run on. An
  integer combination of members of a base with some nonzero coefficient is a nonzero vector, so
  its self-pairing is negative, and expanding that self-pairing as a double sum turns a
  configuration of a graph into an inequality between integers.

  - Coefficients all `1` on a cycle give `IsRootBase.isAcyclic_rootBaseGraph`: the sum around a
    cycle would be isotropic, since each vertex of a cycle contributes `-2` for itself and `1`
    for each of its two neighbours in the cycle.
  - Coefficient `2` at a vertex and `1` at each neighbour gives
    `IsRootBase.ncard_neighborSet_le_three`: the vector `2x + ∑ N` over a set `N` of `d`
    pairwise orthogonal neighbours has self-pairing `2d - 8`.
  - `IsRootBase.not_adj_triangle` is the triangle case, and is what makes the neighbours of a
    vertex pairwise orthogonal.

Evenness does not appear as a hypothesis here: `IsRootBase` asks for the value `-2` outright,
which is what `isRoot_iff_pairing_eq_neg_two` supplies for an even negative definite lattice.
`IsRootBase.of_basis` builds a base from a presentation by a Gram matrix, which is the form the
standard lattices of `Standard.lean` come in.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- The pairing is additive on a finite sum in its left argument. -/
theorem pairing_sum_left (L : FiniteProjectiveLatticeCat ℤ ℤ) {ι : Type*} (s : Finset ι)
    (f : ι → L.obj.obj.carrier) (y : L.obj.obj.carrier) :
    L.obj.obj.pairing (∑ i ∈ s, f i) y = ∑ i ∈ s, L.obj.obj.pairing (f i) y := by
  simp only [← BilinModuleCat.bilinMap_apply, map_sum, LinearMap.sum_apply]

/-- The pairing is additive on a finite sum in its right argument. -/
theorem pairing_sum_right (L : FiniteProjectiveLatticeCat ℤ ℤ) {ι : Type*} (s : Finset ι)
    (f : ι → L.obj.obj.carrier) (y : L.obj.obj.carrier) :
    L.obj.obj.pairing y (∑ i ∈ s, f i) = ∑ i ∈ s, L.obj.obj.pairing y (f i) := by
  simp only [← BilinModuleCat.bilinMap_apply, map_sum]

/-- The self-pairing of a finite sum expands as the double sum of the pairings of its terms. -/
theorem pairing_sum_sum (L : FiniteProjectiveLatticeCat ℤ ℤ) {ι : Type*} (S : Finset ι)
    (f : ι → L.obj.obj.carrier) :
    L.obj.obj.pairing (∑ y ∈ S, f y) (∑ z ∈ S, f z) =
      ∑ y ∈ S, ∑ z ∈ S, L.obj.obj.pairing (f y) (f z) := by
  rw [pairing_sum_left]
  exact Finset.sum_congr rfl fun y _ => pairing_sum_right L S f (f y)

/-- The pairing of an integral lattice is symmetric. -/
theorem pairing_comm (L : FiniteProjectiveLatticeCat ℤ ℤ) (x y : L.obj.obj.carrier) :
    L.obj.obj.pairing x y = L.obj.obj.pairing y x :=
  L.obj.property.2 x y

/-- The pairing negates in its right argument. -/
theorem pairing_neg_right (L : FiniteProjectiveLatticeCat ℤ ℤ) (x y : L.obj.obj.carrier) :
    L.obj.obj.pairing x (-y) = -L.obj.obj.pairing x y := by
  simp only [← BilinModuleCat.bilinMap_apply, map_neg]

/-- A base of simple roots of a lattice: a linearly independent spanning set of vectors of
self-pairing `-2` whose distinct members pair in `{0, 1}`. In the negative definite convention
of this repository the classical obtuseness condition on simple roots reads as non-negativity
of the pairing, and the Cauchy-Schwarz bound of `RootLattice.lean` caps it at `1`. -/
structure IsRootBase (L : FiniteProjectiveLatticeCat ℤ ℤ) (B : Set L.obj.obj.carrier) : Prop where
  /-- Every member of a base is a root of the single level set `-2`. -/
  pairing_self : ∀ x ∈ B, L.obj.obj.pairing x x = -2
  /-- Two distinct members of a base pair in `{0, 1}`. -/
  pairing_ne : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
    L.obj.obj.pairing x y = 0 ∨ L.obj.obj.pairing x y = 1
  /-- A base is linearly independent. -/
  linearIndepOn : LinearIndepOn ℤ id B
  /-- A base spans the lattice. -/
  span_eq_top : Submodule.span ℤ B = ⊤

namespace IsRootBase

variable {B : Set L.obj.obj.carrier}

/-- Every member of a base is a root. -/
theorem isRoot (hB : IsRootBase L B) {x : L.obj.obj.carrier} (hx : x ∈ B) : IsRoot L.obj x :=
  Or.inr (Or.inl (hB.pairing_self x hx))

/-- No member of a base is zero. -/
theorem ne_zero (hB : IsRootBase L B) {x : L.obj.obj.carrier} (hx : x ∈ B) : x ≠ 0 := by
  rintro rfl
  simpa using hB.pairing_self 0 hx

/-- No member of a base is its own negative: the two self-pairings would be `-2` and `2`. -/
theorem ne_neg_self (hB : IsRootBase L B) {x : L.obj.obj.carrier} (hx : x ∈ B) : x ≠ -x := by
  intro h
  have h2 : L.obj.obj.pairing x (-x) = -2 := by rw [← h]; exact hB.pairing_self x hx
  rw [pairing_neg_right, hB.pairing_self x hx] at h2
  omega

/-- A base contains no opposite pair. This is the property that fails on the full root set and
that makes the graph of a base simply laced without extra hypotheses. -/
theorem neg_notMem (hB : IsRootBase L B) {x : L.obj.obj.carrier} (hx : x ∈ B) : -x ∉ B := by
  intro hnx
  have hpair : L.obj.obj.pairing x (-x) = 2 := by
    rw [pairing_neg_right, hB.pairing_self x hx]; ring
  rcases hB.pairing_ne x hx (-x) hnx (hB.ne_neg_self hx) with h | h <;> omega

/-- The pairing of two distinct members of a base is not negative, and is at most `1`. -/
theorem pairing_nonneg (hB : IsRootBase L B) {x y : L.obj.obj.carrier} (hx : x ∈ B)
    (hy : y ∈ B) (hne : x ≠ y) : 0 ≤ L.obj.obj.pairing x y := by
  rcases hB.pairing_ne x hx y hy hne with h | h <;> omega

/-- A base of a lattice is a `ℤ`-basis of it: that is what independence and spanning say
together. The rank of the lattice is therefore the number of simple roots. -/
noncomputable def basis (hB : IsRootBase L B) : Module.Basis B ℤ L.obj.obj.carrier :=
  Module.Basis.mk hB.linearIndepOn
    (by simp only [id_eq, Subtype.range_coe]; exact hB.span_eq_top.ge)

/-- A base is finite: it is linearly independent in a module of finite rank. -/
theorem finite (hB : IsRootBase L B) : B.Finite := by
  haveI : Module.Finite ℤ L.obj.obj.carrier := L.property
  haveI := hB.linearIndepOn.finite_of_isNoetherian
  exact Set.toFinite B

/-- A linear combination of members of a base with one nonzero coefficient is nonzero. -/
theorem sum_smul_ne_zero (hB : IsRootBase L B) {S : Finset B} (g : B → ℤ) {x : B}
    (hx : x ∈ S) (hgx : g x ≠ 0) : ∑ y ∈ S, g y • (y : L.obj.obj.carrier) ≠ 0 := by
  intro h
  refine hgx (linearIndependent_iff'.mp hB.linearIndepOn S g ?_ x hx)
  simp only [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id] at h ⊢
  exact h

/-- A nonempty finite subset of a base has nonzero sum. -/
theorem sum_ne_zero (hB : IsRootBase L B) {S : Finset B} (hS : S.Nonempty) :
    ∑ y ∈ S, (y : L.obj.obj.carrier) ≠ 0 := by
  obtain ⟨x, hx⟩ := hS
  have h := hB.sum_smul_ne_zero (fun _ => (1 : ℤ)) hx one_ne_zero
  simpa using h

end IsRootBase

/-- The graph of a base of simple roots: two distinct members are joined when they are not
orthogonal. -/
def rootBaseGraph (L : FiniteProjectiveLatticeCat ℤ ℤ) (B : Set L.obj.obj.carrier) :
    SimpleGraph B where
  Adj x y := x ≠ y ∧ L.obj.obj.pairing x y ≠ 0
  symm := ⟨fun x y hxy =>
    ⟨hxy.1.symm, fun h => hxy.2 (by rw [pairing_comm L (x : L.obj.obj.carrier) y, h])⟩⟩
  loopless := ⟨fun _ hx => hx.1 rfl⟩

/-- Adjacency in the graph of a base is non-orthogonality of distinct members. -/
@[simp]
theorem rootBaseGraph_adj {B : Set L.obj.obj.carrier} {x y : B} :
    (rootBaseGraph L B).Adj x y ↔ x ≠ y ∧ L.obj.obj.pairing x y ≠ 0 :=
  Iff.rfl

namespace IsRootBase

variable {B : Set L.obj.obj.carrier}

/-- The graph of a base is simply laced, with no hypothesis beyond `IsRootBase`. Every edge
carries pairing exactly `1`, because a base contains no opposite pair. -/
theorem pairing_eq_one_of_adj (hB : IsRootBase L B) {x y : B}
    (hadj : (rootBaseGraph L B).Adj x y) : L.obj.obj.pairing x y = 1 :=
  (hB.pairing_ne x x.2 y y.2 (Subtype.coe_injective.ne hadj.1)).resolve_left hadj.2

/-- The norm argument in its general form, and the single engine behind the shape restrictions
on the graph of a base. Any integer combination of members of a base with one nonzero
coefficient is a nonzero vector, so its self-pairing, written out as a double sum, is
negative. -/
theorem sum_smul_pairing_neg (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B)
    {S : Finset B} (g : B → ℤ) {x : B} (hx : x ∈ S) (hgx : g x ≠ 0) :
    ∑ y ∈ S, ∑ z ∈ S, g y * g z * L.obj.obj.pairing (y : L.obj.obj.carrier) z < 0 := by
  have hneg := L.pairing_self_neg hL (hB.sum_smul_ne_zero g hx hgx)
  rw [pairing_sum_sum] at hneg
  calc ∑ y ∈ S, ∑ z ∈ S, g y * g z * L.obj.obj.pairing (y : L.obj.obj.carrier) z
      = ∑ y ∈ S, ∑ z ∈ S,
          L.obj.obj.pairing (g y • (y : L.obj.obj.carrier)) (g z • (z : L.obj.obj.carrier)) := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
        rw [BilinModuleCat.pairing_zsmul_left, BilinModuleCat.pairing_zsmul_right, smul_eq_mul,
          smul_eq_mul, mul_assoc]
    _ < 0 := hneg

/-- The counting bound behind acyclicity. The double sum of the pairings over a nonempty finite
subset of a base is negative, because the sum of the members is a nonzero vector of a negative
definite lattice. -/
theorem sum_sum_pairing_neg (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B)
    {S : Finset B} (hS : S.Nonempty) :
    ∑ y ∈ S, ∑ z ∈ S, L.obj.obj.pairing (y : L.obj.obj.carrier) z < 0 := by
  obtain ⟨x, hx⟩ := hS
  simpa using hB.sum_smul_pairing_neg hL (fun _ => (1 : ℤ)) hx one_ne_zero

/-- No nonempty finite subset of a base has every member pairing to a non-negative total against
the whole subset. Since the self-pairing contributes `-2`, the condition says that every member
pairs to a total of at least `2` against the others, which a cycle of the graph of a base would
satisfy: each of its members pairs to `1` with its two neighbours in the cycle and to a
non-negative value with the rest. -/
theorem not_forall_sum_nonneg (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B)
    {S : Finset B} (hS : S.Nonempty)
    (h : ∀ y ∈ S, 0 ≤ ∑ z ∈ S, L.obj.obj.pairing (y : L.obj.obj.carrier) z) : False :=
  absurd (Finset.sum_nonneg h) (hB.sum_sum_pairing_neg hL hS).not_ge

/-- The graph of a base has no triangle: three members pairing to `1` in every pair sum to zero,
which linear independence forbids. -/
theorem not_adj_triangle (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B) {x y z : B}
    (hxy : (rootBaseGraph L B).Adj x y) (hxz : (rootBaseGraph L B).Adj x z)
    (hyz : (rootBaseGraph L B).Adj y z) : False := by
  classical
  have hsum := L.add_add_eq_zero_of_pairing_triangle hL (hB.pairing_self x x.2)
    (hB.pairing_self y y.2) (hB.pairing_self z z.2) (hB.pairing_eq_one_of_adj hxy)
    (hB.pairing_eq_one_of_adj hxz) (hB.pairing_eq_one_of_adj hyz)
  refine hB.sum_ne_zero (S := ({x, y, z} : Finset B)) ⟨x, by simp⟩ ?_
  rw [Finset.sum_insert (by simp [hxy.1, hxz.1]), Finset.sum_insert (by simp [hyz.1]),
    Finset.sum_singleton, ← add_assoc]
  exact hsum

/-- Acyclicity. The graph of a base of an even negative definite lattice has no cycle. Every
vertex of a cycle has two distinct neighbours inside the cycle, so it pairs to at least `2`
with the rest of the support, and `not_forall_sum_nonneg` excludes that. -/
theorem isAcyclic_rootBaseGraph (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B) :
    (rootBaseGraph L B).IsAcyclic := by
  classical
  intro v p hp
  refine hB.not_forall_sum_nonneg hL (S := p.support.toFinset) ⟨v, by simp⟩ ?_
  intro y hyS
  rw [List.mem_toFinset] at hyS
  obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp (hp.ncard_neighborSet_toSubgraph_eq_two hyS)
  have hya : p.toSubgraph.Adj y a := by
    have : a ∈ p.toSubgraph.neighborSet y := by rw [hset]; exact Set.mem_insert a {b}
    exact this
  have hyb : p.toSubgraph.Adj y b := by
    have : b ∈ p.toSubgraph.neighborSet y := by rw [hset]; exact Set.mem_insert_of_mem a rfl
    exact this
  have hmem : ∀ {w : B}, p.toSubgraph.Adj y w → w ∈ p.support.toFinset := by
    intro w hw
    rw [List.mem_toFinset, ← SimpleGraph.Walk.mem_verts_toSubgraph]
    exact hw.symm.fst_mem
  have hsub : ({a, b} : Finset B) ⊆ p.support.toFinset.erase y := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨(hya.adj_sub.ne).symm, hmem hya⟩
    · exact Finset.mem_erase.mpr ⟨(hyb.adj_sub.ne).symm, hmem hyb⟩
  have hpair : ∀ z ∈ p.support.toFinset.erase y,
      0 ≤ L.obj.obj.pairing (y : L.obj.obj.carrier) z := fun z hz =>
    hB.pairing_nonneg y.2 z.2
      (Subtype.coe_injective.ne (Finset.ne_of_mem_erase hz).symm)
  have htwo : (2 : ℤ) ≤ ∑ z ∈ p.support.toFinset.erase y,
      L.obj.obj.pairing (y : L.obj.obj.carrier) z := by
    calc (2 : ℤ) = ∑ z ∈ ({a, b} : Finset B), L.obj.obj.pairing (y : L.obj.obj.carrier) z := by
          rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton,
            hB.pairing_eq_one_of_adj hya.adj_sub, hB.pairing_eq_one_of_adj hyb.adj_sub]
          ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun z hz _ => hpair z hz
  rw [← Finset.add_sum_erase _ _ (List.mem_toFinset.mpr hyS), hB.pairing_self y y.2]
  omega

/-- The degree bound. A member `x` of a base has at most three neighbours. The hypotheses are
the ones the graph of a base supplies: `N` is a finite set of members pairing to `1` with `x`
and to `0` with one another, the second condition coming from the absence of triangles. The
vector `2x + ∑ N` has self-pairing `2 * N.card - 8`, which negative definiteness forces to be
negative. -/
theorem card_le_three (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B) {x : B}
    {N : Finset B} (hxN : x ∉ N)
    (hx : ∀ y ∈ N, L.obj.obj.pairing (x : L.obj.obj.carrier) y = 1)
    (horth : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → L.obj.obj.pairing (y : L.obj.obj.carrier) z = 0) :
    N.card ≤ 3 := by
  classical
  have hsne : (2 : ℤ) • (x : L.obj.obj.carrier) + ∑ y ∈ N, (y : L.obj.obj.carrier) ≠ 0 := by
    have h := hB.sum_smul_ne_zero (S := insert x N) (fun y => if y = x then (2 : ℤ) else 1)
      (Finset.mem_insert_self x N) (by simp)
    have hcongr : ∀ y ∈ N, (if y = x then (2 : ℤ) else 1) • (y : L.obj.obj.carrier) = y := by
      intro y hy
      rw [if_neg (by rintro rfl; exact hxN hy), one_zsmul]
    rwa [Finset.sum_insert hxN, if_pos rfl, Finset.sum_congr rfl hcongr] at h
  have hxv : L.obj.obj.pairing (x : L.obj.obj.carrier) (∑ y ∈ N, (y : L.obj.obj.carrier)) =
      (N.card : ℤ) := by
    rw [pairing_sum_right, Finset.sum_congr rfl hx, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hvv : L.obj.obj.pairing (∑ y ∈ N, (y : L.obj.obj.carrier))
      (∑ y ∈ N, (y : L.obj.obj.carrier)) = -2 * (N.card : ℤ) := by
    rw [pairing_sum_sum]
    have hrow : ∀ y ∈ N, ∑ z ∈ N, L.obj.obj.pairing (y : L.obj.obj.carrier) z = -2 := by
      intro y hy
      have hzero : ∑ z ∈ N.erase y, L.obj.obj.pairing (y : L.obj.obj.carrier) z = 0 :=
        Finset.sum_eq_zero fun z hz =>
          horth y hy z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz).symm
      rw [← Finset.add_sum_erase _ _ hy, hB.pairing_self y y.2, hzero, add_zero]
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
    ring
  have hself := L.pairing_self_neg hL hsne
  rw [pairing_add_self, BilinModuleCat.pairing_zsmul_left, BilinModuleCat.pairing_zsmul_right,
    hB.pairing_self x x.2, BilinModuleCat.pairing_zsmul_left, hxv, hvv] at hself
  simp only [smul_eq_mul] at hself
  omega

/-- The degree bound on the graph of a base: no member of a base has more than three neighbours.
The neighbours of a member are pairwise orthogonal because the graph has no triangle, so
`card_le_three` applies to them. -/
theorem ncard_neighborSet_le_three (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B)
    (x : B) : ((rootBaseGraph L B).neighborSet x).ncard ≤ 3 := by
  classical
  haveI : Module.Finite ℤ L.obj.obj.carrier := L.property
  haveI := hB.linearIndepOn.finite_of_isNoetherian
  have hfin : ((rootBaseGraph L B).neighborSet x).Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine hB.card_le_three hL (x := x) (fun hx => ?_) (fun y hy => ?_) (fun y hy z hz hyz => ?_)
  · exact (rootBaseGraph L B).irrefl (hfin.mem_toFinset.mp hx)
  · exact hB.pairing_eq_one_of_adj (hfin.mem_toFinset.mp hy)
  · by_contra h
    exact hB.not_adj_triangle hL (hfin.mem_toFinset.mp hy) (hfin.mem_toFinset.mp hz) ⟨hyz, h⟩

/-- A `ℤ`-basis of vectors of self-pairing `-2` whose distinct members pair in `{0, 1}` is a base
of simple roots. This is the criterion that the standard presentations of the ADE lattices by a
Gram matrix satisfy, and it shows the predicate is inhabited. -/
theorem of_basis {ι : Type*} (b : Module.Basis ι ℤ L.obj.obj.carrier)
    (hself : ∀ i, L.obj.obj.pairing (b i) (b i) = -2)
    (hpair : ∀ i j, i ≠ j →
      L.obj.obj.pairing (b i) (b j) = 0 ∨ L.obj.obj.pairing (b i) (b j) = 1) :
    IsRootBase L (Set.range b) where
  pairing_self := by rintro _ ⟨i, rfl⟩; exact hself i
  pairing_ne := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hpair i j fun h => hne (congrArg b h)
  linearIndepOn := b.linearIndependent.linearIndepOn_id
  span_eq_top := b.span_eq

end IsRootBase

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
