/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.RootBase
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

/-!
# Shape bounds on the graph of a base of simple roots

`RootBase.lean` supplies the norm argument `IsRootBase.sum_smul_pairing_neg`, and reads off from
it that the graph of a base is acyclic and has degree at most three. This file adds the next
shape bound: a connected diagram carries at most one vertex of degree three.

* `isChordless_of_isPath` is the graph-theoretic input. In an acyclic graph an edge between two
  vertices of a path is one of the edges of that path. Mathlib defines `SimpleGraph.Walk.
  IsChordless` and translates it into `Subgraph.IsInduced` through
  `SimpleGraph.Walk.isInduced_toSubgraph`, but does not derive it from acyclicity.
* `eq_start_of_adj_of_notMem_support` is the form of that input the norm argument actually uses:
  a vertex outside a path that is adjacent to the start of the path is adjacent to no other
  vertex of the path. `not_adj_of_ends` is the two-sided version, for one vertex hanging off
  each end.
* `IsRootBase.pairing_sum_support_eq_one` and `IsRootBase.pairing_sum_support_self` are the two
  lattice computations. Writing `T` for the sum of the vertices of a path, a member of the base
  outside the path and adjacent to its start pairs to `1` with `T`, and `T` pairs to `-2` with
  itself, whatever the length of the path. The second follows from the first by induction along
  the path, since the head of a path is a vertex outside its tail adjacent to the start of that
  tail.
* `IsRootBase.no_two_branch_nodes` is the bound. Two vertices of degree at least three in one
  connected component are equal. The vector `a + a' + 2T + b + b'`, for `T` the sum of the
  vertices of the path between the two branch nodes and `a, a'` and `b, b'` the further
  neighbours of the two ends, has self-pairing `(-8) + 2 * 8 + (-8) = 0`, and a nonzero vector
  of a negative definite lattice has negative self-pairing.
  `IsRootBase.subsingleton_setOf_three_le_ncard_neighborSet` is the reading of the bound a
  preconnected diagram gives: at most one vertex of degree at least three, so with the degree
  bound of `RootBase.lean` a connected diagram is a path or has exactly one vertex of degree
  exactly three.

The bound is stated for two branch nodes joined by a walk, not for the whole graph: an
orthogonal direct sum of two copies of the `D` diagram is a base with two branch nodes, so a
reachability hypothesis is not removable.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

section AcyclicWalk

variable {V : Type*} {G : SimpleGraph V}

/-- In an acyclic graph a path has no chord: an edge of the graph between two vertices of the
path is one of the edges of the path. Mathlib has the predicate `SimpleGraph.Walk.IsChordless`
and its translation into `SimpleGraph.Subgraph.IsInduced`, but not this implication. -/
theorem isChordless_of_isPath (hG : G.IsAcyclic) {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.IsChordless := by
  classical
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro s t hs ht hadj
  have hmem : t ∈ (p.takeUntil s hs).support ∨ t ∈ (p.dropUntil s hs).support := by
    rw [← SimpleGraph.Walk.mem_support_append_iff]
    rw [p.take_spec hs]
    exact ht
  rcases hmem with htm | htm
  · have hr : ((p.takeUntil s hs).reverse).IsPath := (hp.takeUntil hs).reverse
    have htr : t ∈ ((p.takeUntil s hs).reverse).support := by
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
      exact htm
    have hnil : ¬ ((p.takeUntil s hs).reverse).Nil := by
      intro hn
      rw [SimpleGraph.Walk.nil_iff_support_eq.mp hn, List.mem_singleton] at htr
      exact hadj.ne htr.symm
    have hsnd := hG.eq_snd_of_adj_start hr hadj htr
    have hedge := SimpleGraph.Walk.mk_start_snd_mem_edges hnil
    rw [← hsnd, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hedge
    exact p.edges_takeUntil_subset_edges hs hedge
  · have hr : (p.dropUntil s hs).IsPath := hp.dropUntil hs
    have hnil : ¬ (p.dropUntil s hs).Nil := by
      intro hn
      rw [SimpleGraph.Walk.nil_iff_support_eq.mp hn, List.mem_singleton] at htm
      exact hadj.ne htm.symm
    have hsnd := hG.eq_snd_of_adj_start hr hadj htm
    have hedge := SimpleGraph.Walk.mk_start_snd_mem_edges hnil
    rw [← hsnd] at hedge
    exact p.edges_dropUntil_subset_edges hs hedge

/-- In an acyclic graph a vertex outside a path that is adjacent to the start of the path is
adjacent to no other vertex of the path. Adjoining the vertex to the front of the path produces
a path, and `SimpleGraph.IsAcyclic.eq_snd_of_adj_start` applies to that longer path. -/
theorem eq_start_of_adj_of_notMem_support (hG : G.IsAcyclic) {u v a t : V} {p : G.Walk u v}
    (hp : p.IsPath) (ha : a ∉ p.support) (hau : G.Adj a u) (hat : G.Adj a t)
    (ht : t ∈ p.support) : t = u := by
  have hq : (SimpleGraph.Walk.cons hau p).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff hau p).mpr ⟨hp, ha⟩
  have htq : t ∈ (SimpleGraph.Walk.cons hau p).support := by
    rw [SimpleGraph.Walk.support_cons]
    exact List.mem_cons_of_mem a ht
  have := hG.eq_snd_of_adj_start hq hat htq
  rwa [SimpleGraph.Walk.snd_cons] at this

/-- Two vertices outside a path in an acyclic graph, one adjacent to each end, are distinct and
not adjacent, as soon as the two ends are distinct. -/
theorem not_adj_of_ends (hG : G.IsAcyclic) {u v c d : V} {p : G.Walk u v} (hp : p.IsPath)
    (huv : u ≠ v) (hc : c ∉ p.support) (hcu : G.Adj c u) (hd : d ∉ p.support)
    (hdv : G.Adj v d) : c ≠ d ∧ ¬ G.Adj c d := by
  have hum : u ∈ p.support := p.start_mem_support
  have hcd : c ≠ d := by
    rintro rfl
    exact huv (eq_start_of_adj_of_notMem_support hG hp hc hcu hdv.symm p.end_mem_support).symm
  refine ⟨hcd, fun hcdadj => ?_⟩
  have hr : (p.concat hdv).IsPath := hp.concat hd hdv
  have hcr : c ∉ (p.concat hdv).support := by
    rw [SimpleGraph.Walk.support_concat]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hc, hcd⟩
  have hdr : d ∈ (p.concat hdv).support := by
    rw [SimpleGraph.Walk.support_concat]
    simp
  exact hd (eq_start_of_adj_of_notMem_support hG hr hcr hcu hcdadj hdr ▸ hum)

end AcyclicWalk

namespace FiniteProjectiveLatticeCat

variable {L : FiniteProjectiveLatticeCat ℤ ℤ} {B : Set L.obj.obj.carrier}

namespace IsRootBase

variable [DecidableEq B]

/-- A member of a base outside a path of the graph of the base, adjacent to the start of that
path, pairs to `1` with the sum of the vertices of the path. Every other vertex of the path is
non-adjacent to it, by `eq_start_of_adj_of_notMem_support`, so contributes `0`. -/
theorem pairing_sum_support_eq_one (hB : IsRootBase L B)
    (hG : (rootBaseGraph L B).IsAcyclic) {u v a : B} {p : (rootBaseGraph L B).Walk u v}
    (hp : p.IsPath) (ha : a ∉ p.support) (hau : (rootBaseGraph L B).Adj a u) :
    L.obj.obj.pairing (∑ t ∈ p.support.toFinset, (t : L.obj.obj.carrier)) a = 1 := by
  rw [pairing_sum_left, Finset.sum_eq_single u]
  · exact hB.pairing_eq_one_of_adj hau.symm
  · intro t ht htu
    have htm : t ∈ p.support := List.mem_toFinset.mp ht
    have hta : t ≠ a := fun h => ha (h ▸ htm)
    by_contra hne
    refine htu (eq_start_of_adj_of_notMem_support hG hp ha hau ?_ htm)
    refine ⟨fun h => hta h.symm, ?_⟩
    rw [pairing_comm L (a : L.obj.obj.carrier) (t : L.obj.obj.carrier)]
    exact hne
  · exact fun h => absurd (List.mem_toFinset.mpr p.start_mem_support) h

/-- The sum of the vertices of a path of the graph of a base has self-pairing `-2`, whatever
the length of the path. Adding one vertex to the front of a path adds `-2` for the new
diagonal term and `2 * 1` for the two new cross terms, by `pairing_sum_support_eq_one`. -/
theorem pairing_sum_support_self (hB : IsRootBase L B)
    (hG : (rootBaseGraph L B).IsAcyclic) :
    ∀ {u v : B} (p : (rootBaseGraph L B).Walk u v), p.IsPath →
      L.obj.obj.pairing (∑ t ∈ p.support.toFinset, (t : L.obj.obj.carrier))
        (∑ t ∈ p.support.toFinset, (t : L.obj.obj.carrier)) = -2 := by
  intro u v p
  induction p with
  | @nil z => exact fun _ => by simpa using hB.pairing_self (z : L.obj.obj.carrier) z.2
  | @cons s s' t h q ih =>
    intro hp
    obtain ⟨hq, hs⟩ := (SimpleGraph.Walk.cons_isPath_iff h q).mp hp
    have hcross : L.obj.obj.pairing (s : L.obj.obj.carrier)
        (∑ z ∈ q.support.toFinset, (z : L.obj.obj.carrier)) = 1 := by
      rw [pairing_comm L (s : L.obj.obj.carrier)]
      exact hB.pairing_sum_support_eq_one hG hq hs h
    rw [SimpleGraph.Walk.support_cons, List.toFinset_cons,
      Finset.sum_insert (by simpa using hs), pairing_add_self, hB.pairing_self _ s.2, hcross,
      ih hq]
    ring

omit [DecidableEq B] in
/-- The branch node bound. Two vertices of degree at least three in one connected component of
the graph of a base of an even negative definite lattice are equal.

Write `p` for the path between them, `T` for the sum of its vertices, `a, a'` for two further
neighbours of the first end and `b, b'` for two further neighbours of the second end. The four
extra neighbours lie outside the path and are pairwise non-adjacent, and each pairs to `1` with
`T`, so `a + a' + 2T + b + b'` has self-pairing `(-4) + 2 * 8 + (-8) + ... = 0`. Linear
independence makes that vector nonzero, and negative definiteness then forbids it. -/
theorem no_two_branch_nodes (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B) {x y : B}
    (hx : 3 ≤ ((rootBaseGraph L B).neighborSet x).ncard)
    (hy : 3 ≤ ((rootBaseGraph L B).neighborSet y).ncard)
    (hreach : (rootBaseGraph L B).Reachable x y) : x = y := by
  classical
  haveI : Module.Finite ℤ L.obj.obj.carrier := L.property
  haveI := hB.linearIndepOn.finite_of_isNoetherian
  have hG := hB.isAcyclic_rootBaseGraph hL
  by_contra hne
  obtain ⟨w⟩ := hreach
  obtain ⟨p, hp⟩ := w.toPath
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  -- Two neighbours of `x` other than the second vertex of the path.
  have hsx : p.snd ∈ (rootBaseGraph L B).neighborSet x := p.adj_snd hnil
  have hcardx : 1 < ((rootBaseGraph L B).neighborSet x \ {p.snd}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hsx]
    omega
  obtain ⟨a, a', hamem, ha'mem, haa'⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mp hcardx
  -- Two neighbours of `y` other than the penultimate vertex of the path.
  have hpy : p.penultimate ∈ (rootBaseGraph L B).neighborSet y := (p.adj_penultimate hnil).symm
  have hcardy : 1 < ((rootBaseGraph L B).neighborSet y \ {p.penultimate}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hpy]
    omega
  obtain ⟨b, b', hbmem, hb'mem, hbb'⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mp hcardy
  -- The four extra neighbours lie outside the path.
  have hout : ∀ {c : B}, c ∈ (rootBaseGraph L B).neighborSet x \ {p.snd} →
      c ∉ p.support := by
    intro c hc hcs
    exact hc.2 (hG.eq_snd_of_adj_start hp hc.1 hcs)
  have hout' : ∀ {c : B}, c ∈ (rootBaseGraph L B).neighborSet y \ {p.penultimate} →
      c ∉ p.support := by
    intro c hc hcs
    exact hc.2 (hG.eq_penultimate_of_adj_end hp hc.1 hcs)
  have haS : a ∉ p.support := hout hamem
  have ha'S : a' ∉ p.support := hout ha'mem
  have hbS : b ∉ p.support := hout' hbmem
  have hb'S : b' ∉ p.support := hout' hb'mem
  -- Adjacencies of the four extra neighbours to the two ends.
  have hax : (rootBaseGraph L B).Adj a x := hamem.1.symm
  have ha'x : (rootBaseGraph L B).Adj a' x := ha'mem.1.symm
  have hyb : (rootBaseGraph L B).Adj y b := hbmem.1
  have hyb' : (rootBaseGraph L B).Adj y b' := hb'mem.1
  -- Distinctness and non-adjacency of the four extra neighbours.
  obtain ⟨hab, hnab⟩ := not_adj_of_ends hG hp hne haS hax hbS hyb
  obtain ⟨hab', hnab'⟩ := not_adj_of_ends hG hp hne haS hax hb'S hyb'
  obtain ⟨ha'b, hna'b⟩ := not_adj_of_ends hG hp hne ha'S ha'x hbS hyb
  obtain ⟨ha'b', hna'b'⟩ := not_adj_of_ends hG hp hne ha'S ha'x hb'S hyb'
  have hnaa' : ¬ (rootBaseGraph L B).Adj a a' := fun h =>
    hB.not_adj_triangle hL hamem.1 ha'mem.1 h
  have hnbb' : ¬ (rootBaseGraph L B).Adj b b' := fun h =>
    hB.not_adj_triangle hL hyb hyb' h
  -- The pairings of the four extra neighbours with one another.
  have hzero : ∀ {c d : B}, c ≠ d → ¬ (rootBaseGraph L B).Adj c d →
      L.obj.obj.pairing (c : L.obj.obj.carrier) d = 0 := by
    intro c d hcd hadj
    by_contra h
    exact hadj ⟨hcd, h⟩
  -- The sum of the vertices of the path, and the pairings against it.
  set T : L.obj.obj.carrier := ∑ t ∈ p.support.toFinset, (t : L.obj.obj.carrier) with hTdef
  have hTT : L.obj.obj.pairing T T = -2 := hB.pairing_sum_support_self hG p hp
  have hrev : p.reverse.support.toFinset = p.support.toFinset := by
    rw [SimpleGraph.Walk.support_reverse, List.toFinset_reverse]
  have hTa : L.obj.obj.pairing T a = 1 := hB.pairing_sum_support_eq_one hG hp haS hax
  have hTa' : L.obj.obj.pairing T a' = 1 := hB.pairing_sum_support_eq_one hG hp ha'S ha'x
  have hTb : L.obj.obj.pairing T b = 1 := by
    have h := hB.pairing_sum_support_eq_one hG hp.reverse
      (p := p.reverse) (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse]) hyb.symm
    rwa [hTdef, ← hrev]
  have hTb' : L.obj.obj.pairing T b' = 1 := by
    have h := hB.pairing_sum_support_eq_one hG hp.reverse
      (p := p.reverse) (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse]) hyb'.symm
    rwa [hTdef, ← hrev]
  -- The vector and its expansion.
  set S : Finset B := insert a (insert a' (insert b (insert b' p.support.toFinset))) with hSdef
  set g : B → ℤ := fun t => if t ∈ p.support.toFinset then (2 : ℤ) else 1 with hgdef
  have hxS : x ∈ S := by
    simp only [hSdef, Finset.mem_insert]
    exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_toFinset.mpr p.start_mem_support))))
  have hgx : g x ≠ 0 := by simp [hgdef]
  have hvne : ∑ t ∈ S, g t • (t : L.obj.obj.carrier) ≠ 0 := hB.sum_smul_ne_zero g hxS hgx
  have hexp : ∑ t ∈ S, g t • (t : L.obj.obj.carrier)
      = (T + T) + (((a : L.obj.obj.carrier) + a') + ((b : L.obj.obj.carrier) + b')) := by
    have hsupp : ∑ t ∈ p.support.toFinset, g t • (t : L.obj.obj.carrier) = T + T := by
      rw [hTdef, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [hgdef, if_pos ht]
      abel
    rw [hSdef, Finset.sum_insert (by simp [haa', hab, hab', haS]),
      Finset.sum_insert (by simp [ha'b, ha'b', ha'S]),
      Finset.sum_insert (by simp [hbb', hbS]), Finset.sum_insert (by simpa using hb'S), hsupp]
    have hga : g a = 1 := by simp [hgdef, haS]
    have hga' : g a' = 1 := by simp [hgdef, ha'S]
    have hgb : g b = 1 := by simp [hgdef, hbS]
    have hgb' : g b' = 1 := by simp [hgdef, hb'S]
    rw [hga, hga', hgb, hgb']
    abel
  -- The self-pairing of the vector is zero.
  have haa : L.obj.obj.pairing (a : L.obj.obj.carrier) a = -2 := hB.pairing_self _ a.2
  have ha'a' : L.obj.obj.pairing (a' : L.obj.obj.carrier) a' = -2 := hB.pairing_self _ a'.2
  have hbb : L.obj.obj.pairing (b : L.obj.obj.carrier) b = -2 := hB.pairing_self _ b.2
  have hb'b' : L.obj.obj.pairing (b' : L.obj.obj.carrier) b' = -2 := hB.pairing_self _ b'.2
  have hAA : L.obj.obj.pairing ((a : L.obj.obj.carrier) + a') ((a : L.obj.obj.carrier) + a')
      = -4 := by
    rw [pairing_add_self, haa, ha'a', hzero haa' hnaa']
    ring
  have hBB : L.obj.obj.pairing ((b : L.obj.obj.carrier) + b') ((b : L.obj.obj.carrier) + b')
      = -4 := by
    rw [pairing_add_self, hbb, hb'b', hzero hbb' hnbb']
    ring
  have hAB : L.obj.obj.pairing ((a : L.obj.obj.carrier) + a') ((b : L.obj.obj.carrier) + b')
      = 0 := by
    rw [BilinModuleCat.pairing_add_left, BilinModuleCat.pairing_add_right,
      BilinModuleCat.pairing_add_right, hzero hab hnab, hzero hab' hnab', hzero ha'b hna'b,
      hzero ha'b' hna'b']
    ring
  have hCC : L.obj.obj.pairing (((a : L.obj.obj.carrier) + a') + ((b : L.obj.obj.carrier) + b'))
      (((a : L.obj.obj.carrier) + a') + ((b : L.obj.obj.carrier) + b')) = -8 := by
    rw [pairing_add_self, hAA, hAB, hBB]
    ring
  have hTC : L.obj.obj.pairing T (((a : L.obj.obj.carrier) + a') + ((b : L.obj.obj.carrier) + b'))
      = 4 := by
    rw [BilinModuleCat.pairing_add_right, BilinModuleCat.pairing_add_right,
      BilinModuleCat.pairing_add_right, hTa, hTa', hTb, hTb']
    ring
  have hfinal : L.obj.obj.pairing (∑ t ∈ S, g t • (t : L.obj.obj.carrier))
      (∑ t ∈ S, g t • (t : L.obj.obj.carrier)) = 0 := by
    rw [hexp, pairing_add_self, pairing_add_self, BilinModuleCat.pairing_add_left, hTT, hTC, hCC]
    ring
  exact absurd hfinal (L.pairing_self_neg hL hvne).ne

omit [DecidableEq B] in
/-- The branch node bound on a connected diagram. The set of vertices of degree at least three
of the graph of a base is a subsingleton as soon as the graph is preconnected. With
`IsRootBase.ncard_neighborSet_le_three` this says that a connected diagram is either a path or
carries exactly one vertex of degree exactly three. -/
theorem subsingleton_setOf_three_le_ncard_neighborSet (hL : IsNegativeDefiniteLattice L)
    (hB : IsRootBase L B) (hpre : (rootBaseGraph L B).Preconnected) :
    {v : B | 3 ≤ ((rootBaseGraph L B).neighborSet v).ncard}.Subsingleton :=
  fun _ hu _ hv => hB.no_two_branch_nodes hL hu hv (hpre _ _)

end IsRootBase

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
