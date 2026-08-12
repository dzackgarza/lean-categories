/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ArmBounds

/-!
# The shape of a connected diagram

`DiagramBounds.lean` bounds the graph of a base of simple roots: it is acyclic, of degree at
most three, and a connected component carries at most one vertex of degree three.
`ArmBounds.lean` bounds the arm lengths of a three-armed star. This file supplies the missing
graph-theoretic step between them: it reads the two bounds as a decomposition of the graph, and
so classifies the diagram of a connected base.

* `notAdj_getVert` is the chord bound in the form the arms need. In an acyclic graph two
  vertices of a path at index distance at least two are non-adjacent. The proof is an induction
  along the path on `eq_start_of_adj_of_notMem_support` of `DiagramBounds.lean`.
* `eq_start_of_mem_support_of_mem_support` and `notAdj_of_mem_support_of_mem_support` are the
  fork bounds. Two paths out of a common start that leave it by different edges meet only at
  that start, and no edge joins one to the other away from it. Both come from Mathlib's
  uniqueness of paths in an acyclic graph, `SimpleGraph.isAcyclic_iff_path_unique`.
* `exists_maximal_isPath` and `exists_maximal_isPath_snd` produce a path of maximum length in a
  finite graph, the second among the paths that leave a given vertex by a given edge. Maximum
  length exists because the lengths of paths are bounded by the number of vertices.
* `mem_support_of_adj_getVert` is the degree bound in the form the covering needs: an interior
  vertex of a path already has two neighbours on the path, so if its degree is at most two it
  has no other neighbour.
* `isPath_of_no_branch_node` is the first classification statement. A finite connected acyclic
  graph of degree at most two is a path: one path passes through every vertex and carries every
  edge. Take a path of maximum length: no vertex of it has a neighbour outside it, and
  connectedness then puts every vertex on it. Acyclicity enters only for the edges.
* `exists_arms_of_branch_node` is the second. A finite connected graph with one vertex `c` of
  degree three and all other degrees at most two is covered by three paths out of `c` that
  leave it by its three different edges. The paths are again of maximum length, one for each
  edge at `c`. Acyclicity is not needed for the covering; it enters through the fork bounds,
  which are what make the three paths meet only at `c`.
* `IsRootBase.exists_threeArmStar_of_branch_node` reads that decomposition off as the
  `IsThreeArmStar` data of `ArmBounds.lean`. The `t`-th arm is the `t`-th path run backwards,
  `x t i = (p t).getVert ((p t).length - i)`, so that `x t 0` is the far end and
  `x t (k t - 1)` is the neighbour of `c`. The pairing conditions are the two bounds above:
  inside an arm `notAdj_getVert` gives orthogonality at index distance at least two, and
  between two arms the fork bounds give it.
* `IsRootBase.adeClassification` is the classification of connected diagrams. The graph of a
  base of an even negative definite lattice, when connected, is either a path or a star with
  three arms whose lengths, counted with the branch node, are one of the ADE triples.

The disjunction is on the presence of a vertex of degree exactly three. `RootBase.lean` caps
the degree at three and `DiagramBounds.lean` allows at most one such vertex, so the two cases
are the only ones and the second carries a single branch node.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

section GraphShape

variable {V : Type*} {G : SimpleGraph V}

/-! ## Chords and forks in an acyclic graph -/

/-- In an acyclic graph two vertices of a path whose indices differ by at least two are not
adjacent. An edge between them would close a cycle with the stretch of the path between them.
The induction removes the first vertex of the path: an edge from it to a later vertex is
excluded by `eq_start_of_adj_of_notMem_support`. -/
theorem notAdj_getVert (hG : G.IsAcyclic) : ∀ {u v : V} {p : G.Walk u v}, p.IsPath →
    ∀ {a b : ℕ}, a + 1 < b → b ≤ p.length → ¬ G.Adj (p.getVert a) (p.getVert b) := by
  intro u v p
  induction p with
  | nil => intro _ a b hab hb; simp only [SimpleGraph.Walk.length_nil] at hb; omega
  | @cons s s' t h q ih =>
    intro hp a b hab hb hadj
    obtain ⟨hq, hs⟩ := (SimpleGraph.Walk.cons_isPath_iff h q).mp hp
    rw [SimpleGraph.Walk.length_cons] at hb
    rw [SimpleGraph.Walk.getVert_cons q h (by omega : b ≠ 0)] at hadj
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [SimpleGraph.Walk.getVert_zero] at hadj
      have hmem : q.getVert (b - 1) ∈ q.support := q.getVert_mem_support _
      have := eq_start_of_adj_of_notMem_support hG hq hs h hadj hmem
      have hzero : q.getVert (b - 1) = q.getVert 0 := by
        rw [SimpleGraph.Walk.getVert_zero]; exact this
      have := hq.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hzero
      omega
    · rw [SimpleGraph.Walk.getVert_cons q h (by omega : a ≠ 0)] at hadj
      exact ih hq (by omega) (by omega) hadj

/-- Extending a walk at its far end does not change the edge it leaves its start by. -/
theorem snd_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) (hp : ¬ p.Nil) :
    (p.concat h).snd = p.snd := by
  cases p with
  | nil => simp at hp
  | cons _ _ => simp [SimpleGraph.Walk.concat_cons]

/-- Two paths out of a common start that leave it by different edges meet only at that start.
Otherwise the two stretches up to a common vertex are two paths with the same ends, which
uniqueness of paths in an acyclic graph identifies, so the two first edges agree. -/
theorem eq_start_of_mem_support_of_mem_support (hG : G.IsAcyclic) {c v w : V} {p : G.Walk c v}
    {q : G.Walk c w} (hp : p.IsPath) (hq : q.IsPath) (hne : p.snd ≠ q.snd) {z : V}
    (hzp : z ∈ p.support) (hzq : z ∈ q.support) : z = c := by
  classical
  by_contra hzc
  have heq : p.takeUntil z hzp = q.takeUntil z hzq :=
    congrArg Subtype.val (hG.path_unique ⟨_, hp.takeUntil hzp⟩ ⟨_, hq.takeUntil hzq⟩)
  refine hne ?_
  rw [← SimpleGraph.Walk.snd_takeUntil hzc p hzp, ← SimpleGraph.Walk.snd_takeUntil hzc q hzq,
    heq]

/-- No edge joins two paths out of a common start that leave it by different edges, away from
that start. Such an edge would extend the first path to a second path to the far end of the
edge, and uniqueness of paths would then put the near end of the edge on the other path. -/
theorem notAdj_of_mem_support_of_mem_support (hG : G.IsAcyclic) {c v w : V} {p : G.Walk c v}
    {q : G.Walk c w} (hp : p.IsPath) (hq : q.IsPath) (hne : p.snd ≠ q.snd) {z z' : V}
    (hzp : z ∈ p.support) (hzq : z' ∈ q.support) (hzc : z ≠ c) (hz'c : z' ≠ c) :
    ¬ G.Adj z z' := by
  classical
  intro hadj
  have hz : z ∉ (q.takeUntil z' hzq).support := fun hmem =>
    hzc (eq_start_of_mem_support_of_mem_support hG hp hq hne hzp
      (q.support_takeUntil_subset_support hzq hmem))
  have := hG.mem_support_of_ne_mem_support_of_adj_of_isPath (hp.takeUntil hzp)
    (hq.takeUntil hzq) hadj hz
  exact hz'c (eq_start_of_mem_support_of_mem_support hG hp hq hne
    (p.support_takeUntil_subset_support hzp this) hzq)

/-! ## Paths of maximum length -/

/-- A finite graph carries a path of maximum length, as soon as it has a vertex. The lengths of
paths are bounded by the number of vertices, so the set of lengths is finite. -/
theorem exists_maximal_isPath [Finite V] (u : V) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧
      ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length := by
  classical
  haveI := Fintype.ofFinite V
  have hsub : {m : ℕ | ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = m} ⊆
      {i : ℕ | i < Fintype.card V} := by
    rintro m ⟨a, b, p, hp, rfl⟩
    exact hp.length_lt
  have hfin : {m : ℕ | ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = m}.Finite :=
    (Set.finite_lt_nat _).subset hsub
  have hne : {m : ℕ | ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = m}.Nonempty :=
    ⟨0, u, u, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, rfl⟩
  obtain ⟨a, b, p, hp, hlen⟩ := hne.csSup_mem hfin
  refine ⟨a, b, p, hp, fun x y q hq => ?_⟩
  rw [hlen]
  exact le_csSup hfin.bddAbove ⟨x, y, q, hq, rfl⟩

/-- A finite graph carries a path of maximum length among those that start at a given vertex and
leave it by a given edge. -/
theorem exists_maximal_isPath_snd [Finite V] {c n : V} (hcn : G.Adj c n) :
    ∃ (v : V) (p : G.Walk c v), p.IsPath ∧ p.snd = n ∧ 0 < p.length ∧
      ∀ (w : V) (q : G.Walk c w), q.IsPath → q.snd = n → q.length ≤ p.length := by
  classical
  haveI := Fintype.ofFinite V
  have hsub : {m : ℕ | ∃ (v : V) (p : G.Walk c v), p.IsPath ∧ p.snd = n ∧ p.length = m} ⊆
      {i : ℕ | i < Fintype.card V} := by
    rintro m ⟨v, p, hp, -, rfl⟩
    exact hp.length_lt
  have hfin : {m : ℕ | ∃ (v : V) (p : G.Walk c v), p.IsPath ∧ p.snd = n ∧ p.length = m}.Finite :=
    (Set.finite_lt_nat _).subset hsub
  have hsingle : (SimpleGraph.Walk.cons hcn SimpleGraph.Walk.nil).IsPath := by
    simp [SimpleGraph.Walk.isPath_def, hcn.ne]
  have hne : {m : ℕ | ∃ (v : V) (p : G.Walk c v), p.IsPath ∧ p.snd = n ∧ p.length = m}.Nonempty :=
    ⟨1, n, SimpleGraph.Walk.cons hcn SimpleGraph.Walk.nil, hsingle, by simp, by simp⟩
  obtain ⟨v, p, hp, hsnd, hlen⟩ := hne.csSup_mem hfin
  have hmax : ∀ (w : V) (q : G.Walk c w), q.IsPath → q.snd = n → q.length ≤ p.length := by
    intro w q hq hqs
    rw [hlen]
    exact le_csSup hfin.bddAbove ⟨w, q, hq, hqs, rfl⟩
  refine ⟨v, p, hp, hsnd, ?_, hmax⟩
  have hone : 1 ≤ p.length := by
    simpa using hmax n (SimpleGraph.Walk.cons hcn SimpleGraph.Walk.nil) hsingle (by simp)
  omega

/-! ## Covering a graph by maximal paths -/

/-- A neighbour of an interior vertex of a path of degree at most two lies on the path: the two
neighbours along the path already exhaust its neighbours. -/
theorem mem_support_of_adj_getVert [Finite V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hi0 : 0 < i) (hil : i < p.length) (hdeg : (G.neighborSet (p.getVert i)).ncard ≤ 2) {z : V}
    (hz : G.Adj (p.getVert i) z) : z ∈ p.support := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hprev : G.Adj (p.getVert (j + 1)) (p.getVert j) := (p.adj_getVert_succ (by omega)).symm
  have hnext : G.Adj (p.getVert (j + 1)) (p.getVert (j + 2)) := p.adj_getVert_succ (by omega)
  have hjne : p.getVert j ≠ p.getVert (j + 2) := by
    intro h
    have := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) h
    omega
  have hsub : ({p.getVert j, p.getVert (j + 2)} : Set V) ⊆ G.neighborSet (p.getVert (j + 1)) := by
    rintro x (rfl | rfl)
    · exact hprev
    · exact hnext
  have heq : ({p.getVert j, p.getVert (j + 2)} : Set V) = G.neighborSet (p.getVert (j + 1)) :=
    Set.eq_of_subset_of_ncard_le hsub (by rwa [Set.ncard_pair hjne]) (Set.toFinite _)
  have : z ∈ ({p.getVert j, p.getVert (j + 2)} : Set V) := by rw [heq]; exact hz
  rcases this with rfl | rfl
  · exact p.getVert_mem_support _
  · exact p.getVert_mem_support _

/-- A finite connected acyclic graph in which every vertex has at most two neighbours is a path:
there is a path that passes through every vertex and carries every edge, in the sense that two
of its vertices are adjacent only when they are consecutive along it.

Take a path of maximum length. An end of it has no neighbour outside it, since such a neighbour
would extend it, and an interior vertex has no neighbour outside it by the degree bound. So the
support is closed under adjacency, and connectedness carries every vertex into it. That the
graph has no further edge is `notAdj_getVert`. -/
theorem isPath_of_no_branch_node [Finite V] (hG : G.IsAcyclic) (hconn : G.Connected)
    (hdeg : ∀ w : V, (G.neighborSet w).ncard ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ (∀ w : V, w ∈ p.support) ∧
      ∀ a b : ℕ, a ≤ p.length → b ≤ p.length → G.Adj (p.getVert a) (p.getVert b) →
        a + 1 = b ∨ b + 1 = a := by
  classical
  obtain ⟨u₀⟩ := hconn.nonempty
  obtain ⟨a, b, p, hp, hmax⟩ := exists_maximal_isPath (G := G) u₀
  have hclosed : ∀ w ∈ p.support, ∀ z : V, G.Adj w z → z ∈ p.support := by
    intro w hw z hwz
    obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
    by_contra hzs
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [SimpleGraph.Walk.getVert_zero] at hwz
      have hcons : (SimpleGraph.Walk.cons hwz.symm p).IsPath :=
        (SimpleGraph.Walk.cons_isPath_iff _ p).mpr ⟨hp, hzs⟩
      have := hmax z b (SimpleGraph.Walk.cons hwz.symm p) hcons
      rw [SimpleGraph.Walk.length_cons] at this
      omega
    · rcases eq_or_lt_of_le hi with rfl | hlt
      · rw [p.getVert_length] at hwz
        have := hmax a z (p.concat hwz) (hp.concat hzs hwz)
        rw [SimpleGraph.Walk.length_concat] at this
        omega
      · exact hzs (mem_support_of_adj_getVert hp hi0 hlt (hdeg _) hwz)
  have hwalk : ∀ {s t : V} (q : G.Walk s t), s ∈ p.support → t ∈ p.support := by
    intro s t q
    induction q with
    | nil => exact id
    | cons h _ ih => exact fun hs => ih (hclosed _ hs _ h)
  refine ⟨a, b, p, hp, fun w => ?_, fun m n hm hn hadj => ?_⟩
  · obtain ⟨q⟩ := hconn.preconnected a w
    exact hwalk q p.start_mem_support
  · rcases lt_trichotomy m n with h | rfl | h
    · rcases Nat.lt_or_ge (m + 1) n with h' | h'
      · exact absurd hadj (notAdj_getVert hG hp h' hn)
      · exact Or.inl (by omega)
    · exact absurd rfl hadj.ne
    · rcases Nat.lt_or_ge (n + 1) m with h' | h'
      · exact absurd hadj.symm (notAdj_getVert hG hp h' hm)
      · exact Or.inr (by omega)

/-- A finite connected graph with one vertex `c` of degree three and all other degrees at most
two is covered by three paths out of `c`, one along each edge at `c`.

Each path is of maximum length among those leaving `c` by its edge, so its far end has no
neighbour outside it; the interior vertices have none by the degree bound; and the neighbours of
`c` are the three second vertices. So the union of the three supports is closed under adjacency,
and connectedness carries every vertex into it. -/
theorem exists_arms_of_branch_node [Finite V] (hconn : G.Connected) {c : V}
    (hc : (G.neighborSet c).ncard = 3) (hdeg : ∀ w : V, w ≠ c → (G.neighborSet w).ncard ≤ 2) :
    ∃ (v : Fin 3 → V) (p : ∀ t, G.Walk c (v t)), (∀ t, (p t).IsPath) ∧ (∀ t, 0 < (p t).length) ∧
      (∀ t u, t ≠ u → (p t).snd ≠ (p u).snd) ∧ ∀ w : V, w = c ∨ ∃ t, w ∈ (p t).support := by
  classical
  obtain ⟨n₀, n₁, n₂, h01, h02, h12, hset⟩ := Set.ncard_eq_three.mp hc
  set nn : Fin 3 → V := ![n₀, n₁, n₂] with hnn
  have hn0 : nn 0 = n₀ := by rw [hnn]; rfl
  have hn1 : nn 1 = n₁ := by rw [hnn]; rfl
  have hn2 : nn 2 = n₂ := by rw [hnn]; rfl
  have hmemn : ∀ t, nn t ∈ G.neighborSet c := by
    intro t
    rw [hset]
    fin_cases t <;> simp [hn0, hn1, hn2]
  have hnninj : ∀ t u, t ≠ u → nn t ≠ nn u := by
    have h10 : n₁ ≠ n₀ := Ne.symm h01
    have h20 : n₂ ≠ n₀ := Ne.symm h02
    have h21 : n₂ ≠ n₁ := Ne.symm h12
    intro t u htu
    fin_cases t <;> fin_cases u <;> simp_all
  have key : ∀ t : Fin 3, ∃ (v : V) (p : G.Walk c v), p.IsPath ∧ p.snd = nn t ∧ 0 < p.length ∧
      ∀ (w : V) (q : G.Walk c w), q.IsPath → q.snd = nn t → q.length ≤ p.length :=
    fun t => exists_maximal_isPath_snd (hmemn t)
  choose v p hp hsnd hpos hmax using key
  refine ⟨v, p, hp, hpos, fun t u htu h => hnninj t u htu (by rw [← hsnd t, ← hsnd u, h]), ?_⟩
  have hclosed : ∀ w : V, (w = c ∨ ∃ t, w ∈ (p t).support) → ∀ z : V, G.Adj w z →
      (z = c ∨ ∃ t, z ∈ (p t).support) := by
    intro w hw z hwz
    have hmem : ∀ t : Fin 3, nn t ∈ (p t).support := fun t => by
      rw [← hsnd t]; exact (p t).getVert_mem_support 1
    rcases eq_or_ne w c with hwc | hwc
    · have hz : z ∈ G.neighborSet c := by rw [← hwc]; exact hwz
      rw [hset] at hz
      have hz3 : z = n₀ ∨ z = n₁ ∨ z = n₂ := by simpa using hz
      refine Or.inr ?_
      rcases hz3 with rfl | rfl | rfl
      · exact ⟨0, by rw [← hn0]; exact hmem 0⟩
      · exact ⟨1, by rw [← hn1]; exact hmem 1⟩
      · exact ⟨2, by rw [← hn2]; exact hmem 2⟩
    · obtain ⟨t, hwt⟩ := hw.resolve_left hwc
      obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwt
      refine Or.inr ⟨t, ?_⟩
      have hi0 : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · exact absurd ((p t).getVert_zero) hwc
        · exact h
      rcases eq_or_lt_of_le hi with rfl | hlt
      · by_contra hzs
        rw [(p t).getVert_length] at hwz
        have hcat := hmax t z ((p t).concat hwz) ((hp t).concat hzs hwz) ?_
        · rw [SimpleGraph.Walk.length_concat] at hcat
          omega
        · have hnil : ¬ (p t).Nil := by
            have := hpos t
            rw [← SimpleGraph.Walk.length_eq_zero_iff]
            omega
          rw [snd_concat _ _ hnil]
          exact hsnd t
      · exact mem_support_of_adj_getVert (hp t) hi0 hlt (hdeg _ hwc) hwz
  have hwalk : ∀ {s t : V} (q : G.Walk s t), (s = c ∨ ∃ r, s ∈ (p r).support) →
      (t = c ∨ ∃ r, t ∈ (p r).support) := by
    intro s t q
    induction q with
    | nil => exact id
    | cons h _ ih => exact fun hs => ih (hclosed _ hs _ h)
  intro w
  obtain ⟨q⟩ := hconn.preconnected c w
  exact hwalk q (Or.inl rfl)

end GraphShape

namespace FiniteProjectiveLatticeCat

variable {L : FiniteProjectiveLatticeCat ℤ ℤ} {B : Set L.obj.obj.carrier}

/-- Two distinct non-adjacent members of a base are orthogonal: that is the definition of the
graph of a base read backwards. -/
theorem pairing_eq_zero_of_notAdj {x y : B} (hne : x ≠ y)
    (hadj : ¬ (rootBaseGraph L B).Adj x y) : L.obj.obj.pairing (x : L.obj.obj.carrier) y = 0 := by
  by_contra h
  exact hadj ⟨hne, h⟩

namespace IsRootBase

/-- The three arms of a connected diagram with a branch node. A vertex `c` of degree three in the
connected graph of a base of an even negative definite lattice carries the `IsThreeArmStar` data
of `ArmBounds.lean`, and the three arms cover every vertex of the graph.

The three paths out of `c` come from `exists_arms_of_branch_node`, and the `t`-th arm is the
`t`-th path run backwards from its far end. Inside an arm the pairing pattern is adjacency along
the path and `notAdj_getVert` away from it; between two arms it is the fork bounds. -/
theorem exists_threeArmStar_of_branch_node (hL : IsNegativeDefiniteLattice L)
    (hB : IsRootBase L B) (hconn : (rootBaseGraph L B).Connected) {c : B}
    (hc : ((rootBaseGraph L B).neighborSet c).ncard = 3) :
    ∃ (x : Fin 3 → ℕ → B) (k : Fin 3 → ℕ), IsThreeArmStar L B c x k ∧
      ∀ w : B, w = c ∨ ∃ t, ∃ i < k t, x t i = w := by
  classical
  haveI := hB.finite.to_subtype
  have hG := hB.isAcyclic_rootBaseGraph hL
  have hdeg : ∀ w : B, w ≠ c → ((rootBaseGraph L B).neighborSet w).ncard ≤ 2 := by
    intro w hwc
    have h3 := hB.ncard_neighborSet_le_three hL w
    have hne : ((rootBaseGraph L B).neighborSet w).ncard ≠ 3 := by
      intro h
      exact hwc (hB.subsingleton_setOf_three_le_ncard_neighborSet hL hconn.preconnected
        (le_of_eq h.symm) (le_of_eq hc.symm))
    omega
  obtain ⟨v, p, hp, hpos, hsnd, hcov⟩ := exists_arms_of_branch_node hconn hc hdeg
  refine ⟨fun t i => (p t).getVert ((p t).length - i), fun t => (p t).length, ?_, ?_⟩
  · have hvne : ∀ (t : Fin 3) (a b : ℕ), a ≤ (p t).length → b ≤ (p t).length → a ≠ b →
        (p t).getVert a ≠ (p t).getVert b := by
      intro t a b ha hb hab h
      exact hab ((hp t).getVert_injOn (by simpa using ha) (by simpa using hb) h)
    have hcne : ∀ (t : Fin 3) (a : ℕ), a ≤ (p t).length → 0 < a → (p t).getVert a ≠ c := by
      intro t a ha ha0 h
      have h0 : (p t).getVert a = (p t).getVert 0 := by rw [h, (p t).getVert_zero]
      have := (hp t).getVert_injOn (by simpa using ha)
        (by simp only [Set.mem_setOf_eq]; omega) h0
      omega
    have harm : ∀ t : Fin 3, IsArm L
        (fun i => (((p t).getVert ((p t).length - i) : B) : L.obj.obj.carrier))
        ((p t).length) := by
      intro t
      refine ⟨fun i _ => hB.pairing_self _ ((p t).getVert _).2, fun i hi => ?_,
        fun i j hij hj => ?_⟩
      · have hstep : (p t).length - (i + 1) + 1 = (p t).length - i := by omega
        have hadj := (p t).adj_getVert_succ
          (show (p t).length - (i + 1) < (p t).length by omega)
        rw [hstep] at hadj
        exact hB.pairing_eq_one_of_adj hadj.symm
      · refine pairing_eq_zero_of_notAdj
          (hvne t _ _ (by omega) (by omega) (by omega)) fun hadj => ?_
        exact notAdj_getVert hG (hp t) (a := (p t).length - j) (b := (p t).length - i)
          (by omega) (by omega) hadj.symm
    refine ⟨harm, hB.pairing_self _ c.2, fun t i hi => ?_, fun t i hi => ?_, fun t u htu i hi j
      hj => ?_, fun t i hi => hcne t _ (by omega) (by omega)⟩
    · refine pairing_eq_zero_of_notAdj (hcne t _ (by omega) (by omega)) fun hadj => ?_
      refine notAdj_getVert hG (hp t) (a := 0) (b := (p t).length - i) (by omega) (by omega) ?_
      rw [(p t).getVert_zero]
      exact hadj.symm
    · have h1 : (p t).length - i = 1 := by omega
      have hnil : ¬ (p t).Nil := by
        have := hpos t
        rw [← SimpleGraph.Walk.length_eq_zero_iff]
        omega
      rw [h1]
      exact hB.pairing_eq_one_of_adj ((p t).adj_snd hnil).symm
    · have hmt : (p t).getVert ((p t).length - i) ∈ (p t).support := (p t).getVert_mem_support _
      have hmu : (p u).getVert ((p u).length - j) ∈ (p u).support := (p u).getVert_mem_support _
      have hct := hcne t ((p t).length - i) (by omega) (by omega)
      have hcu := hcne u ((p u).length - j) (by omega) (by omega)
      refine pairing_eq_zero_of_notAdj (fun h => hct ?_) ?_
      · exact eq_start_of_mem_support_of_mem_support hG (hp t) (hp u) (hsnd t u htu) hmt
          (h ▸ hmu)
      · exact notAdj_of_mem_support_of_mem_support hG (hp t) (hp u) (hsnd t u htu) hmt hmu hct hcu
  · intro w
    rcases hcov w with h | ⟨t, hw⟩
    · exact Or.inl h
    · obtain ⟨a, rfl, ha⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · exact Or.inl (p t).getVert_zero
      · refine Or.inr ⟨t, (p t).length - a,
          show (p t).length - a < (p t).length by omega, ?_⟩
        change (p t).getVert ((p t).length - ((p t).length - a)) = (p t).getVert a
        congr 1
        omega

/-- The classification of connected diagrams. The graph of a base of simple roots of an even
negative definite lattice, when connected, is either a path through every vertex, or a star with
three arms out of a single branch node whose lengths, counted with the branch node, form one of
the ADE triples `(1, q, r)`, `(2, 2, r)`, `(2, 3, 3)`, `(2, 3, 4)`, `(2, 3, 5)`.

The disjunction is on the presence of a vertex of degree three. Without one the degree bound of
`RootBase.lean` leaves degree at most two, and `isPath_of_no_branch_node` applies. With one the
branch node is unique by `DiagramBounds.lean`, so every other vertex has degree at most two,
`exists_threeArmStar_of_branch_node` produces the arms, and `IsThreeArmStar.admissible` bounds
their lengths. -/
theorem adeClassification (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B)
    (hconn : (rootBaseGraph L B).Connected) :
    (∃ (u v : B) (q : (rootBaseGraph L B).Walk u v), q.IsPath ∧ (∀ w : B, w ∈ q.support) ∧
        ∀ a b : ℕ, a ≤ q.length → b ≤ q.length →
          (rootBaseGraph L B).Adj (q.getVert a) (q.getVert b) → a + 1 = b ∨ b + 1 = a) ∨
      ∃ (c : B) (x : Fin 3 → ℕ → B) (k : Fin 3 → ℕ), IsThreeArmStar L B c x k ∧
        ADEInequality.Admissible {(k 0).succPNat, (k 1).succPNat, (k 2).succPNat} ∧
        ∀ w : B, w = c ∨ ∃ t, ∃ i < k t, x t i = w := by
  classical
  haveI := hB.finite.to_subtype
  by_cases hbranch : ∃ c : B, ((rootBaseGraph L B).neighborSet c).ncard = 3
  · obtain ⟨c, hc⟩ := hbranch
    obtain ⟨x, k, hstar, hcov⟩ := hB.exists_threeArmStar_of_branch_node hL hconn hc
    exact Or.inr ⟨c, x, k, hstar, hstar.admissible hL hB, hcov⟩
  · simp only [not_exists] at hbranch
    refine Or.inl (isPath_of_no_branch_node (hB.isAcyclic_rootBaseGraph hL) hconn fun w => ?_)
    have h3 := hB.ncard_neighborSet_le_three hL w
    have := hbranch w
    omega

end IsRootBase

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
