/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.RootLattice
public import LeanCategories.Lattices.Valued.ScaleAndEvenness

/-!
# Even definite root lattices are simply laced

`RootLattice.lean` builds the root set of a definite lattice, its finiteness, the root graph,
and the Cauchy-Schwarz bound. This file adds the reduction steps that stand between that
material and a classification statement.

* **Reduction to one level set.** `IsRoot` names the four values `±1` and `±2`. Evenness of the
  lattice, in the `IsIEven L (2)` form of `ScaleAndEvenness.lean`, removes `±1`, and negative
  definiteness removes `+2`. So a root of an even negative definite lattice has self-pairing
  exactly `-2`: `isRoot_iff_pairing_eq_neg_two`.
* **Pairings in `{-1, 0, 1}`.** With every root on one level set the Cauchy-Schwarz bound
  applies to every pair of roots that is neither equal nor opposite:
  `pairing_mem_of_isRoot`. `rootGraph_simplyLaced` restates this on the root graph: an edge
  between roots that are not opposite carries pairing of absolute value `1`, so no edge is
  multiple.
* **Triangles are dependent.** Three roots pairing to `1` in every pair sum to a vector of
  self-pairing `0`, which negative definiteness forces to be zero:
  `add_add_eq_zero_of_pairing_triangle`. A triangle of the root graph therefore spans a rank
  two sublattice, which is the input to the rank-two subdiagram bounds.
* **Irreducibility is indecomposability.** `preconnected_rootGraph_iff_forall_not_splitting`
  identifies preconnectedness of the root graph with the absence of a partition of the root
  set into two nonempty mutually orthogonal parts, and `pairing_eq_zero_of_mem_span` carries
  such a partition to an orthogonal splitting of the spanned sublattices.

Opposite roots stay adjacent in the root graph: `b(x, -x) = 2` for a root of self-pairing `-2`.
The simple lacing statement therefore carries the hypothesis `x ≠ -y`, which the passage to a
set of simple roots supplies later.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

/-- A nonzero vector of a negative definite lattice has a negative value. -/
theorem pairing_self_neg (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) {x : L.obj.obj.carrier} (hx : x ≠ 0) :
    L.obj.obj.pairing x x < 0 := by
  have h := (oppositeFiniteProjectiveLattice L).pairing_self_pos
    (isPositiveDefiniteLattice_opposite L hL) hx
  change 0 < (oppositeLattice L.obj).obj.pairing x x at h
  rwa [oppositeLattice_pairing, neg_pos] at h

/-- Only the zero vector of a negative definite lattice is isotropic. -/
theorem eq_zero_of_pairing_self_eq_zero (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) {x : L.obj.obj.carrier}
    (hx : L.obj.obj.pairing x x = 0) : x = 0 := by
  by_contra h
  exact absurd hx (L.pairing_self_neg hL h).ne

/-- Evenness in the `IsIEven L (2)` sense of `ScaleAndEvenness.lean` says exactly that every
self-pairing is divisible by `2`. -/
theorem two_dvd_pairing_self_of_isEven (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hE : IsEven L.obj) (x : L.obj.obj.carrier) : (2 : ℤ) ∣ L.obj.obj.pairing x x := by
  have hx := (isIEven_iff_value_mem L.obj (Ideal.span {(2 : ℤ)})).mp hE x
  rw [Ideal.mem_span_singleton] at hx
  exact hx

/-- Reduction to a single level set. In an even negative definite lattice the four root values
`±1` and `±2` collapse to `-2`: evenness excludes `±1`, and definiteness excludes `2`. -/
theorem isRoot_iff_pairing_eq_neg_two (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) (hE : IsEven L.obj) (x : L.obj.obj.carrier) :
    IsRoot L.obj x ↔ L.obj.obj.pairing x x = -2 := by
  refine ⟨fun hx => ?_, fun hx => Or.inr (Or.inl hx)⟩
  have hdvd := L.two_dvd_pairing_self_of_isEven hE x
  have hne : x ≠ 0 := by
    rintro rfl
    rcases hx with h | h | h | h <;>
      rw [BilinModuleCat.pairing_zero_left] at h <;> omega
  have hneg := L.pairing_self_neg hL hne
  rcases hx with h | h | h | h <;> omega

/-- The pairing of two roots of an even negative definite lattice that are neither equal nor
opposite lies in `{-1, 0, 1}`. This is the Cauchy-Schwarz bound of `RootLattice.lean` applied
after the reduction to the level set `-2`. -/
theorem pairing_mem_of_isRoot (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) (hE : IsEven L.obj) {x y : L.obj.obj.carrier}
    (hx : IsRoot L.obj x) (hy : IsRoot L.obj y) (hne : x ≠ y) (hopp : x ≠ -y) :
    L.obj.obj.pairing x y ∈ ({-1, 0, 1} : Set ℤ) := by
  have hbound := L.abs_pairing_le_one_of_isNegativeDefinite hL
    ((L.isRoot_iff_pairing_eq_neg_two hL hE x).mp hx)
    ((L.isRoot_iff_pairing_eq_neg_two hL hE y).mp hy) hne hopp
  rw [abs_le] at hbound
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- The root graph of an even negative definite lattice is simply laced: an edge between two
roots that are not opposite carries a pairing of absolute value `1`. -/
theorem rootGraph_simplyLaced (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) (hE : IsEven L.obj) {x y : L.rootSet}
    (hadj : (rootGraph L).Adj x y) (hopp : (x : L.obj.obj.carrier) ≠ -(y : L.obj.obj.carrier)) :
    |L.obj.obj.pairing x y| = 1 := by
  have hmem := L.pairing_mem_of_isRoot hL hE x.property y.property
    (Subtype.coe_injective.ne hadj.1) hopp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hzero := hadj.2
  rcases hmem with h | h | h
  · rw [h]; decide
  · exact absurd h hzero
  · rw [h]; decide

/-- The triangle relation. Three vectors of self-pairing `-2` in a negative definite lattice
whose three pairings are all `1` sum to zero, because the self-pairing of the sum is
`-6 + 2 * 3 = 0`. -/
theorem add_add_eq_zero_of_pairing_triangle (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) {x y z : L.obj.obj.carrier}
    (hx : L.obj.obj.pairing x x = -2) (hy : L.obj.obj.pairing y y = -2)
    (hz : L.obj.obj.pairing z z = -2) (hxy : L.obj.obj.pairing x y = 1)
    (hxz : L.obj.obj.pairing x z = 1) (hyz : L.obj.obj.pairing y z = 1) :
    x + y + z = 0 := by
  refine L.eq_zero_of_pairing_self_eq_zero hL ?_
  have hsum : L.obj.obj.pairing (x + y) (x + y) = -2 := by
    rw [pairing_add_self, hx, hy, hxy]; ring
  have hcross : L.obj.obj.pairing (x + y) z = 2 := by
    rw [BilinModuleCat.pairing_add_left, hxz, hyz]; ring
  rw [pairing_add_self, hsum, hcross, hz]
  ring

/-- A triangle of roots is linearly dependent: the third root is the negative of the sum of the
other two, so it lies in their span. This bounds the rank a triangle can occupy. -/
theorem mem_span_of_pairing_triangle (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) {x y z : L.obj.obj.carrier}
    (hx : L.obj.obj.pairing x x = -2) (hy : L.obj.obj.pairing y y = -2)
    (hz : L.obj.obj.pairing z z = -2) (hxy : L.obj.obj.pairing x y = 1)
    (hxz : L.obj.obj.pairing x z = 1) (hyz : L.obj.obj.pairing y z = 1) :
    z ∈ Submodule.span ℤ ({x, y} : Set L.obj.obj.carrier) := by
  have hsum := L.add_add_eq_zero_of_pairing_triangle hL hx hy hz hxy hxz hyz
  have hzeq : z = -(x + y) := by
    rw [eq_neg_iff_add_eq_zero, add_comm z (x + y)]
    exact hsum
  rw [hzeq]
  refine Submodule.neg_mem _ (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.subset_span (Set.mem_insert x {y})
  · exact Submodule.subset_span (Set.mem_insert_of_mem x rfl)

/-- Orthogonality of two subsets is inherited by the sublattices they span. -/
theorem pairing_eq_zero_of_mem_span (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {S T : Set L.obj.obj.carrier}
    (h : ∀ x ∈ S, ∀ y ∈ T, L.obj.obj.pairing x y = 0)
    {v w : L.obj.obj.carrier} (hv : v ∈ Submodule.span ℤ S)
    (hw : w ∈ Submodule.span ℤ T) : L.obj.obj.pairing v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem a ha =>
      induction hw using Submodule.span_induction with
      | mem b hb => exact h a ha b hb
      | zero => exact BilinModuleCat.pairing_zero_right _ a
      | add b c _ _ hb hc =>
          rw [BilinModuleCat.pairing_add_right, hb, hc, add_zero]
      | smul r b _ hb =>
          rw [BilinModuleCat.pairing_smul_right, hb, smul_zero]
  | zero => exact BilinModuleCat.pairing_zero_left _ w
  | add a b _ _ ha hb => rw [BilinModuleCat.pairing_add_left, ha, hb, add_zero]
  | smul r a _ ha => rw [BilinModuleCat.pairing_smul_left, ha, smul_zero]

/-- An orthogonal splitting of the root set: a partition of the roots into two nonempty parts
that pair to zero across the partition. -/
def IsOrthogonalRootSplitting (L : FiniteProjectiveLatticeCat ℤ ℤ) (S : Set L.rootSet) : Prop :=
  S.Nonempty ∧ Sᶜ.Nonempty ∧
    ∀ x ∈ S, ∀ y ∈ Sᶜ, L.obj.obj.pairing (x : L.obj.obj.carrier) (y : L.obj.obj.carrier) = 0

/-- Irreducibility is indecomposability. The root graph is preconnected exactly when the root
set admits no splitting into two nonempty mutually orthogonal parts. -/
theorem preconnected_rootGraph_iff_forall_not_splitting (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    (rootGraph L).Preconnected ↔ ∀ S : Set L.rootSet, ¬ IsOrthogonalRootSplitting L S := by
  constructor
  · rintro hpre S ⟨⟨u, hu⟩, ⟨v, hv⟩, horth⟩
    obtain ⟨p⟩ := hpre u v
    obtain ⟨d, _, hd1, hd2⟩ := p.exists_boundary_dart S hu hv
    exact d.adj.2 (horth _ hd1 _ hd2)
  · intro h u v
    by_contra hr
    refine h {z | (rootGraph L).Reachable u z} ⟨⟨u, SimpleGraph.Reachable.refl u⟩, ⟨v, hr⟩, ?_⟩
    rintro a ha b hb
    by_contra hne
    exact hb (ha.trans (SimpleGraph.Adj.reachable ⟨fun hab => hb (hab ▸ ha), hne⟩))

end FiniteProjectiveLatticeCat

/-- Irreducibility of a root lattice, as the absence of an orthogonal splitting of its root
set. This is `IsIrreducibleRootLattice` restated through
`preconnected_rootGraph_iff_forall_not_splitting`. -/
theorem isIrreducibleRootLattice_iff_forall_not_splitting (L : RootLatticeCat) :
    IsIrreducibleRootLattice L ↔
      L.obj.obj.rootSet.Nonempty ∧
        ∀ S : Set L.obj.obj.rootSet,
          ¬ FiniteProjectiveLatticeCat.IsOrthogonalRootSplitting L.obj.obj S :=
  and_congr_right fun _ =>
    FiniteProjectiveLatticeCat.preconnected_rootGraph_iff_forall_not_splitting L.obj.obj

end LeanCategories.Lattices.Valued
