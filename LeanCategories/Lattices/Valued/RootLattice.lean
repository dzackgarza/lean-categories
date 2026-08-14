/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DefiniteIndefinite
public import LeanCategories.Lattices.Valued.RootSystem
public import LeanCategories.Lattices.Valued.Theta
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The root set of a definite lattice

`DefiniteIndefinite.lean` cuts the root locus out of the definite category by a spanning
condition on the vectors of self-pairing `±1` or `±2`. This file supplies the first layer of
theory that locus needs before any classification statement can be made.

Three things are established.

* The root set is finite. A root lies in one of four value level sets, and `Theta.lean` shows
  each level set of a positive definite lattice is finite. Negation of the form carries the
  negative definite case to the positive definite one, so the whole definite locus is covered.
* Every root is reflective in the sense of `Mathlib.LinearAlgebra.RootSystem.OfBilinear`,
  because `±1` and `±2` all divide `2`. The root set therefore sits inside the reflective
  vectors that `RootSystem.lean` assembles into a Mathlib root pairing, and a value level set
  is carried into itself by the reflections in its own members.
* The root graph joins two distinct roots when they are not orthogonal. Irreducibility of a
  root lattice is preconnectedness of that graph on a nonempty root set.

The classification input is the Cauchy-Schwarz bound: two roots of norm `2` in a positive
definite lattice that are neither equal nor opposite pair to `-1`, `0`, or `1`. Expanding the
squares of the sum and the difference gives `4 ± 2b(x, y) > 0`, and the two boundary values are
exactly the excluded cases. This repository takes its ADE lattices negative definite, so the
same bound is restated there for roots of norm `-2`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

/-- The roots of a finite integral lattice: the vectors of self-pairing `±1` or `±2`. -/
def rootSet (L : FiniteProjectiveLatticeCat ℤ ℤ) : Set L.obj.obj.carrier :=
  {x | IsRoot L.obj x}

/-- Membership in the root set is the root condition. -/
@[simp]
theorem mem_rootSet {L : FiniteProjectiveLatticeCat ℤ ℤ} {x : L.obj.obj.carrier} :
    x ∈ L.rootSet ↔ IsRoot L.obj x :=
  Iff.rfl

/-- Expansion of the self-pairing of a sum. -/
theorem pairing_add_self (L : FiniteProjectiveLatticeCat ℤ ℤ) (x y : L.obj.obj.carrier) :
    L.obj.obj.pairing (x + y) (x + y) =
      L.obj.obj.pairing x x + 2 * L.obj.obj.pairing x y + L.obj.obj.pairing y y := by
  rw [BilinModuleCat.pairing_add_left, BilinModuleCat.pairing_add_right,
    BilinModuleCat.pairing_add_right, L.obj.property.2 y x]
  ring

/-- Expansion of the self-pairing of a difference. -/
theorem pairing_sub_self (L : FiniteProjectiveLatticeCat ℤ ℤ) (x y : L.obj.obj.carrier) :
    L.obj.obj.pairing (x - y) (x - y) =
      L.obj.obj.pairing x x - 2 * L.obj.obj.pairing x y + L.obj.obj.pairing y y := by
  have hsymm := L.obj.property.2 y x
  change L.obj.obj.bilinMap (x - y) (x - y) = _
  simp only [map_sub, LinearMap.sub_apply]
  change L.obj.obj.pairing x x - L.obj.obj.pairing y x -
    (L.obj.obj.pairing x y - L.obj.obj.pairing y y) = _
  rw [hsymm]
  ring

/-- The root set is the union of the four value level sets `±1` and `±2`. -/
theorem rootSet_eq_union (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    L.rootSet =
      L.representationSet 2 ∪ L.representationSet (-2) ∪
        L.representationSet 1 ∪ L.representationSet (-1) := by
  ext x
  simp only [mem_rootSet, Set.mem_union, mem_representationSet]
  change (L.obj.obj.pairing x x = 2 ∨ L.obj.obj.pairing x x = -2 ∨
    L.obj.obj.pairing x x = 1 ∨ L.obj.obj.pairing x x = -1) ↔ _
  tauto

/-- Negating the form of a negative definite lattice makes it positive definite. -/
theorem isPositiveDefiniteLattice_opposite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) :
    IsPositiveDefiniteLattice (oppositeFiniteProjectiveLattice L) := by
  have hsig := integralSignature_opposite L
  change IsPositiveDefiniteSignature (integralSignature (oppositeFiniteProjectiveLattice L))
  rw [hsig]
  revert hL
  change IsNegativeDefiniteSignature (integralSignature L) → _
  generalize integralSignature L = s
  obtain ⟨p, n, z⟩ := s
  simp only [IsPositiveDefiniteSignature, IsNegativeDefiniteSignature]
  tauto

/-- Negating the form negates the value that a level set records. -/
theorem representationSet_opposite (L : FiniteProjectiveLatticeCat ℤ ℤ) (n : ℤ) :
    (oppositeFiniteProjectiveLattice L).representationSet n = L.representationSet (-n) := by
  ext x
  simp only [mem_representationSet]
  change (oppositeLattice L.obj).obj.pairing x x = n ↔ _
  rw [oppositeLattice_pairing, neg_eq_iff_eq_neg]
  exact Iff.rfl

/-- The vectors of a fixed value in a definite lattice form a finite set. -/
theorem representationSet_finite_of_isDefinite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : isDefiniteLattice L) (n : ℤ) : (L.representationSet n).Finite := by
  rcases hL with hpos | hneg
  · exact L.representationSet_finite hpos n
  · have hfin := (oppositeFiniteProjectiveLattice L).representationSet_finite
      (isPositiveDefiniteLattice_opposite L hneg) (-n)
    rwa [representationSet_opposite, neg_neg] at hfin

/-- The roots of a definite lattice form a finite set. -/
theorem rootSet_finite_of_isDefinite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : isDefiniteLattice L) : L.rootSet.Finite := by
  rw [rootSet_eq_union]
  exact ((((L.representationSet_finite_of_isDefinite hL 2).union
    (L.representationSet_finite_of_isDefinite hL (-2))).union
      (L.representationSet_finite_of_isDefinite hL 1)).union
        (L.representationSet_finite_of_isDefinite hL (-1)))

/-- Every root is a reflective vector: its self-pairing divides `2`. -/
theorem isReflective_of_isRoot (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {x : L.obj.obj.carrier} (hx : IsRoot L.obj x) :
    LinearMap.IsReflective L.obj.obj.bilinMap x := by
  refine LinearMap.IsReflective.of_dvd_two _ ?_
  change L.obj.obj.pairing x x ∣ 2
  rcases hx with h | h | h | h <;> rw [h] <;> decide

/-- The root set of a lattice sits inside its reflective vectors. -/
theorem rootSet_subset_reflectiveRoot (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    L.rootSet ⊆ {x | IsReflectiveRoot L.obj x} :=
  fun _ hx => L.isReflective_of_isRoot hx

/-- The reflection step of the classification. Two vectors of the same value `n` whose pairing
is half of `n` differ by a vector of value `n` again. For `n = 2` this says that two roots
pairing to `1` reflect onto each other, and for `n = -2` it says the same in the negative
definite convention. -/
theorem pairing_sub_self_eq (L : FiniteProjectiveLatticeCat ℤ ℤ) {n : ℤ}
    {x y : L.obj.obj.carrier} (hx : L.obj.obj.pairing x x = n)
    (hy : L.obj.obj.pairing y y = n) (hxy : 2 * L.obj.obj.pairing x y = n) :
    L.obj.obj.pairing (y - x) (y - x) = n := by
  rw [pairing_sub_self, L.obj.property.2 y x, hxy, hx, hy]
  ring

/-- The Cauchy-Schwarz bound. Two roots of norm `2` in a positive definite lattice that are
neither equal nor opposite pair to `-1`, `0`, or `1`. -/
theorem abs_pairing_le_one_of_isPositiveDefinite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) {x y : L.obj.obj.carrier}
    (hx : L.obj.obj.pairing x x = 2) (hy : L.obj.obj.pairing y y = 2)
    (hne : x ≠ y) (hopp : x ≠ -y) : |L.obj.obj.pairing x y| ≤ 1 := by
  have hsub : 0 < L.obj.obj.pairing (x - y) (x - y) :=
    L.pairing_self_pos hL (sub_ne_zero.mpr hne)
  have hadd : 0 < L.obj.obj.pairing (x + y) (x + y) := by
    refine L.pairing_self_pos hL fun h => hopp ?_
    exact eq_neg_of_add_eq_zero_left h
  rw [pairing_sub_self, hx, hy] at hsub
  rw [pairing_add_self, hx, hy] at hadd
  rw [abs_le]
  omega

/-- The Cauchy-Schwarz bound in the negative definite convention this repository uses for its
ADE lattices: two roots of norm `-2` that are neither equal nor opposite pair to `-1`, `0`, or
`1`. -/
theorem abs_pairing_le_one_of_isNegativeDefinite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) {x y : L.obj.obj.carrier}
    (hx : L.obj.obj.pairing x x = -2) (hy : L.obj.obj.pairing y y = -2)
    (hne : x ≠ y) (hopp : x ≠ -y) : |L.obj.obj.pairing x y| ≤ 1 := by
  have hxo : (oppositeFiniteProjectiveLattice L).obj.obj.pairing x x = 2 := by
    change (oppositeLattice L.obj).obj.pairing x x = 2
    rw [oppositeLattice_pairing, hx]
    ring
  have hyo : (oppositeFiniteProjectiveLattice L).obj.obj.pairing y y = 2 := by
    change (oppositeLattice L.obj).obj.pairing y y = 2
    rw [oppositeLattice_pairing, hy]
    ring
  have h := abs_pairing_le_one_of_isPositiveDefinite (oppositeFiniteProjectiveLattice L)
    (isPositiveDefiniteLattice_opposite L hL) hxo hyo hne hopp
  change |(oppositeLattice L.obj).obj.pairing x y| ≤ 1 at h
  rwa [oppositeLattice_pairing, abs_neg] at h

/-- The root graph of a lattice. Two distinct roots are adjacent when they are not
orthogonal. -/
def rootGraph (L : FiniteProjectiveLatticeCat ℤ ℤ) : SimpleGraph L.rootSet where
  Adj x y := x ≠ y ∧ L.obj.obj.pairing x y ≠ 0
  symm := ⟨fun x y hxy =>
    ⟨hxy.1.symm, fun h => hxy.2 (by rw [L.obj.property.2 (x : L.obj.obj.carrier) y, h])⟩⟩
  loopless := ⟨fun _ hx => hx.1 rfl⟩

/-- Adjacency in the root graph is non-orthogonality of distinct roots. -/
@[simp]
theorem rootGraph_adj {L : FiniteProjectiveLatticeCat ℤ ℤ} {x y : L.rootSet} :
    (rootGraph L).Adj x y ↔ x ≠ y ∧ L.obj.obj.pairing x y ≠ 0 :=
  Iff.rfl

end FiniteProjectiveLatticeCat

/-- A definite root lattice is irreducible when its roots are nonempty and its root graph is
preconnected. An orthogonal decomposition into two proper root sublattices would split the
root graph into two mutually non-adjacent parts, so preconnectedness is the indecomposability
condition that the classification runs on. -/
def IsIrreducibleRootLattice (L : RootLatticeCat) : Prop :=
  L.obj.obj.rootSet.Nonempty ∧ (FiniteProjectiveLatticeCat.rootGraph L.obj.obj).Preconnected

/-- The roots of an irreducible root lattice are pairwise reachable in the root graph. -/
theorem reachable_of_isIrreducibleRootLattice {L : RootLatticeCat}
    (h : IsIrreducibleRootLattice L) (x y : L.obj.obj.rootSet) :
    (FiniteProjectiveLatticeCat.rootGraph L.obj.obj).Reachable x y :=
  h.2 x y

end LeanCategories.Lattices.Valued
