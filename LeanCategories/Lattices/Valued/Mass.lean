/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Lattices.Valued.Theta

/-!
# Finite orthogonal groups and the mass of a family of lattices

An isometry preserves the value of every vector, so it maps each level set of the quadratic form
into itself. In a positive definite lattice those level sets are finite. An isometry is determined
by the images of an integral basis, so the orthogonal group embeds into a finite product of level
sets and is finite. Its order gives the local factor `1 / |O(L)|` of the Smith-Minkowski-Siegel
mass formula. The mass of a finite family of lattices is the sum of those factors.

Finiteness of a genus is not available in this development, so the family is an explicit list of
lattices, not a genus.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

/-- The orthogonal group of a positive definite lattice is finite. -/
theorem orthogonalGroup_finite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) : Finite (OrthogonalGroup L.obj) := by
  classical
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  set b := Module.Free.chooseBasis ℤ L.obj.obj.carrier with hb
  haveI : ∀ i, Finite (L.representationSet (L.obj.obj.pairing (b i) (b i))) :=
    fun i ↦ (L.representationSet_finite hL _).to_subtype
  refine Finite.of_injective
    (fun g : OrthogonalGroup L.obj ↦ fun i ↦
      (⟨g.1 (b i), g.property (b i) (b i)⟩ :
        L.representationSet (L.obj.obj.pairing (b i) (b i)))) ?_
  intro g h hgh
  refine Subtype.ext (LinearEquiv.toLinearMap_injective (b.ext fun i ↦ ?_))
  exact congrArg Subtype.val (congrFun hgh i)

/-- The order of the orthogonal group of a lattice. -/
def orthogonalGroupCard (L : FiniteProjectiveLatticeCat ℤ ℤ) : ℕ :=
  Nat.card (OrthogonalGroup L.obj)

/-- A positive definite lattice has a nonzero orthogonal-group order. -/
theorem orthogonalGroupCard_pos (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) : 0 < L.orthogonalGroupCard := by
  haveI := L.orthogonalGroup_finite hL
  exact Nat.card_pos

end FiniteProjectiveLatticeCat

/-- The mass of a finite family of lattices: the sum of the reciprocal orthogonal-group orders. -/
def mass (Ls : List (FiniteProjectiveLatticeCat ℤ ℤ)) : ℚ :=
  (Ls.map fun L ↦ (1 : ℚ) / L.orthogonalGroupCard).sum

/-- The mass of a one-element family is the reciprocal orthogonal-group order. -/
@[simp]
theorem mass_singleton (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    mass [L] = 1 / L.orthogonalGroupCard := by
  simp [mass]

/-- The mass of a nonempty family of positive definite lattices is positive. -/
theorem mass_pos {Ls : List (FiniteProjectiveLatticeCat ℤ ℤ)} (hne : Ls ≠ [])
    (hL : ∀ L ∈ Ls, IsPositiveDefiniteLattice L) : 0 < mass Ls := by
  refine List.sum_pos _ ?_ (by simpa using hne)
  intro q hq
  obtain ⟨L, hLs, rfl⟩ := List.mem_map.mp hq
  have hcard := L.orthogonalGroupCard_pos (hL L hLs)
  positivity

end LeanCategories.Lattices.Valued
