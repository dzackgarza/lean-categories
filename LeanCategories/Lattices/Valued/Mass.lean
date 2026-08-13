/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Lattices.Valued.ReducedBasis
public import LeanCategories.Lattices.Valued.Theta

/-!
# Finite orthogonal groups and the mass of a genus

An isometry preserves the value of every vector, so it maps each level set of the quadratic form
into itself. In a positive definite lattice those level sets are finite. An isometry is determined
by the images of an integral basis, so the orthogonal group embeds into a finite product of level
sets and is finite. Its order gives the local factor `1 / |O(L)|` of the Smith-Minkowski-Siegel
mass formula.

An isometry carries the orthogonal group of its source to the orthogonal group of its target, so
the order is an invariant of the global isometry class and `isometryClassCard` reads it off the
class. `genus_finite` says the classes of a positive definite genus form a finite set, so summing
the reciprocal orders over that set is a finite sum: that sum is `genusMass`, the mass of the
genus.

`mass` keeps the same sum over an explicit list, for a family presented by representatives rather
than by the genus containing them.
-/

@[expose] public section

noncomputable section

open CategoryTheory LeanCategories.Modules.Bilinear.Valued

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

/-- An isometry identifies the orthogonal groups of its source and target. -/
def orthogonalGroupCongr {L M : FiniteProjectiveLatticeCat ℤ ℤ} (e : L ≅ M) :
    OrthogonalGroup L.obj ≃* OrthogonalGroup M.obj :=
  BilinModuleCat.OrthogonalGroup.congr
    ((isLattice ℤ ℤ).ι.mapIso ((isFiniteProjectiveLattice ℤ ℤ).ι.mapIso e))

/-- The orthogonal-group order is an invariant of the global isometry class. -/
theorem orthogonalGroupCard_congr {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : IsGloballyIsometric L M) : L.orthogonalGroupCard = M.orthogonalGroupCard := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr (orthogonalGroupCongr e).toEquiv

end FiniteProjectiveLatticeCat

/-- The order of the orthogonal group, read off a global isometry class. -/
def isometryClassCard : IntegralLatticeIsometryClass → ℕ :=
  Quotient.lift FiniteProjectiveLatticeCat.orthogonalGroupCard fun _ _ h ↦
    FiniteProjectiveLatticeCat.orthogonalGroupCard_congr h

@[simp]
theorem isometryClassCard_mk (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    isometryClassCard (Quotient.mk globalIsometrySetoid L) = L.orthogonalGroupCard :=
  rfl

/-- The class set of the genus of `L`: the global isometry classes that genus contains. -/
def genusClassSet (L : FiniteProjectiveLatticeCat ℤ ℤ) : Set IntegralLatticeIsometryClass :=
  {q : IntegralLatticeIsometryClass | ∃ M : FiniteProjectiveLatticeCat ℤ ℤ,
    Quotient.mk globalIsometrySetoid M = q ∧ SameGenus L M}

/-- A lattice lies in the class set of its own genus. -/
theorem mk_mem_genusClassSet (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    Quotient.mk globalIsometrySetoid L ∈ genusClassSet L :=
  ⟨L, rfl, sameGenus_refl L⟩

/-- The class set of a positive definite genus is finite. -/
theorem genusClassSet_finite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) : (genusClassSet L).Finite :=
  genus_finite L hL

/-- Positive definiteness is a genus invariant, so every class of a positive definite genus has a
nonzero orthogonal-group order. -/
theorem isometryClassCard_pos_of_mem_genusClassSet {L : FiniteProjectiveLatticeCat ℤ ℤ}
    (hL : IsPositiveDefiniteLattice L) {q : IntegralLatticeIsometryClass}
    (hq : q ∈ genusClassSet L) : 0 < isometryClassCard q := by
  obtain ⟨M, rfl, hgen⟩ := hq
  refine M.orthogonalGroupCard_pos ?_
  rwa [IsPositiveDefiniteLattice, ← signature_eq_of_sameGenus hgen]

/-- **The mass of a genus.** The sum of the reciprocal orthogonal-group orders over the class set
of the genus of `L`, a finite sum by `genus_finite`. -/
def genusMass (L : FiniteProjectiveLatticeCat ℤ ℤ) (hL : IsPositiveDefiniteLattice L) : ℚ :=
  ∑ q ∈ (genusClassSet_finite L hL).toFinset, 1 / (isometryClassCard q : ℚ)

/-- The mass of a genus is positive. -/
theorem genusMass_pos (L : FiniteProjectiveLatticeCat ℤ ℤ) (hL : IsPositiveDefiniteLattice L) :
    0 < genusMass L hL := by
  refine Finset.sum_pos (fun q hq ↦ ?_)
    ⟨Quotient.mk globalIsometrySetoid L,
      (genusClassSet_finite L hL).mem_toFinset.mpr (mk_mem_genusClassSet L)⟩
  have hpos := isometryClassCard_pos_of_mem_genusClassSet hL
    ((genusClassSet_finite L hL).mem_toFinset.mp hq)
  have : (0 : ℚ) < (isometryClassCard q : ℚ) := by exact_mod_cast hpos
  exact one_div_pos.mpr this

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
