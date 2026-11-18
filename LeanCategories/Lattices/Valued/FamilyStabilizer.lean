/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Set.Image

@[expose] public section

/-!
# The stabilizer of a family of lattice vectors under `O(L) × Perm(I)`

For a family `v : I → L` of vectors of a lattice `L`, the group `O(L) × Equiv.Perm I` acts on
families by reindexing and applying the isometry pointwise (`instSMulFamily`,
`instMulActionFamily`). `familyStabilizer L v` is the stabilizer of `v` in that product group —
the subgroup itself, not only its image in `O(L)`; `familyStabilizerImage` is that image, and
`image_range_of_mem_familyStabilizer` records the mathematical content: a stabilizing pair carries
the range of the family onto itself.

This is the consumer item "for a family `v : I → L` of lattice vectors, the stabilizer under
`O(L) × Sym_C(I)` itself" of lean-categories#91. The issue writes `Sym_C(I)`; no cone-preserving
permutation group `Sym_C` exists in this repository (searched: no declaration whose name contains
`Sym_C`, `SymC` or a cone-preserving permutation subgroup), so the action and stabilizer are stated
for the full `Equiv.Perm I`, of which a later `Sym_C(I)` would be a subgroup. The restriction step
itself is `Subgroup.subgroupOf`; what is missing is the definition of `Sym_C(I)`, not the
stabilizer. Full `Equiv.Perm I` is the honest general form here: it is the group acting, and
`Sym_C(I) ≤ Equiv.Perm I` needs only its carrier.

## LC-09 search record

Corpus queries (formalization-corpus API, whole index): `stabilizer product group family vectors`
(0 files), `symmetric group acting on functions orbit stabilizer lattice` (0 files),
`MulAction stabilizer Pi` (0 files). Nothing to port. Local Mathlib hits, all Apache-2.0:
`MulAction.stabilizer` and `MulAction.mem_stabilizer_iff`
(`Mathlib/GroupTheory/GroupAction/Defs.lean:509` and `:519`), `Equiv.Perm` with
`Equiv.Perm.symm_apply_apply`, `Set.mem_range`/`Set.mem_image`. The action instance below is glue:
Mathlib has no `MulAction (M ≃ₗ[R] M) M` and hence no product action of `O(L) × Perm(I)` on
families, so the action is defined on the function `p ↦ fun i ↦ p.1.1 (v (p.2.symm i))`.

## Main declarations

* `instSMulFamily`, `instMulActionFamily`;
* `familyStabilizer`, `mem_familyStabilizer`;
* `familyStabilizerImage`, `mem_familyStabilizerImage`;
* `image_range_of_mem_familyStabilizer`.
-/

namespace LeanCategories.Lattices.Valued

universe u v

variable {R : Type u} [CommRing R]
variable {I : Type v}

/-- The action of `O(L) × Equiv.Perm I` on families of vectors of `L`: reindex by the permutation
and apply the isometry pointwise. -/
instance instSMulFamily (L : IntegralLatticeCat R) :
    SMul (OrthogonalGroup L × Equiv.Perm I) (I → L.obj.carrier) where
  smul p x := fun i => p.1.1 (x (p.2.symm i))

/-- The action of `O(L) × Equiv.Perm I` on families of vectors of `L` is a group action. -/
instance instMulActionFamily (L : IntegralLatticeCat R) :
    MulAction (OrthogonalGroup L × Equiv.Perm I) (I → L.obj.carrier) where
  one_smul x := by
    funext i
    rfl
  mul_smul p q x := by
    funext i
    rfl

/-- The stabilizer of the family `v : I → L.obj.carrier` under `O(L) × Equiv.Perm I`. -/
def familyStabilizer (L : IntegralLatticeCat R) (v : I → L.obj.carrier) :
    Subgroup (OrthogonalGroup L × Equiv.Perm I) :=
  MulAction.stabilizer _ v

/-- Membership: a pair fixes the family exactly when the isometry undoes the reindexing
everywhere. -/
theorem mem_familyStabilizer (L : IntegralLatticeCat R) (v : I → L.obj.carrier)
    (p : OrthogonalGroup L × Equiv.Perm I) :
    p ∈ familyStabilizer L v ↔ ∀ i, p.1.1 (v (p.2.symm i)) = v i := by
  rw [familyStabilizer, MulAction.mem_stabilizer_iff]
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

/-- A stabilizing pair carries the range of the family onto itself. -/
theorem image_range_of_mem_familyStabilizer (L : IntegralLatticeCat R)
    (v : I → L.obj.carrier) {p : OrthogonalGroup L × Equiv.Perm I}
    (hp : p ∈ familyStabilizer L v) :
    p.1.1 '' Set.range v = Set.range v := by
  rw [mem_familyStabilizer] at hp
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨p.2 i, ?_⟩
    simpa using (hp (p.2 i)).symm
  · rintro ⟨i, rfl⟩
    exact ⟨v (p.2.symm i), ⟨p.2.symm i, rfl⟩, hp i⟩

/-- The image of the stabilizer of a family in `O(L)`: the isometries that occur in a stabilizing
pair. This is the subgroup the research preamble presents; `familyStabilizer` is the subgroup of
the product that it is the image of. -/
def familyStabilizerImage (L : IntegralLatticeCat R) (v : I → L.obj.carrier) :
    Subgroup (OrthogonalGroup L) :=
  (familyStabilizer L v).map (MonoidHom.fst (OrthogonalGroup L) (Equiv.Perm I))

/-- Membership in the image: an isometry lies in it exactly when some reindexing makes the pair
stabilize the family. -/
theorem mem_familyStabilizerImage (L : IntegralLatticeCat R) (v : I → L.obj.carrier)
    (g : OrthogonalGroup L) :
    g ∈ familyStabilizerImage L v ↔
      ∃ σ : Equiv.Perm I, ∀ i, g.1.1 (v (σ.symm i)) = v i := by
  rw [familyStabilizerImage, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, (mem_familyStabilizer L v p).mp hp⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨(g, σ), (mem_familyStabilizer L v (g, σ)).mpr hσ, rfl⟩

/-! ## The stabilizer under `O(L) × S` for a subgroup `S` of the permutations

The issue writes `O(L) × Sym_C(I)`. `Sym_C(I)` is a subgroup of `Equiv.Perm I`, and nothing in this
repository names its carrier (see the module docstring above), so the stabilizer is delivered for an
arbitrary `S ≤ Equiv.Perm I` and proved to be the restriction of `familyStabilizer` along the
inclusion `O(L) × S → O(L) × Equiv.Perm I`. Instantiating `S := Sym_C(I)` is then the issue's
statement, with no further work: the one input still missing is that subgroup's carrier.
-/

section Subgroup

variable (S : Subgroup (Equiv.Perm I))

/-- The action of `O(L) × S` on families of vectors of `L`, for a subgroup `S` of the permutations
of the index set. -/
instance instSMulFamilyOfSubgroup (L : IntegralLatticeCat R) :
    SMul (OrthogonalGroup L × S) (I → L.obj.carrier) where
  smul p x := fun i => p.1.1 (x (((p.2 : S) : Equiv.Perm I).symm i))

/-- The action of `O(L) × S` on families of vectors of `L` is a group action. -/
instance instMulActionFamilyOfSubgroup (L : IntegralLatticeCat R) :
    MulAction (OrthogonalGroup L × S) (I → L.obj.carrier) where
  one_smul x := by
    funext i
    rfl
  mul_smul p q x := by
    funext i
    rfl

/-- The stabilizer of the family `v` under `O(L) × S`. -/
def familyStabilizerOfSubgroup (L : IntegralLatticeCat R) (v : I → L.obj.carrier) :
    Subgroup (OrthogonalGroup L × S) :=
  MulAction.stabilizer _ v

/-- Membership in the stabilizer under `O(L) × S`. -/
theorem mem_familyStabilizerOfSubgroup (L : IntegralLatticeCat R) (v : I → L.obj.carrier)
    (p : OrthogonalGroup L × S) :
    p ∈ familyStabilizerOfSubgroup S L v ↔
      ∀ i, p.1.1 (v (((p.2 : S) : Equiv.Perm I).symm i)) = v i := by
  rw [familyStabilizerOfSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

/-- The inclusion `O(L) × S → O(L) × Equiv.Perm I`. -/
def subgroupInclusion (L : IntegralLatticeCat R) :
    OrthogonalGroup L × S →* OrthogonalGroup L × Equiv.Perm I :=
  MonoidHom.prodMap (MonoidHom.id _) S.subtype

/-- **The stabilizer under `O(L) × S` is the stabilizer under `O(L) × Equiv.Perm I`, restricted**:
it is the preimage of `familyStabilizer L v` along `O(L) × S → O(L) × Equiv.Perm I`. At
`S := Sym_C(I)` this is the issue's stabilizer; only that subgroup's carrier is missing. -/
theorem familyStabilizerOfSubgroup_eq_comap (L : IntegralLatticeCat R)
    (v : I → L.obj.carrier) :
    familyStabilizerOfSubgroup S L v
      = (familyStabilizer L v).comap (subgroupInclusion S L) := by
  ext p
  simp only [familyStabilizerOfSubgroup, familyStabilizer, subgroupInclusion,
    Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact h
  · intro h
    exact h

end Subgroup

end LeanCategories.Lattices.Valued
