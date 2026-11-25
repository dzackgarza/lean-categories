/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.GroupPullback
public import LeanCategories.Lattices.Valued.FamilyStabilizer
public import LeanCategories.Lattices.Valued.Standard

@[expose] public section

/-!
# Acceptance tests for lean-categories#91: the lattice items

The lattice-side acceptance items, decided on the smallest input that settles each: the rank-one
lattice `rankOneLattice 1` over `ℤ`, and the constantly zero one-vector family on it.

* "Mathematics wanted" 2 — the orthogonal-sum map `O(L₁) × O(L₂) → O(L₁ ⊕ L₂)` is an injective
  group morphism (`sumHom`, `sumHom_injective`);
* consumer 1 — products of subgroups of lattice orthogonal groups (`one_mem_top`, `prodEquiv`);
* consumer 3, the `Equiv.Perm I` part — the stabilizer of a family of lattice vectors
  (`v`, `one_mem`, `one_mem_image`, `range_fixed`). The issue writes `O(L) × Sym_C(I)`; `Sym_C(I)`
  has no owner in this repository, so the statements are for `Equiv.Perm I`, of which any
  `Sym_C(I)` would be a subgroup.

The `Grp` side of the issue is decided in `Algebra/GroupProductTests.lean`.
-/

open CategoryTheory Limits

namespace LeanCategories.Lattices.Valued

/-- The smallest lattice: the rank-one form `⟨x, y⟩ = x * y` on `ℤ`. -/
abbrev L : IntegralLatticeCat ℤ :=
  rankOneLattice 1

/-- Item 2: the orthogonal-sum map at `rankOneLattice 1`, as a group morphism. -/
noncomputable def sumHom :
    OrthogonalGroup L × OrthogonalGroup L →* OrthogonalGroup (orthogonalSum L L) :=
  integralOrthogonalSumGroupHom L L

/-- Item 2: injectivity, instantiated at the smallest lattice. -/
theorem sumHom_injective : Function.Injective (integralOrthogonalSumGroupHom L L) :=
  integralOrthogonalSumGroupHom_injective L L

/-- Item 3: the identity lies in the product of the top subgroups. -/
theorem one_mem_top :
    (1 : OrthogonalGroup (orthogonalSum L L)) ∈ orthogonalSumSubgroup L L ⊤ ⊤ := by
  rw [mem_orthogonalSumSubgroup]
  exact ⟨1, trivial, 1, trivial, map_one (integralOrthogonalSumGroupHom L L)⟩

/-- Item 3: the product `P₁ × P₂` is isomorphic to its image in `O(L₁ ⊕ L₂)`. -/
noncomputable def prodEquiv :
    ↥((⊤ : Subgroup (OrthogonalGroup L)).prod (⊤ : Subgroup (OrthogonalGroup L))) ≃*
      ↥(orthogonalSumSubgroup L L ⊤ ⊤) :=
  orthogonalSumSubgroupMulEquiv L L ⊤ ⊤

/-- Item 5: the smallest family, the constantly zero vector of `L`. -/
def v : Fin 1 → L.obj.carrier :=
  fun _ => 0

/-- Item 5: the identity pair stabilizes the family. -/
theorem one_mem : (1 : OrthogonalGroup L × Equiv.Perm (Fin 1)) ∈ familyStabilizer L v := by
  rw [mem_familyStabilizer]
  intro _
  simp [v]

/-- Item 5: the identity isometry lies in the image of the stabilizer in `O(L)`. -/
theorem one_mem_image : (1 : OrthogonalGroup L) ∈ familyStabilizerImage L v := by
  rw [mem_familyStabilizerImage]
  exact ⟨1, fun _ => by simp [v]⟩

/-- Item 5: a stabilizing pair carries the range of the family onto itself. -/
theorem range_fixed : (1 : OrthogonalGroup L).1.1 '' Set.range v = Set.range v :=
  image_range_of_mem_familyStabilizer L v one_mem

/-- Item 5, the issue's `Sym_C(I)` form: for **any** subgroup `S` of the permutations of the index
set — in particular any `Sym_C(I)` — the stabilizer of the family under `O(L) × S` is the
stabilizer under `O(L) × Equiv.Perm I` restricted along the inclusion. -/
theorem stabilizer_of_subgroup (S : Subgroup (Equiv.Perm (Fin 1))) :
    familyStabilizerOfSubgroup S L v
      = (familyStabilizer L v).comap (subgroupInclusion S L) :=
  familyStabilizerOfSubgroup_eq_comap S L v

/-- The full permutation group is the case `S = ⊤`. -/
theorem stabilizer_top :
    familyStabilizerOfSubgroup (⊤ : Subgroup (Equiv.Perm (Fin 1))) L v
      = (familyStabilizer L v).comap (subgroupInclusion ⊤ L) :=
  familyStabilizerOfSubgroup_eq_comap ⊤ L v

/-- The identity pair lies in the stabilizer under any `S`, so the restricted stabilizer is not
empty and the construction is not vacuous. -/
theorem one_mem_stabilizer_of_subgroup (S : Subgroup (Equiv.Perm (Fin 1))) :
    (1 : OrthogonalGroup L × S) ∈ familyStabilizerOfSubgroup S L v := by
  rw [mem_familyStabilizerOfSubgroup]
  intro _
  simp [v]

/-- The one-colour colouring of the index set: `Sym_C(I)` is then all of `Equiv.Perm I`. -/
def trivialColouring : Fin 1 → Bool :=
  fun _ => true

/-- Item 5 in the issue's literal form: the stabilizer under `O(L) × Sym_C(I)` is the general
stabilizer at `S := Sym_C(I)`, and hence the full stabilizer restricted. -/
theorem stabilizer_symC :
    colouredFamilyStabilizer trivialColouring L v
      = (familyStabilizer L v).comap
          (subgroupInclusion (colourPreservingPerms trivialColouring) L) :=
  colouredFamilyStabilizer_eq_comap trivialColouring L v

/-- At the one-colour colouring every permutation preserves the colouring. -/
theorem symC_trivial (σ : Equiv.Perm (Fin 1)) :
    σ ∈ colourPreservingPerms trivialColouring :=
  mem_colourPreservingPerms trivialColouring |>.mpr fun _ => rfl

/-- The identity pair lies in the issue's stabilizer, so the construction is not vacuous. -/
theorem one_mem_symC :
    (1 : OrthogonalGroup L × colourPreservingPerms trivialColouring) ∈
      colouredFamilyStabilizer trivialColouring L v := by
  rw [mem_colouredFamilyStabilizer]
  intro _
  simp [v]

/-- A colouring with two colours on two indices, to see that `Sym_C(I)` can be proper. -/
def twoColour : Fin 2 → Bool :=
  fun i => i == 0

/-- The transposition does not preserve the two-colour colouring, so `Sym_C(I)` is a proper
subgroup of `Equiv.Perm I` in general. -/
theorem swap_not_mem_twoColour :
    Equiv.swap (0 : Fin 2) 1 ∉ colourPreservingPerms twoColour := by
  intro h
  have h0 := h 0
  simp [twoColour, Equiv.swap_apply_left] at h0

end LeanCategories.Lattices.Valued
