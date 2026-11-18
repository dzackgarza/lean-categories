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

end LeanCategories.Lattices.Valued
