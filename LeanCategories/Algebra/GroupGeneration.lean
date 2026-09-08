/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

/-!
# Words in a family of subgroups

Definition-level realization of Munkres FC02-C11-U016.
-/

namespace LeanCategories.Algebra.SubgroupFamily

universe u v

variable {G : Type u} [Group G] {ι : Type v}

/-- A letter from a family of subgroups remembers the subgroup from which the
element was chosen. -/
abbrev Letter (H : ι → Subgroup G) := Σ i : ι, H i

/-- A word in a family of subgroups is a finite sequence of subgroup elements. -/
abbrev Word (H : ι → Subgroup G) := List (Letter H)

/-- Evaluate a subgroup-family word in the ambient group. -/
def eval {H : ι → Subgroup G} : Word H → G :=
  List.prod ∘ List.map (fun a => (a.2 : G))

/-- A family of subgroups generates `G` when every element is represented by a
finite word in elements of the family (FC02-C11-U016). -/
def Generates (H : ι → Subgroup G) : Prop :=
  ∀ g : G, ∃ w : Word H, eval w = g

end LeanCategories.Algebra.SubgroupFamily
