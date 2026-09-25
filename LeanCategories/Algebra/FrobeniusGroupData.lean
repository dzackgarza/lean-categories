/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Frobenius group data

Definition-level carrier for Dummit--Foote FC01-C19-U026.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

/-- Dummit--Foote's defining predicate for a Frobenius group with specified
kernel `Q`: `Q` is proper, nontrivial and normal, and every nonidentity
element of `Q` has centralizer contained in `Q`.

The later prime-power, elementary-abelian, cyclic-quotient and irreducibility
hypotheses in §19.3 are standing assumptions for the application, not part of
this definition. -/
def IsFrobeniusGroupWithKernel
    (G : Type u) [Group G] (Q : Subgroup G) : Prop :=
  Q ≠ ⊥ ∧ Q ≠ ⊤ ∧ Q.Normal ∧
    ∀ x : G, x ∈ Q → x ≠ 1 → Subgroup.centralizer {x} ≤ Q

end LeanCategories.Algebra
