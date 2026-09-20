/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.FormationIndexingData
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Serre formation data

Definition-level realization of Serre FC10-C11-U004.

For an indexed family of finite-index subgroups `E ↦ G_E` and a
multiplicative `G`-module `A`, Serre requires every coefficient element to
have one of the `G_E` as its stabilizer. He writes `A_E = A^{G_E}` for the
elements fixed by `G_E`.

The source conditions are recorded as predicates on supplied data rather
than proof-valued fields of a structure. No cohomological axiom is part of
this unit.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v w

variable {G : Type u} [Group G] {X : Type v}

/-- The coefficient elements fixed by the subgroup attached to the field
`E`; this is Serre's `A_E = A^{G_E}`. -/
def formationFixedElements (G_E : X → Subgroup G) (E : X)
    (A : Type w) [CommGroup A] [MulDistribMulAction G A] : Set A :=
  {a | ∀ g : G_E E, (g : G) • a = a}

/-- Serre's stabilizer condition for the coefficient module: every
coefficient element has stabilizer equal to one of the indexed subgroups. -/
def IsFormationCoefficientAction (G_E : X → Subgroup G)
    (A : Type w) [CommGroup A] [MulDistribMulAction G A] : Prop :=
  ∀ a : A, ∃ E : X, MulAction.stabilizer G a = G_E E

/-- The raw group-and-module form of Serre's formation definition.

This is a predicate, not a structure, so realizing the definition introduces
no proof-valued constructor obligations in Sweep III. -/
def IsSerreFormation (G_E : X → Subgroup G)
    (A : Type w) [CommGroup A] [MulDistribMulAction G A] : Prop :=
  IsFormationIndexingFamily G_E ∧ IsFormationCoefficientAction G_E A

end LeanCategories.Homological
