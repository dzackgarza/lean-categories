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

The source object is packaged below as the subgroup family together with its
coefficient group/action and the two defining conditions.  No cohomological
axiom is part of this unit.
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

/-- Serre's formation object: an indexed subgroup family together with the
multiplicative coefficient group/action satisfying the indexing and
stabilizer clauses of the definition. -/
structure SerreFormationData
    (G : Type u) [Group G] (X : Type v) where
  /-- The subgroup attached to each source index. -/
  G_E : X → Subgroup G
  /-- The coefficient group. -/
  A : Type w
  /-- Multiplicative group structure on the coefficients. -/
  commGroup : CommGroup A
  /-- Ambient group action on the coefficients. -/
  action : MulDistribMulAction G A
  /-- Serre's closure/finite-index conditions on the subgroup family. -/
  indexing : IsFormationIndexingFamily G_E
  /-- Every coefficient has one of the indexed subgroups as stabilizer. -/
  coefficientAction :
    letI : CommGroup A := commGroup
    letI : MulDistribMulAction G A := action
    IsFormationCoefficientAction G_E A

attribute [instance] SerreFormationData.commGroup SerreFormationData.action

/-- The fixed coefficient carrier `A_E=A^{G_E}` belonging to a formation. -/
def SerreFormationData.fixedElements
    (F : SerreFormationData G X) (E : X) : Set F.A :=
  formationFixedElements F.G_E E F.A

end LeanCategories.Homological
