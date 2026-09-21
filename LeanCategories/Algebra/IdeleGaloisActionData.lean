/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Raw Galois-action data on idèles

Definition-level realization of Neukirch FC09-C06-U019.

For an idèle `α` of a Galois extension and `σ ∈ Gal(L/K)`, Neukirch
defines the conjugate idèle by the component formula

`(σ α)_(σ P) = σ(α_P)`.

The checked ClassFieldTheory reference proves that this component formula
preserves the restricted product and packages it as a genuine action by group
automorphisms.  Those preservation and action-law proofs are result content.
Sweep III records the maps occurring in the formula, states the formula as a
predicate on that raw data, and records the corresponding fixed-point carrier.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe uG uI uP uC

/-- Raw data occurring in the component formula for the Galois action on
idèles.

`placeMap σ P` is the place `σP`, `localMap σ P` is conjugation from the
`P`-component to the `σP`-component, `component P α` is `α_P`, and
`act σ α` is the proposed conjugate idèle.  No action or restricted-product
law is bundled into the data. -/
structure IdeleGaloisActionData
    (G : Type uG) (I : Type uI) (Place : Type uP)
    (Local : Place → Type uC) where
  placeMap : G → Place → Place
  localMap :
    (σ : G) → (P : Place) →
      Local P → Local (placeMap σ P)
  component : (P : Place) → I → Local P
  act : G → I → I

/-- Neukirch's defining coordinate formula
`(σ α)_(σ P) = σ(α_P)` for raw idèle-action data.

That this formula determines an idèle and satisfies the group-action and
automorphism laws is deliberately not part of this predicate. -/
def IsIdeleGaloisActionFormulaData
    {G : Type uG} {I : Type uI} {Place : Type uP}
    {Local : Place → Type uC}
    (D : IdeleGaloisActionData G I Place Local) : Prop :=
  ∀ (σ : G) (α : I) (P : Place),
    D.component (D.placeMap σ P) (D.act σ α) =
      D.localMap σ P (D.component P α)

/-- The raw fixed-idèle carrier attached to a supplied action map:
`I^G = {α | σ α = α for every σ}`.

Once the action laws are established, this set is the underlying carrier of
the usual fixed subgroup. -/
def ideleGaloisFixedPointsData
    {G : Type uG} {I : Type uI} {Place : Type uP}
    {Local : Place → Type uC}
    (D : IdeleGaloisActionData G I Place Local) : Set I :=
  {α | ∀ σ : G, D.act σ α = α}

end LeanCategories.Algebra
