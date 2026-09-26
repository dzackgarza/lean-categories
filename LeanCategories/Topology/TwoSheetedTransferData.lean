/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Two-sheeted singular-chain transfer data

Definition-level realization of Hatcher FC07-C02-U089.

For a two-sheeted covering `p : Xtilde → X`, Hatcher's transfer with
`ZMod 2` coefficients sends a singular simplex to the sum of its two lifts.
Sweep III records exactly the degreewise linear maps characterized by that
generator formula.

The existence and uniqueness of the two lifts, compatibility with the
singular boundary, the resulting chain-map structure, and short exactness of
the transfer sequence are result clauses. They are deliberately not bundled
as constructor fields here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open AlgebraicTopology CategoryTheory Limits

/-- A covering has exactly two sheets when every fibre consists of exactly
two distinct points. -/
def IsTwoSheetedCovering {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) : Prop :=
  IsCoveringMap p ∧
    ∀ x : X, ∃ e₀ e₁ : E,
      e₀ ≠ e₁ ∧ p e₀ = x ∧ p e₁ = x ∧
        ∀ e : E, p e = x → e = e₀ ∨ e = e₁

/-- The singular simplicial set of a topological space. -/
abbrev singularSSet (X : Type) [TopologicalSpace X] : SSet :=
  TopCat.toSSet.obj (TopCat.of X)

/-- The coefficient object `Z/2` in its module category. -/
abbrev modTwoCoefficient : ModuleCat (ZMod 2) :=
  ModuleCat.of (ZMod 2) (ZMod 2)

/-- Singular chains with `Z/2` coefficients. -/
abbrev modTwoSingularChainComplex (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  (singularSSet X).chainComplex modTwoCoefficient

/-- A singular simplex upstairs is a lift of `σ` when applying the covering
map degreewise in the singular simplicial set gives `σ`. -/
def IsSingularSimplexLift {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) {n : ℕ}
    (σ : (singularSSet X).obj (Opposite.op (SimplexCategory.mk n)))
    (σ' : (singularSSet E).obj (Opposite.op (SimplexCategory.mk n))) : Prop :=
  (TopCat.toSSet.map (TopCat.ofHom p)).app
      (Opposite.op (SimplexCategory.mk n)) σ' = σ

/-- `σ₀,σ₁` are exactly the two singular-simplex lifts of `σ`. -/
def AreExactlyTwoSingularSimplexLifts
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) {n : ℕ}
    (σ : (singularSSet X).obj (Opposite.op (SimplexCategory.mk n)))
    (σ₀ σ₁ : (singularSSet E).obj (Opposite.op (SimplexCategory.mk n))) : Prop :=
  IsSingularSimplexLift p σ σ₀ ∧
    IsSingularSimplexLift p σ σ₁ ∧
    σ₀ ≠ σ₁ ∧
      ∀ τ : (singularSSet E).obj (Opposite.op (SimplexCategory.mk n)),
        IsSingularSimplexLift p σ τ → τ = σ₀ ∨ τ = σ₁

/-- The source generator formula characterizing the degree-`n`
two-sheeted transfer: every singular simplex is sent to the sum of its two
lifts. -/
def IsTwoSheetedTransferComponent
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (n : ℕ)
    (T : (modTwoSingularChainComplex X).X n ⟶
      (modTwoSingularChainComplex E).X n) : Prop :=
  ∀ σ : (singularSSet X).obj (Opposite.op (SimplexCategory.mk n)),
    ∃ σ₀ σ₁ : (singularSSet E).obj (Opposite.op (SimplexCategory.mk n)),
      AreExactlyTwoSingularSimplexLifts p σ σ₀ σ₁ ∧
        (singularSSet X).ιChainComplex σ ≫ T =
          (singularSSet E).ιChainComplex σ₀ +
            (singularSSet E).ιChainComplex σ₁

/-- Source-faithful degree-`n` two-sheeted transfer data: a linear map
together with Hatcher's exact sum-of-the-two-lifts generator graph. -/
abbrev TwoSheetedTransferComponentData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (n : ℕ) :
    Type _ :=
  {T :
      (modTwoSingularChainComplex X).X n ⟶
        (modTwoSingularChainComplex E).X n //
    IsTwoSheetedTransferComponent p n T}

/-- The degreewise linear data underlying Hatcher's transfer. The equation
`d τ = τ d` is deliberately not a field: it is the result that upgrades this
family to a chain map. -/
abbrev TwoSheetedTransferData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) :=
  ∀ n : ℕ, TwoSheetedTransferComponentData p n

end LeanCategories.Topology
