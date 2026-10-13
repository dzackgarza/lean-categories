/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.CohomologyRingData
public import LeanCategories.Topology.TwoSheetedTransferData

/-!
# Finite-sheeted transfer data

Definition-level realization of Hatcher FC07-C03-U136.

For an n-sheeted covering p : E -> X, Hatcher's transfer sends a singular
simplex to the sum of all n of its distinct lifts.  The resulting degreewise
maps form a chain map and hence induce transfer maps in homology and
cohomology.

Sweep III records the source data without proving the lifting, boundary, or
descent theorems.  The finite list of lifts is specified by a Fin n family
which is injective, consists entirely of lifts, and exhausts every lift.
Degreewise transfer maps, and the induced homology/cohomology maps, are
represented as candidates satisfying their exact generator/representative
graphs. No arbitrary map is selected before the corresponding theorems.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped BigOperators

/-- A covering has exactly n sheets when every fibre is equivalent to Fin n. -/
def IsFiniteSheetedCovering
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (n : ℕ) : Prop :=
  IsCoveringMap p ∧
    ∀ x : X, Nonempty (Fin n ≃ {e : E // p e = x})

/-- Singular chains with coefficients in R. -/
abbrev singularChainComplexWithCoefficients
    (R : Type) [CommRing R]
    (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat R) ℕ :=
  (singularSSet X).chainComplex (ModuleCat.of R R)

/-- A Fin n family lists exactly all singular-simplex lifts of sigma. -/
def AreExactlyFiniteSingularSimplexLifts
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (sheets : ℕ) {k : ℕ}
    (σ : (singularSSet X).obj (Opposite.op (SimplexCategory.mk k)))
    (lifts : Fin sheets →
      (singularSSet E).obj (Opposite.op (SimplexCategory.mk k))) : Prop :=
  Function.Injective lifts ∧
    (∀ i, IsSingularSimplexLift p σ (lifts i)) ∧
      ∀ τ : (singularSSet E).obj (Opposite.op (SimplexCategory.mk k)),
        IsSingularSimplexLift p σ τ → ∃ i, τ = lifts i

/-- The source generator formula for the degree-k finite-sheeted transfer. -/
def IsFiniteSheetedTransferComponent
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R]
    (p : C(E, X)) (sheets k : ℕ)
    (T : (singularChainComplexWithCoefficients R X).X k ⟶
      (singularChainComplexWithCoefficients R E).X k) : Prop :=
  ∀ σ : (singularSSet X).obj (Opposite.op (SimplexCategory.mk k)),
    ∃ lifts : Fin sheets →
      (singularSSet E).obj (Opposite.op (SimplexCategory.mk k)),
      AreExactlyFiniteSingularSimplexLifts p sheets σ lifts ∧
        (singularSSet X).ιChainComplex σ ≫ T =
          ∑ i : Fin sheets, (singularSSet E).ιChainComplex (lifts i)

/-- Source-faithful degree-`k` finite-sheeted transfer data: a candidate
linear map together with Hatcher's exact all-lifts generator graph. -/
abbrev FiniteSheetedTransferComponentData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R]
    (p : C(E, X)) (sheets k : ℕ)
    :
    Type _ :=
  {T :
      (singularChainComplexWithCoefficients R X).X k ⟶
        (singularChainComplexWithCoefficients R E).X k //
    IsFiniteSheetedTransferComponent R p sheets k T}

/-- Degreewise data underlying the finite-sheeted transfer chain map.

The chain-map equation is a Sweep-IV result and is not a field. -/
abbrev FiniteSheetedTransferData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R]
    (p : C(E, X)) (sheets : ℕ) (_hp : IsFiniteSheetedCovering p sheets) :=
  ∀ k : ℕ, FiniteSheetedTransferComponentData R p sheets k

/-- Type of a homology transfer candidate in degree k. -/
abbrev FiniteSheetedHomologyTransferHomData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R] (k : ℕ) :=
  (singularChainComplexWithCoefficients R X).homology k ⟶
    (singularChainComplexWithCoefficients R E).homology k

/-- Representative-level specification of the induced homology transfer. -/
def IsFiniteSheetedHomologyTransferData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R]
    (p : C(E, X)) (sheets : ℕ)
    (k : ℕ)
    (τ : FiniteSheetedTransferComponentData R p sheets k)
    (T : FiniteSheetedHomologyTransferHomData (E := E) (X := X) R k) : Prop :=
  let KX := singularChainComplexWithCoefficients R X
  let KE := singularChainComplexWithCoefficients R E
  ∀ x : KX.cycles k,
    ∃ z : KE.cycles k,
      (KE.iCycles k).hom z = τ.1.hom ((KX.iCycles k).hom x) ∧
        T.hom ((KX.homologyπ k).hom x) = (KE.homologyπ k).hom z

/-- Source-faithful homology-transfer data relative to a supplied degreewise
chain transfer component. -/
abbrev FiniteSheetedHomologyTransferData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R]
    (p : C(E, X)) (sheets k : ℕ)
    (τ : FiniteSheetedTransferComponentData R p sheets k) :=
  {T : FiniteSheetedHomologyTransferHomData (E := E) (X := X) R k //
    IsFiniteSheetedHomologyTransferData R p sheets k τ T}

/-- Type of a cohomology transfer candidate in degree k. -/
abbrev FiniteSheetedCohomologyTransferHomData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R] (k : ℕ) :=
  singularCohomologyModuleData R (TopCat.of E) (ModuleCat.of R R) k ⟶
    singularCohomologyModuleData R (TopCat.of X) (ModuleCat.of R R) k

/-- Representative-level specification of the induced cohomology transfer:
an upstairs cocycle is pulled back along the chain transfer. -/
def IsFiniteSheetedCohomologyTransferData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R]
    (p : C(E, X)) (sheets : ℕ)
    (k : ℕ)
    (τ : FiniteSheetedTransferComponentData R p sheets k)
    (T : FiniteSheetedCohomologyTransferHomData (E := E) (X := X) R k) : Prop :=
  let KX := singularCochainComplexData R (TopCat.of X) (ModuleCat.of R R)
  let KE := singularCochainComplexData R (TopCat.of E) (ModuleCat.of R R)
  ∀ x : KE.cycles k,
    ∃ y : KX.cycles k,
      (KX.iCycles k).hom y = τ.1 ≫ (KE.iCycles k).hom x ∧
        T.hom ((KE.homologyπ k).hom x) = (KX.homologyπ k).hom y

/-- Source-faithful cohomology-transfer data relative to a supplied degreewise
chain transfer component. -/
abbrev FiniteSheetedCohomologyTransferData
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (R : Type) [CommRing R]
    (p : C(E, X)) (sheets k : ℕ)
    (τ : FiniteSheetedTransferComponentData R p sheets k) :=
  {T : FiniteSheetedCohomologyTransferHomData (E := E) (X := X) R k //
    IsFiniteSheetedCohomologyTransferData R p sheets k τ T}

end LeanCategories.Topology
