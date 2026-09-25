/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.LocalHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Local-homology orientation data

Definition-level realization of Hatcher FC07-C03-U041 and FC07-C03-U044.

An R-orientation of an n-manifold is a locally consistent choice, at every
point x, of a generator of H_n(M, M minus {x}; R). The integral definition is
the specialization R = Z.

The representation issue is the canonical map from H_n(M,M minus U;R) to
H_n(M,M minus {x};R) for x in U. Constructing it directly by cokernel.map asks
for a commuting-square proof. Since both relative complexes are cokernels of
maps into the same ambient singular chain complex, the desired map is instead
characterized by its quotient graph and selected by Classical.epsilon.

Local consistency and generation are then literal predicates over those
selected maps. No excision, well-definedness, existence of orientations, or
orientation-covering comparison is proved here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories.Topology

/-- The singular-chain map whose cokernel is the relative complex for (X,A). -/
def relativeSubspaceChainInclusionData
    (R : Type) [CommRing R]
    (X : Type) [TopologicalSpace X] (A : Set X) :
    (singularChainFunctor R).obj (TopCat.of A) ⟶
      (singularChainFunctor R).obj (TopCat.of X) :=
  (singularChainFunctor R).map (subspaceInclusion X A)

/-- Type of a candidate map between two relative singular-chain complexes. -/
abbrev RelativeSingularRestrictionChainMapData
    (R : Type) [CommRing R]
    (X : Type) [TopologicalSpace X] (A B : Set X) :=
  relativeSingularChainComplex R X A ⟶
    relativeSingularChainComplex R X B

/-- Exact cokernel graph for the canonical relative-chain map.

For a source inclusion A subset B, the result layer proves that a map with
this graph exists. No commuting-square proof is used in this definition. -/
def IsRelativeSingularRestrictionChainMapData
    (R : Type) [CommRing R]
    (X : Type) [TopologicalSpace X] (A B : Set X)
    (φ : RelativeSingularRestrictionChainMapData R X A B) : Prop :=
  cokernel.π (relativeSubspaceChainInclusionData R X A) ≫ φ =
    cokernel.π (relativeSubspaceChainInclusionData R X B)

/-- The canonical relative-chain map, selected from its quotient graph. -/
def relativeSingularRestrictionChainMapData
    (R : Type) [CommRing R]
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    RelativeSingularRestrictionChainMapData R X A B :=
  Classical.epsilon
    (IsRelativeSingularRestrictionChainMapData R X A B)

/-- The induced map on relative singular homology. -/
def relativeSingularRestrictionHomologyMapData
    (R : Type) [CommRing R]
    (n : ℕ) (X : Type) [TopologicalSpace X] (A B : Set X) :
    relativeSingularHomologyModule R n X A ⟶
      relativeSingularHomologyModule R n X B :=
  HomologicalComplex.homologyMap
    (relativeSingularRestrictionChainMapData R X A B) n

/-- A local homology class is a generator when its singleton span is top. -/
def IsLocalOrientationGeneratorData
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] (x : M)
    (mu : localHomologyModule R n M x) : Prop :=
  Submodule.span R {mu} = ⊤

/-- A candidate pointwise choice of local orientation classes. -/
abbrev ROrientationCandidateData
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] :=
  (x : M) → localHomologyModule R n M x

/-- Hatcher's local-consistency predicate for an R-orientation.

Around each point x there is an open neighborhood U and one class in
H_n(M,M minus U;R) whose image at every y in U is the selected local generator
at y. -/
def IsROrientationData
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (mu : ROrientationCandidateData R n M) : Prop :=
  (∀ x : M, IsLocalOrientationGeneratorData R n M x (mu x)) ∧
    ∀ x : M,
      ∃ U : Set M,
        IsOpen U ∧
          x ∈ U ∧
            ∃ muU : relativeSingularHomologyModule R n M Uᶜ,
              ∀ y : M, y ∈ U →
                (relativeSingularRestrictionHomologyMapData
                  R n M Uᶜ ({y} : Set M)ᶜ).hom muU = mu y

/-- An n-manifold is R-orientable when it admits an R-orientation. Manifold
structure itself is an ambient hypothesis of the source unit. -/
def IsROrientableData
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] : Prop :=
  ∃ mu : ROrientationCandidateData R n M, IsROrientationData R n M mu

/-- Hatcher's ordinary integral orientation predicate. -/
abbrev IsIntegralOrientationData
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (mu : ROrientationCandidateData ℤ n M) : Prop :=
  IsROrientationData ℤ n M mu

/-- Hatcher's ordinary orientability predicate. -/
abbrev IsOrientableData
    (n : ℕ) (M : Type) [TopologicalSpace M] : Prop :=
  IsROrientableData ℤ n M

end LeanCategories.Topology
