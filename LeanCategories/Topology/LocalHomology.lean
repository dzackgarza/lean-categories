/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Local singular homology

Definition-level realization of Hatcher FC07-C02-U042.  Local homology at `x`
is the relative singular homology of `(X, X \ {x})`.  Only the chain-complex and
homology carriers are recorded here; excision and locality are result content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open CategoryTheory Limits
open AlgebraicTopology

/-- Singular chains with coefficients in the commutative ring `R`. -/
abbrev singularChainFunctor (R : Type) [CommRing R] :
    TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} R) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)

/-- The inclusion of a subspace as a morphism of topological spaces. -/
def subspaceInclusion (X : Type) [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Relative singular chains `S_*(X,A;R)`, as the cokernel of the chain map
induced by `A ↪ X`. -/
def relativeSingularChainComplex (R : Type) [CommRing R]
    (X : Type) [TopologicalSpace X] (A : Set X) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel ((singularChainFunctor R).map (subspaceInclusion X A))

/-- Relative singular homology `H_n(X,A;R)`. -/
def relativeSingularHomologyModule (R : Type) [CommRing R]
    (n : ℕ) (X : Type) [TopologicalSpace X] (A : Set X) :
    ModuleCat.{0} R :=
  (relativeSingularChainComplex R X A).homology n

/-- Local homology at `x`: `H_n(X, X \ {x}; R)`. -/
def localHomologyModule (R : Type) [CommRing R]
    (n : ℕ) (X : Type) [TopologicalSpace X] (x : X) :
    ModuleCat.{0} R :=
  relativeSingularHomologyModule R n X ({x}ᶜ)

/-- Hatcher's default integral local homology group at `x`. -/
abbrev localIntegralHomology (n : ℕ) (X : Type) [TopologicalSpace X] (x : X) :=
  localHomologyModule ℤ n X x

end LeanCategories.Topology
