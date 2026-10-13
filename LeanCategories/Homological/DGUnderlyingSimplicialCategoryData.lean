/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Underlying simplicial-category data of a differential graded category

Definition-level realization of Kerodon FC17-KER-U00899 (tag 00SE).

For an integer-indexed chain complex `K` of abelian groups, Kerodon's
generalized Eilenberg--MacLane object depends only on the nonnegative degrees:
restrict along `ℕ ↪ ℤ`, apply inverse Dold--Kan, and forget the module
structure. Proposition 2.5.9.1 (tag 00SD) supplies the Alexander--Whitney lax
monoidal maps. Construction 2.5.9.2 then composes those maps with the identity
and composition maps of a DG category.

Sweep III records exactly that construction data.  The lax-monoidal coherence
of the Alexander--Whitney maps and the identity/associativity laws for the
resulting simplicial category are proposition/result-layer obligations and are
not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory MonoidalCategory

universe u

/-- The integer-indexed chain-complex category used for Kerodon's DG categories. -/
abbrev DGChainComplex := ChainComplex (ModuleCat ℤ) ℤ

/-- Kerodon's nonnegative restriction of an integer-indexed chain complex. -/
def dgNonnegativePart :
    DGChainComplex ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  ComplexShape.embeddingUpNat.op.restrictionFunctor (ModuleCat ℤ)

/-- The monoidal structure on integer-indexed chain complexes routed by
FC17-KER-U00790: transport the native cochain-complex tensor structure along
the chain/cochain reindexing equivalence. -/
local instance dgMonoidalCategoryStruct : MonoidalCategoryStruct DGChainComplex :=
  CategoryTheory.Monoidal.transportStruct
    (ChainComplex.cochainComplexEquivalence (ModuleCat ℤ)).symm

local instance dgMonoidalCategory : MonoidalCategory DGChainComplex :=
  CategoryTheory.Monoidal.transport
    (ChainComplex.cochainComplexEquivalence (ModuleCat ℤ)).symm

/-- The generalized Eilenberg--MacLane simplicial set of an integer-indexed
chain complex: restrict to nonnegative degrees, apply inverse Dold--Kan, then
forget the module structure. -/
def dgDoldKanSSet (K : DGChainComplex) : SSet.{0} :=
  CategoryTheory.Abelian.DoldKan.Γ.obj (dgNonnegativePart.obj K) ⋙
    forget (ModuleCat ℤ)

/-- A chain map induces the corresponding map of generalized
Eilenberg--MacLane simplicial sets. -/
def dgDoldKanSSetMap {K L : DGChainComplex} (f : K ⟶ L) :
    dgDoldKanSSet K ⟶ dgDoldKanSSet L :=
  Functor.whiskerRight
    (CategoryTheory.Abelian.DoldKan.Γ.map (dgNonnegativePart.map f))
    (forget (ModuleCat ℤ))

/-- Raw Alexander--Whitney lax-monoidal data for inverse Dold--Kan.

Kerodon Proposition 2.5.9.1 supplies these maps.  No naturality, unitality, or
associativity theorem is bundled here: those are exactly the result-layer
content which turns this raw data into a lax monoidal structure. -/
structure DoldKanAlexanderWhitneyData where
  /-- The unit map of the raw lax-monoidal data. -/
  unit : 𝟙_ SSet ⟶ dgDoldKanSSet (𝟙_ DGChainComplex)
  /-- The Alexander--Whitney multiplication
  `K(X) × K(Y) → K(X ⊠ Y)`.  The tensor on `SSet` is its cartesian product. -/
  mul (K L : DGChainComplex) :
    dgDoldKanSSet K ⊗ dgDoldKanSSet L ⟶ dgDoldKanSSet (K ⊗ L)

/-- The source-order DG-category data consumed by Kerodon 00SE.

The composition has factors `Hom(Y,Z) ⊠ Hom(X,Y)`, matching Kerodon's
`(g,f) ↦ g ∘ f` convention.  The existing mapped DG-enrichment owner supplies
this data after the Koszul symmetry; no DG-category laws are duplicated here. -/
structure DGCategoryCompositionData (C : Type u) where
  Hom : C → C → DGChainComplex
  id (X : C) : 𝟙_ DGChainComplex ⟶ Hom X X
  comp (X Y Z : C) : Hom Y Z ⊗ Hom X Y ⟶ Hom X Z

/-- Raw simplicial-category data: hom simplicial sets, identity maps, and
composition maps, without the category laws. -/
structure UnderlyingSimplicialCategoryData (C : Type u) where
  Hom : C → C → SSet.{0}
  id (X : C) : 𝟙_ SSet ⟶ Hom X X
  comp (X Y Z : C) : Hom Y Z ⊗ Hom X Y ⟶ Hom X Z

/-- Kerodon 00SE: the underlying simplicial-category data of a DG category.

The hom object is `K(Hom_C(X,Y))`.  Composition is the Alexander--Whitney
multiplication followed by inverse Dold--Kan applied to DG composition, exactly
as in the source formula. -/
def dgUnderlyingSimplicialCategoryData
    (aw : DoldKanAlexanderWhitneyData) (C : Type u)
    (D : DGCategoryCompositionData C) : UnderlyingSimplicialCategoryData C where
  Hom X Y := dgDoldKanSSet (D.Hom X Y)
  id X := aw.unit ≫ dgDoldKanSSetMap (D.id X)
  comp X Y Z :=
    aw.mul (D.Hom Y Z) (D.Hom X Y) ≫ dgDoldKanSSetMap (D.comp X Y Z)

end LeanCategories.Homological
