/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.CohomologyRingData

/-!
# Singular-cohomology pullback and cross-product data

Definition-level realization of Hatcher FC07-C03-U024, ported from the
pinned ATLAS Section 26 construction.

For a map f : X ⟶ Y, singular cochains pull back contravariantly by
precomposition with the induced singular-chain map, and homology gives
f^* : H^n(Y;R) → H^n(X;R). Hatcher's external product is
a × b = p₁^* a ∪ p₂^* b on X × Y.

This file records exactly those maps. Naturality, associativity, the
Künneth theorem, and compatibility with ring structures are result content
and are not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits MonoidalCategory

/-- The cochain map induced contravariantly by a continuous map. -/
def singularCochainMapData
    (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularCochainComplexData R Y (ModuleCat.of R R) ⟶
    singularCochainComplexData R X (ModuleCat.of R R) :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).map f)).op)

/-- Pullback on singular cohomology in degree n. -/
def singularCohomologyMapData
    (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singularCohomologyModuleData R Y (ModuleCat.of R R) n ⟶
    singularCohomologyModuleData R X (ModuleCat.of R R) n :=
  HomologicalComplex.homologyMap (singularCochainMapData R f) n

/-- Hatcher's external cohomology product, obtained by pulling both classes
to X × Y and applying the cup product there. -/
def singularCohomologyCrossProductData
    (R : Type) [CommRing R] (X Y : TopCat.{0})
    (D : SingularCohomologyCupData R (X ⨯ Y)) (p q : ℕ) :
    singularCohomologyModuleData R X (ModuleCat.of R R) p ⊗
      singularCohomologyModuleData R Y (ModuleCat.of R R) q ⟶
    singularCohomologyModuleData R (X ⨯ Y) (ModuleCat.of R R) (p + q) :=
  tensorHom
      (singularCohomologyMapData R (prod.fst (X := X) (Y := Y)) p)
      (singularCohomologyMapData R (prod.snd (X := X) (Y := Y)) q) ≫
    (D.cohomology p q).1

end LeanCategories.Topology
