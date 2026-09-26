/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Category.Quiv
public import LeanCategories.Topology.InducedLieHomData

/-!
# Raw categorical data for the Lie functor

Definition-level realization of Lee FC08-C08-U063.

Lee introduces the category of finite-dimensional smooth Lie groups and smooth
group homomorphisms, the category of finite-dimensional real Lie algebras and
Lie-algebra homomorphisms, and the assignment `G ↦ Lie(G)`, `F ↦ F_*` between
them.  Proposition 8.45 (FC08-C08-U062) is the separate result that the map
assignment preserves identities and composition.

Sweep III therefore uses Mathlib's proof-free categorical interfaces:
`CategoryStruct` records the hom, identity, and composition data without the
category axioms, and `Prefunctor` records object and morphism assignments
without functor laws.  A source-facing Lie-functor datum explicitly supplies,
for every smooth group homomorphism, induced-Lie-hom data certified by U061;
no map is selected by an unwitnessed choice.

The ambient bundles below are the irreducible source-specific residue after the
2026-09-25 reuse audit: pinned/current Mathlib and this project have no bundled
category of smooth Lie groups or finite-dimensional real Lie algebras, and the
pinned TauCeti reference `8e673113.../TauCeti/Geometry/Lie/Functor.lean`
likewise works unbundled.  The generic raw-category and raw-functor layers are
reused from Mathlib rather than reimplemented locally.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open CategoryTheory
open scoped ContDiff Manifold

universe u v w

/-- A finite-dimensional smooth real Lie group, bundled only far enough to be
an object of Lee's raw category `Lie`.

The model is retained because Mathlib's manifold and tangent-space interfaces
are parametrized by it. -/
structure SmoothLieGroupData where
  model : Type u
  modelH : Type v
  carrier : Type w
  [normedAddCommGroup : NormedAddCommGroup model]
  [normedSpace : NormedSpace ℝ model]
  [finiteDimensional : FiniteDimensional ℝ model]
  [modelTopology : TopologicalSpace modelH]
  modelWithCorners : ModelWithCorners ℝ model modelH
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace modelH carrier]
  [group : Group carrier]
  [lieGroup : LieGroup modelWithCorners ∞ carrier]

namespace SmoothLieGroupData

attribute [instance] normedAddCommGroup normedSpace finiteDimensional modelTopology
  topologicalSpace chartedSpace group lieGroup

instance : CoeSort SmoothLieGroupData.{u, v, w} (Type w) := ⟨carrier⟩

/-- Smooth group homomorphisms are the arrows of Lee's raw Lie-group category. -/
instance : Quiver SmoothLieGroupData.{u, v, w} where
  Hom G H :=
    ContMDiffMonoidMorphism G.modelWithCorners H.modelWithCorners ∞ G.carrier H.carrier

/-- Identity and composition data for smooth Lie-group homomorphisms.

No category laws are asserted in Sweep III. -/
instance : CategoryStruct SmoothLieGroupData.{u, v, w} where
  id G :=
    { toMonoidHom := MonoidHom.id G.carrier
      contMDiff_toFun := contMDiff_id }
  comp f g :=
    { toMonoidHom := g.toMonoidHom.comp f.toMonoidHom
      contMDiff_toFun := g.contMDiff_toFun.comp f.contMDiff_toFun }

end SmoothLieGroupData

/-- A finite-dimensional real Lie algebra, bundled only far enough to be an
object of Lee's raw category `lie`. -/
structure FiniteDimensionalRealLieAlgebraData where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℝ carrier]
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra ℝ carrier]
  [finiteDimensional : FiniteDimensional ℝ carrier]

namespace FiniteDimensionalRealLieAlgebraData

attribute [instance] addCommGroup module lieRing lieAlgebra finiteDimensional

instance : CoeSort FiniteDimensionalRealLieAlgebraData.{u} (Type u) := ⟨carrier⟩

/-- Real Lie-algebra homomorphisms are the arrows of Lee's raw Lie-algebra category. -/
instance : Quiver FiniteDimensionalRealLieAlgebraData.{u} where
  Hom L K := L.carrier →ₗ⁅ℝ⁆ K.carrier

/-- Identity and composition data for finite-dimensional real Lie algebras.

No category laws are asserted in Sweep III. -/
instance : CategoryStruct FiniteDimensionalRealLieAlgebraData.{u} where
  id _ := LieHom.id
  comp f g := g.comp f

end FiniteDimensionalRealLieAlgebraData

/-- The object assignment `G ↦ Lie(G)` in Lee's covariant Lie functor. -/
def groupLieAlgebraObjectData (G : SmoothLieGroupData.{u, v, w}) :
    FiniteDimensionalRealLieAlgebraData.{u} := by
  letI : CompleteSpace G.model := FiniteDimensional.complete ℝ G.model
  letI : LieGroup G.modelWithCorners (minSmoothness ℝ 3) G.carrier :=
    LieGroup.of_le (m := minSmoothness ℝ 3) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)
  exact
    { carrier := GroupLieAlgebra G.modelWithCorners G.carrier
      finiteDimensional := by
        change FiniteDimensional ℝ G.model
        infer_instance }

/-- Source-faithful morphism assignment for Lee's Lie functor.  Each arrow is
supplied together with U061's exact differential-at-identity specification.
Functoriality remains Proposition 8.45. -/
structure LiePrefunctorMapData where
  map :
    ∀ {X Y : SmoothLieGroupData.{u, v, w}} (f : X ⟶ Y),
      letI : CompleteSpace X.model := FiniteDimensional.complete ℝ X.model
      letI : CompleteSpace Y.model := FiniteDimensional.complete ℝ Y.model
      letI : LieGroup X.modelWithCorners (minSmoothness ℝ 3) X.carrier :=
        LieGroup.of_le (m := minSmoothness ℝ 3) (n := ∞)
          (by
            rw [minSmoothness_of_isRCLikeNormedField]
            exact (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)
      letI : LieGroup Y.modelWithCorners (minSmoothness ℝ 3) Y.carrier :=
        LieGroup.of_le (m := minSmoothness ℝ 3) (n := ∞)
          (by
            rw [minSmoothness_of_isRCLikeNormedField]
            exact (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)
      InducedLieHomData f

/-- Lee's proof-free covariant Lie-prefunctor obtained from a supplied
source-faithful morphism assignment.  Identity/composition laws are exactly
FC08-C08-U062 and are deliberately absent from `Prefunctor`. -/
def liePrefunctorData (D : LiePrefunctorMapData.{u, v, w}) :
    SmoothLieGroupData.{u, v, w} ⥤q FiniteDimensionalRealLieAlgebraData.{u} where
  obj := groupLieAlgebraObjectData
  map {X Y} f := by
    letI : CompleteSpace X.model := FiniteDimensional.complete ℝ X.model
    letI : CompleteSpace Y.model := FiniteDimensional.complete ℝ Y.model
    letI : LieGroup X.modelWithCorners (minSmoothness ℝ 3) X.carrier :=
      LieGroup.of_le (m := minSmoothness ℝ 3) (n := ∞)
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)
    letI : LieGroup Y.modelWithCorners (minSmoothness ℝ 3) Y.carrier :=
      LieGroup.of_le (m := minSmoothness ℝ 3) (n := ∞)
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)
    change GroupLieAlgebra X.modelWithCorners X.carrier →ₗ⁅ℝ⁆
      GroupLieAlgebra Y.modelWithCorners Y.carrier
    exact (D.map f).1

end LeanCategories.Topology
