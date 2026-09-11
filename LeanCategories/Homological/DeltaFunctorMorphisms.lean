/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DeltaFunctor

/-!
# Morphisms and universal δ-functors

Weibel, *An Introduction to Homological Algebra* (1994), Definition 2.1.4,
§2.1, p. 32, FC05-C02-U006.

A morphism of δ-functors is a degreewise natural transformation commuting
with every connecting morphism. A homological δ-functor is universal when
any natural transformation into its degree-zero term extends uniquely to a
morphism of δ-functors. In the cohomological convention, the direction is
dual: a map out of degree zero extends uniquely to a morphism out of the
universal δ-functor.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

namespace HomologicalDeltaFunctor

/-- A morphism of homological δ-functors: a degreewise natural transformation commuting with
all connecting morphisms. -/
@[ext]
structure Hom (S T : HomologicalDeltaFunctor A B) where
  app : ∀ n, S.T n ⟶ T.T n
  delta_comm : ∀ n (E : ShortExactCat A),
    (app (n + 1)).hom.app E.obj.X₃ ≫ (T.delta n).app E =
      (S.delta n).app E ≫ (app n).hom.app E.obj.X₁

/-- A homological δ-functor is universal when every natural transformation into its degree-zero
part extends uniquely to a morphism of δ-functors. -/
def IsUniversal (T : HomologicalDeltaFunctor A B) : Prop :=
  ∀ (S : HomologicalDeltaFunctor A B) (f₀ : S.T 0 ⟶ T.T 0),
    ∃! f : Hom S T, f.app 0 = f₀

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

/-- A morphism of cohomological δ-functors: a degreewise natural transformation commuting with
all connecting morphisms. -/
@[ext]
structure Hom (S T : CohomologicalDeltaFunctor A B) where
  app : ∀ n, S.T n ⟶ T.T n
  delta_comm : ∀ n (E : ShortExactCat A),
    (app n).hom.app E.obj.X₃ ≫ (T.delta n).app E =
      (S.delta n).app E ≫ (app (n + 1)).hom.app E.obj.X₁

/-- A cohomological δ-functor is universal when every natural transformation out of its
degree-zero part extends uniquely to a morphism of δ-functors. -/
def IsUniversal (T : CohomologicalDeltaFunctor A B) : Prop :=
  ∀ (S : CohomologicalDeltaFunctor A B) (f0 : T.T 0 ⟶ S.T 0),
    ∃! f : Hom T S, f.app 0 = f0

end CohomologicalDeltaFunctor

end LeanCategories.Homological
