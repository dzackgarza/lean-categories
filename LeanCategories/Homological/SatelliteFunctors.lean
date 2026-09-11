/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DeltaFunctorMorphisms

/-!
# Satellite functors

Weibel, *An Introduction to Homological Algebra* (1994), §2.1, p. 32,
FC05-C02-U008.

If an additive functor is the degree-zero term of a universal homological
δ-functor, the higher terms are its left satellite functors. Dually, the
higher terms of a universal cohomological δ-functor are its right satellite
functors.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- A universal homological δ-functor extending `F`. Its positive-degree terms are Weibel's
left satellite functors of `F`. -/
structure LeftSatelliteExtension (F : A ⥤+ B) where
  deltaFunctor : HomologicalDeltaFunctor A B
  universal : deltaFunctor.IsUniversal
  degreeZeroIso : deltaFunctor.T 0 ≅ F

/-- The `n`th left satellite functor supplied by a chosen universal homological extension. -/
def LeftSatelliteExtension.satellite {F : A ⥤+ B} (E : LeftSatelliteExtension F) (n : ℕ) :
    A ⥤+ B :=
  E.deltaFunctor.T n

/-- A universal cohomological δ-functor extending `F`. Its positive-degree terms are Weibel's
right satellite functors of `F`. -/
structure RightSatelliteExtension (F : A ⥤+ B) where
  deltaFunctor : CohomologicalDeltaFunctor A B
  universal : deltaFunctor.IsUniversal
  degreeZeroIso : deltaFunctor.T 0 ≅ F

/-- The `n`th right satellite functor supplied by a chosen universal cohomological extension. -/
def RightSatelliteExtension.satellite {F : A ⥤+ B} (E : RightSatelliteExtension F) (n : ℕ) :
    A ⥤+ B :=
  E.deltaFunctor.T n

end LeanCategories.Homological
