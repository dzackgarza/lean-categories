/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import LeanCategories.Algebra.EssentialExtension

/-!
# Injective hulls

Definition-level realization of Matsumura FC13-CB-U024.

An injective hull is an embedding into an injective module whose image is an
essential submodule. Existence and uniqueness of such hulls are results about
this predicate and remain outside Sweep III.

The definition is adapted from
`TauCeti.Algebra.Module.Injective.Envelope.IsInjectiveEnvelope` at
TauCetiProject/TauCeti@f950b72d39838f59d7ec8f723f7a826a02649145
(Apache-2.0), using the local FC13-CB-U022 essential-extension predicate.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v w

variable {R : Type u} {M : Type v} {E : Type w}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup E] [Module R E]

/-- Matsumura's injective-hull predicate (`FC13-CB-U024`): `f : M → E`
exhibits `E` as an injective hull of `M` when `E` is injective, `f` is an
embedding, and its range is an essential submodule of `E`.

The existence of such an `E` and its uniqueness up to an isomorphism fixing
`M` are theorem clauses, not fields of this Sweep-III definition. -/
structure IsInjectiveHull (f : M →ₗ[R] E) : Prop where
  moduleInjective : Module.Injective R E
  injective : Function.Injective f
  isEssential_range : IsEssentialExtension (LinearMap.range f)

end LeanCategories.Algebra

namespace LeanCategories.Algebra

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]

/-- Matsumura's minimality condition for an injective resolution
(`FC13-CB-U025`).  The augmentation image is essential in degree zero and the
image of every differential is essential in the following injective term.

The ambient terms are already injective by `InjectiveResolution`.  This records
the source's definition-level minimality condition only; existence of a
resolution obtained by iterated injective hulls, and uniqueness/comparison of
such resolutions, remain result clauses. -/
def IsMinimalInjectiveResolution {Z : ModuleCat.{v} R}
    (I : InjectiveResolution Z) : Prop :=
  IsEssentialExtension (LinearMap.range (I.ι.f 0).hom) ∧
    ∀ n : ℕ,
      IsEssentialExtension
        (LinearMap.range (I.cocomplex.d n (n + 1)).hom)

end LeanCategories.Algebra
