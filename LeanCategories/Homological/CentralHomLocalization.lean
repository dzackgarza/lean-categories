/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.OreLocalization.Ring

/-!
# The localization comparison map for Hom

Weibel, *An Introduction to Homological Algebra* (1994), §3.3, pp. 73--75
(FC05-C03-U031).

The source allows a central multiplicative set in a possibly noncommutative
ring.  Mathlib's convenient localized-module/Hom comparison API is
commutative, so this file records the source-general comparison as a
realization interface rather than narrowing the ring hypothesis.

For fractions the comparison is

`(f/s)(a/t) = f(a)/(st)`.

Construction/well-definedness of such realizations, and the theorem that the
comparison is an isomorphism for finitely presented `A`, are result-level.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v w uL vL

/-- A multiplicative subset lies in the center of an associative ring. -/
def IsCentralSubmonoid {R : Type u} [Ring R] (S : Submonoid R) : Prop :=
  ∀ (s : S) (r : R), (s : R) * r = r * (s : R)

/-- Source-general realization data for Weibel's map
`S⁻¹ Hom_R(A,B) → Hom_{S⁻¹R}(S⁻¹A,S⁻¹B)`.

The fields expose the localized ring/modules and fraction representatives, and
`comparison_fraction` fixes the comparison map by Weibel's formula.  This
separates the definition from the theorem that the quotient constructions
exist and that the map is an isomorphism under finite presentation.
-/
structure CentralHomLocalizationRealization
    (R : Type u) [Ring R] (S : Submonoid R) (hS : IsCentralSubmonoid S)
    (A : Type v) [AddCommGroup A] [Module R A]
    (B : Type w) [AddCommGroup B] [Module R B] where
  /-- The central localization `S⁻¹R`. -/
  RS : Type uL
  [ringRS : Ring RS]
  /-- The localized source module. -/
  AS : Type vL
  [addCommGroupAS : AddCommGroup AS]
  [moduleAS : Module RS AS]
  /-- The localized target module. -/
  BS : Type vL
  [addCommGroupBS : AddCommGroup BS]
  [moduleBS : Module RS BS]
  /-- The additive group underlying `S⁻¹ Hom_R(A,B)`. -/
  localizedHom : Type vL
  [addCommGroupLocalizedHom : AddCommGroup localizedHom]
  /-- Fraction representatives `f/s` in localized Hom. -/
  homFraction : (A →ₗ[R] B) → S → localizedHom
  /-- Fraction representatives `a/s` in the localized source. -/
  sourceFraction : A → S → AS
  /-- Fraction representatives `b/s` in the localized target. -/
  targetFraction : B → S → BS
  /-- Weibel's localization comparison map. -/
  comparison : localizedHom →+ (AS →ₗ[RS] BS)
  /-- The defining fraction formula `(f/s)(a/t)=f(a)/(st)`. -/
  comparison_fraction : ∀ (f : A →ₗ[R] B) (s t : S) (a : A),
    comparison (homFraction f s) (sourceFraction a t) =
      targetFraction (f a) (s * t)

attribute [instance]
  CentralHomLocalizationRealization.ringRS
  CentralHomLocalizationRealization.addCommGroupAS
  CentralHomLocalizationRealization.moduleAS
  CentralHomLocalizationRealization.addCommGroupBS
  CentralHomLocalizationRealization.moduleBS
  CentralHomLocalizationRealization.addCommGroupLocalizedHom

end LeanCategories.Homological
