/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.NonLocalRing

@[expose] public section

namespace LeanCategories.Algebra

universe u

/-- Atiyah–Macdonald, Chapter 3 (FC04-C03-U022): a property is local when it holds
for a ring exactly when it holds after localization at every prime ideal. -/
def IsLocalRingPropertyAtPrimes
    (P : ∀ (S : Type u) [CommRing S], Prop) (R : Type u) [CommRing R] : Prop :=
  P R ↔ ∀ (p : Ideal R) [p.IsPrime], P (Localization.AtPrime p)

/-- Atiyah–Macdonald, Chapter 3 (FC04-C03-U022): a property of modules is local when
it holds for the original module exactly when it holds for its localization at every prime. -/
def IsLocalModulePropertyAtPrimes
    (P : ∀ (S : Type u) [CommRing S] (N : Type u) [AddCommGroup N] [Module S N], Prop)
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  P R M ↔ ∀ (p : Ideal R) [p.IsPrime],
    P (Localization.AtPrime p) (LocalizedModule p.primeCompl M)

-- A local ring satisfies this particular comparison, because its prime localizations are local.
example (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalRingPropertyAtPrimes (fun S _ => IsLocalRing S) R := by
  constructor
  · intro _ p hp
    infer_instance
  · intro _
    infer_instance

-- Being a local ring is not itself a local property: every prime localization is local,
-- but a product of two nonzero rings is not. The reverse implication is essential.
example (R S : Type u) [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S] :
    ¬ IsLocalRingPropertyAtPrimes (fun T _ => IsLocalRing T) (R × S) := by
  intro h
  exact IsLocalRing.not_isLocalRing_of_prod_of_nontrivial R S
    (h.mpr fun p hp => inferInstance)

-- Localization of the zero module remains zero, over any base ring.
example (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Subsingleton M] :
    IsLocalModulePropertyAtPrimes (fun _ _ N _ _ => Subsingleton N) R M := by
  constructor
  · intro _ p hp
    infer_instance
  · intro _
    infer_instance

-- The same missing reverse implication is detected even for a property of the base
-- ring regarded as a property of its modules.
example (R S : Type u) [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S] :
    ¬ IsLocalModulePropertyAtPrimes (fun T _ _ _ _ => IsLocalRing T) (R × S) (R × S) := by
  intro h
  exact IsLocalRing.not_isLocalRing_of_prod_of_nontrivial R S
    (h.mpr fun p hp => inferInstance)

end LeanCategories.Algebra
