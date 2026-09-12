/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KoszulTransition
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Koszul-limit local cohomology

Weibel, *An Introduction to Homological Algebra* (1994), Definition 4.6.5,
pp. 115--119 (FC05-C04-U081).

For a central sequence `x`, the transition maps between the Koszul complexes
of the powers `x^i` induce a direct system on Koszul cohomology.  Weibel's
Koszul-limit local cohomology is the colimit of that direct system.

The theorem comparing this construction with derived local cohomology is not
part of the definition and remains in the theorem sweep.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe u

variable (R : Type u) [Ring R]

/-- A coherent choice of Koszul complexes for all powers of a central
sequence, together with the successor transition maps. -/
structure KoszulPowerSystem {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) where
  /-- The chosen realization of `K(x^i)`. -/
  complex : ∀ i : ℕ,
    KoszulComplexRealization R (koszulPowerSequence R x i)
      (isCentralSequence_power R hx i)
  /-- The transition `K(x^(i+1)) → K(x^i)`. -/
  transition : ∀ i : ℕ,
    KoszulPowerTransition R x hx i (complex (i + 1)) (complex i)

/-- The direct system `i ↦ H^q(x^i,B)` induced by the Koszul transition maps. -/
noncomputable def koszulCohomologySystem {n : ℕ} {x : Fin n → R}
    {hx : IsCentralSequence R x} (S : KoszulPowerSystem R x hx)
    (B : ModuleCat R) (q : ℕ) : ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence fun i =>
    koszulCohomologyTransition R (S.transition i) B q

/-- Weibel's Koszul-limit local cohomology
`H_x^q(B) = colim_i H^q(x^i,B)`. -/
noncomputable def koszulLimitLocalCohomology {n : ℕ} {x : Fin n → R}
    {hx : IsCentralSequence R x} (S : KoszulPowerSystem R x hx)
    (B : ModuleCat R) (q : ℕ) : AddCommGrpCat :=
  colimit (koszulCohomologySystem R S B q)

end LeanCategories.Homological
