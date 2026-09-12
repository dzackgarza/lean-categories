/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KoszulExteriorDescription
public import LeanCategories.Homological.KoszulHomology

/-!
# Transition maps between Koszul complexes of powers

Weibel, *An Introduction to Homological Algebra* (1994), §4.6, pp. 115--119
(FC05-C04-U080).

For a central sequence `x`, the map `K(x^(i+1)) → K(x^i)` multiplies the
wedge basis element `e_I` by the product of the `x_j` with `j ∈ I`.  These
maps induce the inverse system on Koszul homology and, contravariantly, the
direct system on Koszul cohomology.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite

universe u

variable (R : Type u) [Ring R]

/-- The coordinatewise `m`th power of a finite sequence. -/
def koszulPowerSequence {n : ℕ} (x : Fin n → R) (m : ℕ) : Fin n → R :=
  fun j => x j ^ m

/-- Powers of a central sequence are central. -/
theorem isCentralSequence_power {n : ℕ} {x : Fin n → R}
    (hx : IsCentralSequence R x) (m : ℕ) :
    IsCentralSequence R (koszulPowerSequence R x m) := by
  intro j r
  induction m with
  | zero => simp [koszulPowerSequence]
  | succ m ih =>
      simp only [koszulPowerSequence, pow_succ]
      have ih' : x j ^ m * r = r * x j ^ m := by
        simpa [koszulPowerSequence] using ih
      calc
        x j ^ m * x j * r = x j ^ m * (x j * r) := by rw [mul_assoc]
        _ = x j ^ m * (r * x j) := by rw [hx j r]
        _ = (x j ^ m * r) * x j := by rw [mul_assoc]
        _ = (r * x j ^ m) * x j := by rw [ih']
        _ = r * (x j ^ m * x j) := by rw [mul_assoc]

/-- Ordered product of the sequence entries indexed by a wedge symbol.

The ambient ring need not be commutative, so the product is taken in the
canonical order on `Fin n`; centrality makes this the expected subset product. -/
def koszulTransitionCoefficient {n p : ℕ} (x : Fin n → R)
    (s : KoszulWedgeIndex n p) : R :=
  (List.ofFn fun j : Fin n => if j ∈ s.1 then x j else 1).prod

/-- A source-faithful transition map `K(x^(i+1)) → K(x^i)`. -/
structure KoszulPowerTransition {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (i : ℕ)
    (Knext : KoszulComplexRealization R (koszulPowerSequence R x (i + 1))
      (isCentralSequence_power R hx (i + 1)))
    (Kcurr : KoszulComplexRealization R (koszulPowerSequence R x i)
      (isCentralSequence_power R hx i)) where
  /-- The transition chain map. -/
  map : Knext.complex ⟶ Kcurr.complex
  /-- On a wedge basis symbol `e_I`, multiply by `∏_{j∈I} x_j`. -/
  map_wedge : ∀ (p : ℕ) (s : KoszulWedgeIndex n p),
    (Kcurr.degreeIso p).hom
        (map.f p ((Knext.degreeIso p).inv (koszulWedgeSymbol R s))) =
      koszulTransitionCoefficient R x s • koszulWedgeSymbol R s

/-- The induced transition `H_q(x^(i+1),A) → H_q(x^i,A)` on Koszul homology. -/
noncomputable def koszulHomologyTransition {n : ℕ} {x : Fin n → R}
    {hx : IsCentralSequence R x} {i : ℕ}
    {Knext : KoszulComplexRealization R (koszulPowerSequence R x (i + 1))
      (isCentralSequence_power R hx (i + 1))}
    {Kcurr : KoszulComplexRealization R (koszulPowerSequence R x i)
      (isCentralSequence_power R hx i)}
    (T : KoszulPowerTransition R x hx i Knext Kcurr)
    (A : ModuleCat Rᵐᵒᵖ) (q : ℕ) :
    koszulHomology R _ _ Knext A q ⟶ koszulHomology R _ _ Kcurr A q :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) q).map
    (((tensorLeftFunctor R A).mapHomologicalComplex (ComplexShape.down ℕ)).map T.map)

/-- The contravariantly induced map `H^q(x^i,B) → H^q(x^(i+1),B)` on
Koszul cohomology. -/
noncomputable def koszulCohomologyTransition {n : ℕ} {x : Fin n → R}
    {hx : IsCentralSequence R x} {i : ℕ}
    {Knext : KoszulComplexRealization R (koszulPowerSequence R x (i + 1))
      (isCentralSequence_power R hx (i + 1))}
    {Kcurr : KoszulComplexRealization R (koszulPowerSequence R x i)
      (isCentralSequence_power R hx i)}
    (T : KoszulPowerTransition R x hx i Knext Kcurr)
    (B : ModuleCat R) (q : ℕ) :
    koszulCohomology R _ _ Kcurr B q ⟶ koszulCohomology R _ _ Knext B q :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).map
    (((preadditiveYoneda.obj B).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((HomologicalComplex.opFunctor (ModuleCat R) (ComplexShape.down ℕ)).map T.map.op))

end LeanCategories.Homological
