/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Algebraic de Rham complex

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.8.9,
pp. 344--353 (FC05-C09-U124).

For a commutative `k`-algebra `R`, the algebraic de Rham differential is
characterized on generators by

`d(r₀ dr₁ ∧ ... ∧ drₙ) = dr₀ ∧ dr₁ ∧ ... ∧ drₙ`.

The identity `d²=0` makes the exterior powers of `Ω[R⁄k]` into a cochain
complex, and its cohomology is algebraic de Rham cohomology.  This file
records the degree objects and the defining formula by a realization
structure; construction and uniqueness of the differential from the formula
are theorem-layer work.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u


variable (k : Type u) [CommRing k]
variable (R : Type u) [CommRing R] [Algebra k R]

/-- The degree-`n` module of algebraic differential forms `Ω^n_{R/k}`. -/
abbrev DeRhamDegree (n : ℕ) : Type u :=
  ⋀[R]^n Ω[R⁄k]

/-- The pure differential form `r₀ dr₁ ∧ ... ∧ drₙ`. -/
def deRhamPureForm {n : ℕ} (r₀ : R) (a : Fin n → R) :
    DeRhamDegree k R n :=
  r₀ • exteriorPower.ιMulti R n (fun i => KaehlerDifferential.D k R (a i))

/-- The source value of the de Rham differential on a pure form:
`dr₀ ∧ dr₁ ∧ ... ∧ drₙ`. -/
def deRhamDifferentialPure {n : ℕ} (r₀ : R) (a : Fin n → R) :
    DeRhamDegree k R (n + 1) :=
  exteriorPower.ιMulti R (n + 1)
    (Fin.cons (KaehlerDifferential.D k R r₀)
      (fun i => KaehlerDifferential.D k R (a i)))

/-- A realization of Weibel's algebraic de Rham complex.

The `d_pure` field is the defining formula from Definition 9.8.9.  Since the
supplied object is already a cochain complex, the relation `d²=0` is carried
by its homological-complex structure rather than repeated as a separate field.
-/
structure DeRhamComplexRealization where
  /-- The cochain complex `(Ω^*_{R/k},d)`. -/
  complex : CochainComplex (ModuleCat R) ℕ
  /-- Degree `n` is the `n`th exterior power of Kähler differentials. -/
  degreeIso : ∀ n : ℕ,
    complex.X n ≅ ModuleCat.of R (DeRhamDegree k R n)
  /-- The differential satisfies
  `d(r₀ dr₁∧...∧drₙ)=dr₀∧dr₁∧...∧drₙ`. -/
  d_pure : ∀ (n : ℕ) (r₀ : R) (a : Fin n → R),
    (degreeIso (n + 1)).hom
        (complex.d n (n + 1)
          ((degreeIso n).inv (deRhamPureForm k R r₀ a))) =
      deRhamDifferentialPure k R r₀ a

/-- Algebraic de Rham cohomology
`H^n_dR(R/k)=H^n(Ω^*_{R/k},d)` attached to a realization of Weibel's
de Rham complex. -/
def algebraicDeRhamCohomology
    (D : DeRhamComplexRealization k R) (n : ℕ) : ModuleCat R :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).obj
    D.complex

end LeanCategories.Homological
