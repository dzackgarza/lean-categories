/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.AlgebraDeRhamLemmas
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Algebraic de Rham complex

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.8.9,
p. 349 (FC05-C09-U124).

For a commutative `k`-algebra `R`, the algebraic de Rham differential is
characterized on generators by

`d(r₀ dr₁ ∧ ... ∧ drₙ) = dr₀ ∧ dr₁ ∧ ... ∧ drₙ`.

The identity `d²=0` makes the exterior powers of `Ω[R⁄k]` into a cochain
complex of `k`-modules. Its cohomology is algebraic de Rham cohomology.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u


variable (k : Type u) [CommRing k]
variable (R : Type u) [CommRing R] [Algebra k R]

/-- The degree-`n` module of algebraic differential forms `Ω^n_{R/k}`. -/
abbrev DeRhamDegree (n : ℕ) : Type u :=
  Algebra.DeRham.Form k R n

/-- The pure differential form `r₀ dr₁ ∧ ... ∧ drₙ`. -/
def deRhamPureForm {n : ℕ} (r₀ : R) (a : Fin n → R) :
    DeRhamDegree k R n :=
  Algebra.DeRham.mk k R n r₀ a

/-- The source value of the de Rham differential on a pure form:
`dr₀ ∧ dr₁ ∧ ... ∧ drₙ`. -/
def deRhamDifferentialPure {n : ℕ} (r₀ : R) (a : Fin n → R) :
    DeRhamDegree k R (n + 1) :=
  Algebra.DeRham.mk k R (n + 1) 1 (Fin.cons r₀ a)

/-- The defining formula for the exterior derivative on pure differential forms. -/
@[simp]
theorem deRhamDifferential_pure {n : ℕ} (r₀ : R) (a : Fin n → R) :
    Algebra.DeRham.differential k R n (deRhamPureForm k R r₀ a) =
      deRhamDifferentialPure k R r₀ a :=
  Algebra.DeRham.differential_mk k R n r₀ a

/-- The algebraic de Rham cochain complex `(Ω^*_{R/k}, d)` of `k`-modules. -/
noncomputable def algebraicDeRhamComplex : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of
    (fun n => ModuleCat.of k (DeRhamDegree k R n))
    (fun n => ModuleCat.ofHom (Algebra.DeRham.differential k R n))
    (fun n => by
      apply ModuleCat.hom_ext
      change (Algebra.DeRham.differential k R (n + 1)).comp
          (Algebra.DeRham.differential k R n) = 0
      ext x
      exact congrArg Subtype.val (Algebra.DeRham.differential_squared k R n x))

@[simp]
theorem algebraicDeRhamComplex_X (n : ℕ) :
    (algebraicDeRhamComplex k R).X n = ModuleCat.of k (DeRhamDegree k R n) := rfl

@[simp]
theorem algebraicDeRhamComplex_d (n : ℕ) :
    (algebraicDeRhamComplex k R).d n (n + 1) =
      ModuleCat.ofHom (Algebra.DeRham.differential k R n) := by
  simp [algebraicDeRhamComplex]

/-- The differential of the algebraic de Rham complex has Weibel's defining pure-form value. -/
@[simp]
theorem algebraicDeRhamComplex_d_pure {n : ℕ} (r₀ : R) (a : Fin n → R) :
    (algebraicDeRhamComplex k R).d n (n + 1) (deRhamPureForm k R r₀ a) =
      deRhamDifferentialPure k R r₀ a := by
  rw [algebraicDeRhamComplex_d]
  exact deRhamDifferential_pure k R r₀ a

/-- The cochain map on algebraic de Rham complexes induced by a `k`-algebra homomorphism. -/
noncomputable def algebraicDeRhamComplexMap {S : Type u} [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) : algebraicDeRhamComplex k R ⟶ algebraicDeRhamComplex k S :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Algebra.DeRham.map k f n))
    (fun n => by
      simp only [algebraicDeRhamComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      change (Algebra.DeRham.differential k S n).comp (Algebra.DeRham.map k f n) =
        (Algebra.DeRham.map k f (n + 1)).comp (Algebra.DeRham.differential k R n)
      ext x
      exact congrArg Subtype.val (Algebra.DeRham.map_differential k f n x).symm)

/-- Algebraic de Rham cohomology `H^n_dR(R/k)=H^n(Ω^*_{R/k},d)` as a `k`-module. -/
noncomputable def algebraicDeRhamCohomology (n : ℕ) : ModuleCat k :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).obj
    (algebraicDeRhamComplex k R)

end LeanCategories.Homological
