/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CosimplicialDoldKan
public import LeanCategories.Homological.CotripleHomology
public import Mathlib.CategoryTheory.Monad.Basic

/-!
# Triple and cotriple cohomology

Weibel, *An Introduction to Homological Algebra* (1994), §8.7, pp. 286--293
(FC05-C08-U076, FC05-C08-U077).

A monad (triple) gives the dual canonical cosimplicial resolution.  Covariant
coefficients applied to that resolution define triple cohomology.  For a
comonad (cotriple), contravariant coefficients turn the canonical simplicial
resolution into a cosimplicial object and define cotriple cohomology.

As in the cotriple-homology layer, existence of the canonical realizations from
the monad/comonad identities is theorem work; the Definitions sweep packages
the source formulas and defines the resulting cohomotopy objects.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.Monad

universe u v

variable {C : Type u} [Category.{v} C]

/-- The `n`-fold iterate `T^n(A)` of a monad endofunctor. -/
def iterObj (T : Monad C) (A : C) : ℕ → C
  | 0 => A
  | n + 1 => T.obj (iterObj T A n)

/-- The degree-`n` object `T^(n+1)(A)` of the canonical cosimplicial
construction. -/
abbrev cosimplicialDegree (T : Monad C) (A : C) (n : ℕ) : C :=
  T.iterObj A (n + 1)

/-- The coface maps of the canonical triple construction.  They insert the
unit in each of the `n+2` possible positions. -/
def coface (T : Monad C) (A : C) :
    (n : ℕ) → Fin (n + 2) → (T.iterObj A (n + 1) ⟶ T.iterObj A (n + 2))
  | 0, i => Fin.cases (T.η.app (T.obj A))
      (fun _ => T.map (T.η.app A)) i
  | n + 1, i => Fin.cases (T.η.app (T.iterObj A (n + 2)))
      (fun j => T.map (coface T A n j)) i

/-- The codegeneracy maps of the canonical triple construction.  They apply
the multiplication in each of the `n+1` possible positions. -/
def codegeneracy (T : Monad C) (A : C) :
    (n : ℕ) → Fin (n + 1) → (T.iterObj A (n + 2) ⟶ T.iterObj A (n + 1))
  | 0, _ => T.μ.app A
  | n + 1, i => Fin.cases (T.μ.app (T.iterObj A (n + 1)))
      (fun j => T.map (codegeneracy T A n j)) i

/-- A cosimplicial realization of Weibel's canonical triple formulas. -/
structure CosimplicialResolution (T : Monad C) (A : C) where
  /-- The realized cosimplicial object. -/
  obj : CosimplicialObject C
  /-- Identification of degree `n` with `T^(n+1)(A)`. -/
  degreeIso : ∀ n : ℕ, obj.obj ⦋n⦌ ≅ T.cosimplicialDegree A n
  /-- Compatibility of cofaces with the canonical unit-insertion formula. -/
  coface_comm : ∀ (n : ℕ) (i : Fin (n + 2)),
    (degreeIso n).hom ≫ T.coface A n i =
      obj.δ i ≫ (degreeIso (n + 1)).hom
  /-- Compatibility of codegeneracies with the canonical multiplication formula. -/
  codegeneracy_comm : ∀ (n : ℕ) (i : Fin (n + 1)),
    (degreeIso (n + 1)).hom ≫ T.codegeneracy A n i =
      obj.σ i ≫ (degreeIso n).hom

end CategoryTheory.Monad

namespace LeanCategories.Homological

universe u v uD vD

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]

/-- Weibel's triple cohomology `H^n(A;E)=π^n E(T^{*+1}A)`. -/
def tripleCohomology (T : Monad C) (A : C)
    (S : T.CosimplicialResolution A) (E : C ⥤ D) (n : ℕ) : D :=
  cosimplicialCohomotopyObject D (S.obj ⋙ E) n

/-- The cosimplicial object obtained by applying a contravariant coefficient
functor to a cotriple simplicial resolution. -/
def cotripleCoefficientCosimplicial (T : Comonad C) (A : C)
    (S : T.SimplicialResolution A) (E : Cᵒᵖ ⥤ D) : CosimplicialObject D :=
  (simplicialCosimplicialEquiv C).functor.obj (op S.obj) ⋙ E

/-- Weibel's cotriple cohomology with contravariant coefficients,
`H^n(A;E)=π^n E(T_*A)`. -/
def cotripleCohomology (T : Comonad C) (A : C)
    (S : T.SimplicialResolution A) (E : Cᵒᵖ ⥤ D) (n : ℕ) : D :=
  cosimplicialCohomotopyObject D (cotripleCoefficientCosimplicial T A S E) n

end LeanCategories.Homological
