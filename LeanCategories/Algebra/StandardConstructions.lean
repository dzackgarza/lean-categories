/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import LeanCategories.Algebra.FreeAlgebras

/-!
# Standard algebra-construction routes

Mathlib owns the standard polynomial, power-series, Laurent-series, tensor,
tensor-algebra, exterior-algebra, and symmetric-algebra constructions. This
module exposes their canonical definitions and algebra structures directly.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u v

variable (R : Type u) [CommRing R]

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Base change of commutative algebras along `R ⟶ S`, via Mathlib's
`CommRingCat.tensorProd` and the equivalences with under-categories. -/
abbrev commAlgBaseChange : CommAlgCat R ⥤ CommAlgCat S :=
  (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
    CommRingCat.tensorProd R S ⋙
      (commAlgCatEquivUnder (CommRingCat.of S)).inverse

end BaseChange

/-- The category of (not necessarily commutative) algebras over `R`.

This is the project name for Mathlib's canonical `AlgCat` category. -/
abbrev AlgebraCat := AlgCat

namespace AlgebraCat

section AlgebraicClosure

variable (K : Type u) [Field K]

/-- Mathlib's canonical algebraic closure of a field, viewed as a `K`-algebra. -/
abbrev algebraicClosure : AlgebraCat K := .of K (AlgebraicClosure K)

/-- The canonical structure morphism into `AlgebraicClosure K`. -/
abbrev algebraicClosureMap : AlgebraCat.of K K ⟶ algebraicClosure K :=
  AlgCat.ofHom (Algebra.ofId K (AlgebraicClosure K)).toAlgHom

end AlgebraicClosure

section SeparableClosure

variable (K : Type u) [Field K]

/-! Mathlib's absolute separable closure, with its canonical `K`-algebra
structure and structure morphism. -/

/-- Mathlib's canonical separable closure of a field, viewed as a `K`-algebra. -/
abbrev separableClosure : AlgebraCat K := .of K (SeparableClosure K)

/-- The canonical structure morphism into `SeparableClosure K`. -/
abbrev separableClosureMap : AlgebraCat.of K K ⟶ separableClosure K :=
  AlgCat.ofHom (Algebra.ofId K (SeparableClosure K)).toAlgHom

end SeparableClosure

section SplittingField

variable (K : Type u) [Field K]

/-- Mathlib's canonical splitting field of a polynomial, viewed as a `K`-algebra. -/
abbrev splittingField (f : Polynomial K) : AlgebraCat K := .of K f.SplittingField

/-- The canonical structure morphism into the splitting field of `f`. -/
abbrev splittingFieldMap (f : Polynomial K) : AlgebraCat.of K K ⟶ splittingField K f :=
  AlgCat.ofHom (algebraMap K f.SplittingField)

end SplittingField

section TensorProduct

variable (A B : Type v) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/** The tensor product of two commutative `R`-algebras, as an `R`-algebra. */
abbrev tensorProduct : AlgebraCat R := .of R (TensorProduct R A B)

/** The canonical left algebra morphism into the tensor product algebra. */
abbrev tensorProductIncludeLeft : AlgebraCat.of R A ⟶ tensorProduct R A B :=
  AlgCat.ofHom Algebra.TensorProduct.includeLeft

/** The canonical right algebra morphism into the tensor product algebra. */
abbrev tensorProductIncludeRight : AlgebraCat.of R B ⟶ tensorProduct R A B :=
  AlgCat.ofHom Algebra.TensorProduct.includeRight

end TensorProduct

/-- The polynomial algebra over `R`. -/
abbrev polynomial : AlgebraCat R := .of R (Polynomial R)

section PolynomialEvaluation

variable {R : Type u} [CommRing R]

/** Evaluation of a polynomial at an element of its coefficient ring. */
abbrev polynomialEvaluation (x : R) : polynomial R ⟶ AlgCat.of R R :=
  AlgCat.ofHom (Polynomial.aeval x)

end PolynomialEvaluation

section GroupRing

variable {R : Type u} [CommRing R] {G : Type v} [Group G]

/** The group ring `R[G]`, using Mathlib's monoid-algebra construction. */
abbrev groupRing : AlgebraCat R := .of R (MonoidAlgebra R G)

/** The canonical coefficient embedding `R ⟶ R[G]`. */
abbrev groupRingCoefficient : AlgCat.of R R ⟶ groupRing (R := R) (G := G) :=
  AlgCat.ofHom (MonoidAlgebra.singleOneAlgHom (R := R) (A := R) (M := G))

end GroupRing

/-- The multivariate polynomial algebra over `R`, with variables indexed by `σ`. -/
abbrev mvPolynomial (σ : Type v) : AlgebraCat R := .of R (MvPolynomial σ R)

/-- The formal power-series algebra over `R`. -/
abbrev powerSeries : AlgebraCat R := .of R (PowerSeries R)

/-- The multivariate formal power-series algebra over `R`, with variables indexed by `σ`. -/
abbrev mvPowerSeries (σ : Type v) : AlgebraCat R := .of R (MvPowerSeries σ R)

/- Laurent series have a canonical constant-term embedding of `R`. -/
instance : Algebra R (LaurentSeries R) :=
  RingHom.toAlgebra (HahnSeries.C : R →+* LaurentSeries R)

/-- The formal Laurent-series algebra over `R`. -/
abbrev laurentSeries : AlgebraCat R := .of R (LaurentSeries R)

/-- The localization of `R` at a submonoid, as an `R`-algebra. -/
abbrev localization (M : Submonoid R) : AlgebraCat R := .of R (Localization M)

/-- The canonical structure morphism into the localization algebra. -/
abbrev localizationMap (M : Submonoid R) : R →ₐ[R] (localization R M).carrier :=
  algebraMap R (Localization M)

/-- The localization of `R` away from one element, as an `R`-algebra.

This is Mathlib's canonical `Localization.Away` construction. -/
abbrev localizationAway (r : R) : AlgebraCat R :=
  .of R (Localization.Away r)

/-- The canonical structure morphism into the localization away from `r`. -/
abbrev localizationAwayMap (r : R) : R →ₐ[R] (localizationAway R r).carrier :=
  algebraMap R (Localization.Away r)

/-- The localization of `R` at the prime ideal `P`, as an `R`-algebra.

This is Mathlib's canonical `Localization.AtPrime` construction. -/
abbrev localizationAtPrime (P : Ideal R) [P.IsPrime] : AlgebraCat R :=
  .of R (Localization.AtPrime P)

/-- The canonical structure morphism into the localization at a prime ideal. -/
abbrev localizationAtPrimeMap (P : Ideal R) [P.IsPrime] :
    R →ₐ[R] (localizationAtPrime R P).carrier :=
  algebraMap R (Localization.AtPrime P)

section FractionRing

variable [IsDomain R]

/-- The fraction ring of an integral domain, as an `R`-algebra. -/
abbrev fractionRing : AlgebraCat R :=
  .of R (FractionRing R)

/-- The canonical structure morphism into the fraction ring. -/
abbrev fractionRingMap : R →ₐ[R] (fractionRing R).carrier :=
  algebraMap R (FractionRing R)

end FractionRing

/-- The `I`-adic completion of `R`, as an `R`-algebra. -/
abbrev adicCompletion (I : Ideal R) : AlgebraCat R :=
  .of R (AdicCompletion I R)

/-- The canonical map from `R` into its `I`-adic completion. -/
abbrev adicCompletionMap (I : Ideal R) : R →ₐ[R] (adicCompletion R I).carrier :=
  algebraMap R (AdicCompletion I R)

/-- The quotient of an `R`-algebra by a two-sided ideal. -/
abbrev quotient (A : AlgebraCat R) (I : Ideal A.carrier) [I.IsTwoSided] : AlgebraCat R :=
  .of R (A.carrier ⧸ I)

/-- The canonical quotient morphism of `R`-algebras. -/
abbrev quotientMap (A : AlgebraCat R) (I : Ideal A.carrier) [I.IsTwoSided] :
    A ⟶ quotient R A I :=
  AlgCat.ofHom (Ideal.Quotient.mkₐ R I)

end AlgebraCat
end LeanCategories.Algebra
