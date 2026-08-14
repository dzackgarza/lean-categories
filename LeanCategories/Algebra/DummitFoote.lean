/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Concrete.Rings
public import LeanCategories.Algebra.GroupTheory
public import LeanCategories.Algebra.Ideals
public import LeanCategories.Algebra.JordanCanonical
public import LeanCategories.Algebra.Polynomial
public import LeanCategories.Algebra.StandardConstructions
public import LeanCategories.Modules.Foundations
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Foundation.Sets
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Data.Matrix.Block
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Basis

@[expose] public section

/-!
# Dummit--Foote routes for Foundation 0.1

This module is a route index for the preliminary chapter and Chapters 1--12
of Dummit--Foote. Every declaration below is an alias to Mathlib or to an
existing owner module in `LeanCategories`, except for the Chapter 12
canonical-form data defined at the end of this file.

The chapter catalogue remains the source checklist. This file only exposes
the definitions that already have a mature implementation.
-/

namespace LeanCategories.Algebra.DummitFoote

universe u v w

/-! ## Preliminary chapter -/

abbrev EquivalenceRelation (α : Type u) := Setoid α

abbrev Partition (α : Type u) := Partitions α

abbrev Divisibility (a b : ℤ) : Prop := a ∣ b

abbrev GreatestCommonDivisor (a b : ℕ) : ℕ := Nat.gcd a b

abbrev CongruenceModulo (n a b : ℤ) : Prop := Int.ModEq n a b

abbrev ResidueClass (n : ℕ) := ZMod n

/-! ## Groups, subgroups, actions, and products -/

abbrev BinaryOperation (α : Type u) := α → α → α

abbrev GroupHom (G H : Type u) [Group G] [Group H] := G →* H

abbrev GroupIso (G H : Type u) [Group G] [Group H] := G ≃* H

abbrev SubgroupGenerated (G : Type u) [Group G] (s : Set G) : Subgroup G :=
  Subgroup.closure s

abbrev ActionKernel (G : Type u) [Group G] (X : Type v) [MulAction G X] : Subgroup G :=
  (MulAction.toPermHom G X).ker

abbrev ConjugacyClasses (G : Type u) [Group G] := ConjClasses G

abbrev ConjugationAction (G : Type u) [Group G] := ConjAct G

abbrev FaithfulAction (G : Type u) (X : Type v) [SMul G X] : Prop :=
  FaithfulSMul G X

abbrev TorsionSubgroup (G : Type u) [CommGroup G] : Subgroup G :=
  CommGroup.torsion G

abbrev PSubgroupCat (p : ℕ) (G : Type u) [Group G] :=
  ObjectProperty.FullSubcategory (C := Subgroup G) (fun H => IsPGroup p H)

abbrev SylowSubgroup (p : ℕ) (G : Type u) [Group G] := Sylow p G

abbrev SubgroupDirectProduct {G : Type u} [Group G]
    {H : Type v} [Group H] (K : Subgroup G) (L : Subgroup H) :
    Subgroup (G × H) :=
  K.prod L

/-! ## Rings, domains, and polynomial rings -/

abbrev RingHom (R : Type u) (S : Type v) [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] := R →+* S

abbrev RingIso (R : Type u) (S : Type v) [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] := R ≃+* S

abbrev Unit (R : Type u) [Monoid R] := Rˣ

abbrev Subring (R : Type u) [NonUnitalNonAssocSemiring R] := _root_.Subring R

abbrev EuclideanDomainStructure (R : Type u) := EuclideanDomain R

abbrev PrincipalIdealRingStructure (R : Type u) [Semiring R] :=
  IsPrincipalIdealRing R

abbrev UniqueFactorizationStructure (R : Type u) [CommMonoidWithZero R] :=
  UniqueFactorizationMonoid R

abbrev IrreducibleElement {R : Type u} [CommMonoidWithZero R] (r : R) : Prop :=
  Irreducible r

abbrev PrimeElement {R : Type u} [CommMonoidWithZero R] (r : R) : Prop :=
  Prime r

abbrev PolynomialRing (R : Type u) [Semiring R] := Polynomial R

abbrev MatrixRing (R : Type u) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Semiring R] := Matrix ι ι R

abbrev GroupRing (R : Type u) (G : Type v) [Semiring R] [Monoid G] :=
  MonoidAlgebra R G

abbrev PolynomialDegree {R : Type u} [Semiring R] (p : Polynomial R) : WithBot ℕ :=
  p.degree

abbrev PolynomialEvaluation {R : Type u} [Semiring R] {S : Type v} [Semiring S]
    (f : R →+* S) (x : S) : Polynomial R →+* S :=
  Polynomial.eval₂RingHom f x

abbrev PolynomialContent {R : Type u} [Semiring R] [NormalizedGCDMonoid R]
    (p : Polynomial R) : R :=
  p.content

abbrev PrimitivePolynomial {R : Type u} [Semiring R] [NormalizedGCDMonoid R]
    (p : Polynomial R) : Prop :=
  p.IsPrimitive

abbrev EisensteinPolynomial {R : Type u} [CommRing R]
    (p : Polynomial R) (P : Ideal R) : Prop :=
  p.IsEisensteinAt P

/-! ## Modules and linear algebra -/

abbrev ModuleHom (R : Type u) (M N : Type v) [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :=
  M →ₗ[R] N

abbrev GeneratedSubmodule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] (s : Set M) : Submodule R M :=
  Submodule.span R s

abbrev FinitelyGeneratedModule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.Finite R M

abbrev FreeModule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.Free R M

abbrev ProjectiveModule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.Projective R M

abbrev InjectiveModule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.Injective R M

abbrev FlatModule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.Flat R M

abbrev TorsionModule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.IsTorsion R M

abbrev TorsionFreeModule (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.IsTorsionFree R M

abbrev ModuleAnnihilator (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Ideal R :=
  Module.annihilator R M

abbrev TensorProduct (R : Type u) (M N : Type v) [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :=
  _root_.TensorProduct R M N

abbrev ModuleBasis (R : Type u) (ι : Type v) (M : Type w) [Semiring R]
    [AddCommMonoid M] [Module R M] :=
  Module.Basis ι R M

abbrev LinearIndependence (R : Type u) (ι : Type v) (M : Type w) [Semiring R]
    [AddCommMonoid M] [Module R M] (v : ι → M) : Prop :=
  LinearIndependent R v

abbrev ModuleRank (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] :=
  Module.rank R M

abbrev FiniteModuleDimension (K : Type u) (M : Type v) [DivisionRing K]
    [AddCommGroup M] [Module K M] :=
  Module.finrank K M

abbrev DualBasis (R : Type u) (ι : Type v) (M : Type w) [CommSemiring R]
    [AddCommMonoid M] [Module R M] (b : Module.Basis ι R M) :=
  b.dualBasis

abbrev MinimalPolynomial (K : Type u) (A : Type v) [Field K] [Semiring A]
    [Algebra K A] (x : A) : Polynomial K :=
  minpoly K x

end LeanCategories.Algebra.DummitFoote

namespace LeanCategories.Algebra.DummitFoote

universe u

/-!
## Canonical forms

The definitions in this section follow Dummit--Foote, Chapter 12,
"Canonical Forms", especially the companion-matrix and rational-canonical-form
definitions in Sections 12.1--12.2. Mathlib supplies the polynomial, matrix,
and dependent block-diagonal infrastructure used here, but does not supply
these canonical-form definitions in the pinned version.

The companion convention is the standard one for
`X^n + a_(n-1) X^(n-1) + ... + a_0`: ones occur on the subdiagonal and the
last column is `(-a_0, ..., -a_(n-1))`. No existence, uniqueness, or
classification theorem is asserted here.
-/

variable (R : Type u) [CommRing R]

/-- A monic nonconstant polynomial, the datum used for a companion block. -/
def IsCompanionPolynomial (f : Polynomial R) : Prop :=
  f.Monic ∧ f.natDegree ≠ 0

/-- The companion matrix of a monic nonconstant polynomial.

The matrix is indexed by `Fin f.natDegree`. The coefficient convention is
the one used in Dummit--Foote, Chapter 12, Section 12.1. -/
def companionMatrix {f : Polynomial R} (hf : IsCompanionPolynomial R f) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
  fun i j =>
    if j.1 + 1 = i.1 then 1
    else if j.1 + 1 = f.natDegree then -f.coeff i.1
    else 0

@[simp]
theorem companionMatrix_apply_subdiagonal {f : Polynomial R}
    (hf : IsCompanionPolynomial R f) (i j : Fin f.natDegree)
    (h : j.1 + 1 = i.1) : companionMatrix R hf i j = 1 := by
  simp [companionMatrix, h]

@[simp]
theorem companionMatrix_apply_off_last_column {f : Polynomial R}
    (hf : IsCompanionPolynomial R f) (i j : Fin f.natDegree)
    (hij : j.1 + 1 ≠ i.1) (hj : j.1 + 1 ≠ f.natDegree) :
    companionMatrix R hf i j = 0 := by
  simp [companionMatrix, hij, hj]

/-- Ordered monic nonconstant invariant factors.

The factors are indexed by `Fin r` and satisfy `f i ∣ f j` for `i ≤ j`.
This is the data appearing in the rational canonical form, not a theorem
that every linear operator has such data. -/
structure InvariantFactorData (r : ℕ) where
  factor : Fin r → Polynomial R
  monic : ∀ i, (factor i).Monic
  nonconstant : ∀ i, (factor i).natDegree ≠ 0
  divisibility : ∀ ⦃i j : Fin r⦄, i ≤ j → factor i ∣ factor j

/-- The index type of the companion blocks in a rational canonical matrix. -/
abbrev invariantFactorIndex {r : ℕ} (d : InvariantFactorData R r) : Type u :=
  Σ i : Fin r, Fin (d.factor i).natDegree

/-- The total dimension of a rational canonical matrix. -/
def invariantFactorDimension {r : ℕ} (d : InvariantFactorData R r) : ℕ :=
  Fintype.card (invariantFactorIndex R d)

/-- The rational canonical matrix associated with ordered invariant factors.

It is Mathlib's dependent block diagonal of the companion matrices of the
invariant factors. -/
def rationalCanonicalMatrix {r : ℕ} (d : InvariantFactorData R r) :
    Matrix (invariantFactorIndex R d) (invariantFactorIndex R d) R :=
  Matrix.blockDiagonal' fun i =>
    companionMatrix R ⟨d.monic i, d.nonconstant i⟩

end LeanCategories.Algebra.DummitFoote
