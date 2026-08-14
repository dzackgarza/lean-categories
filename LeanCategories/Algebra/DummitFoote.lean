/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Concrete.Rings
public import LeanCategories.Algebra.GroupTheory
public import LeanCategories.Algebra.Ideals
public import LeanCategories.Algebra.Polynomial
public import LeanCategories.Algebra.StandardConstructions
public import LeanCategories.Modules.Foundations
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Foundation.Sets
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Setoid.Partition
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
existing owner module in `LeanCategories`. It adds no canonical-form,
Groebner-basis, or outer-automorphism theory.

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
