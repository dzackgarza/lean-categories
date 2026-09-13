/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DifferentialGradedAlgebra
public import LeanCategories.Homological.HochschildComplex
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Hochschild homology of differential graded algebras

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.9.10,
pp. 354--361 (FC05-C09-U149).

For a homologically graded DG-algebra `(A,d)`, the Hochschild direction and
the internal differential direction form a bicomplex.  Its direct-sum total
complex defines DG Hochschild homology.  This file records the homogeneous
bidegree pieces and packages a realization of that bicomplex; verification
that the signed Hochschild and internal formulas produce the realization is
the construction/result layer surrounding the definition.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped BigOperators TensorProduct

universe u v

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]
variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/- Mathlib currently provides tensor-total signs for `down ℕ` and `up ℤ`,
but not for the homological integer shape `down ℤ` used by Weibel here. -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
local instance : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r hpq := by
    change q + 1 = p at hpq
    change q + r + 1 = p + r
    omega
  add_rel p q r hpq := by
    change q + 1 = p at hpq
    change r + q + 1 = r + p
    omega
  ε'_succ p q hpq := by
    change q + 1 = p at hpq
    have h : p = q + 1 := by omega
    subst p
    dsimp
    rw [Int.negOnePow_succ, neg_neg]

/-- A homogeneous pure Hochschild tensor in a graded algebra, together with
the internal degree of every tensor factor. -/
structure HomogeneousDGHochschildTensor (n : ℕ) where
  degree0 : ℤ
  degrees : Fin n → ℤ
  a0 : 𝒜 degree0
  a : ∀ i : Fin n, 𝒜 (degrees i)

namespace HomogeneousDGHochschildTensor

/-- Total internal degree of a homogeneous Hochschild tensor. -/
def internalDegree {n : ℕ} (x : HomogeneousDGHochschildTensor k A 𝒜 n) : ℤ :=
  x.degree0 + ∑ i, x.degrees i

/-- The underlying pure Hochschild chain. -/
def toChain {n : ℕ} (x : HomogeneousDGHochschildTensor k A 𝒜 n) :
    HochschildChainDegree (k := k) (R := A) (M := A) n :=
  hochschildChainPure (k := k) (R := A) (M := A) (x.a0 : A)
    (fun i => (x.a i : A))

end HomogeneousDGHochschildTensor

/-- Homogeneous pure Hochschild chains of internal degree `q`. -/
def dgHochschildGenerators (n : ℕ) (q : ℤ) :
    Set (HochschildChainDegree (k := k) (R := A) (M := A) n) :=
  {z | ∃ x : HomogeneousDGHochschildTensor k A 𝒜 n,
    x.internalDegree = q ∧ x.toChain = z}

/-- The internal-degree-`q` submodule of Hochschild degree `n`. -/
def dgHochschildBidegree (n : ℕ) (q : ℤ) :
    Submodule k (HochschildChainDegree (k := k) (R := A) (M := A) n) :=
  Submodule.span k (dgHochschildGenerators k A 𝒜 n q)

/-- A realization of Weibel's DG Hochschild bicomplex.  The outer homological
direction is Hochschild degree and the inner homological direction is internal
DG degree.  The bicomplex axioms carry the square-zero and anticommutation
identities after the source sign conventions have been verified. -/
structure DGHochschildDoubleComplexRealization
    (D : DifferentialGradedAlgebra k A 𝒜) where
  /-- The DG Hochschild bicomplex. -/
  bicomplex : HomologicalComplex₂ (ModuleCat k)
    (ComplexShape.down ℤ) (ComplexShape.down ℤ)
  /-- Bidegree `(n,q)` is the internal-degree-`q` part of Hochschild degree
  `n`. -/
  degreeIso : ∀ (n : ℕ) (q : ℤ),
    (bicomplex.X (n : ℤ)).X q ≅ ModuleCat.of k ↥(dgHochschildBidegree k A 𝒜 n q)
  /-- Negative Hochschild columns vanish; this is the reindexing of the
  nonnegative Hochschild direction inside the integer-graded total complex. -/
  zeroNegative : ∀ (p q : ℤ), p < 0 → CategoryTheory.Limits.IsZero ((bicomplex.X p).X q)

/-- The direct-sum total complex defining DG Hochschild homology. -/
def dgHochschildTotalComplex
    {D : DifferentialGradedAlgebra k A 𝒜}
    (H : DGHochschildDoubleComplexRealization k A 𝒜 D)
    [HomologicalComplex₂.HasTotal H.bicomplex (ComplexShape.down ℤ)] :
    ChainComplex (ModuleCat k) ℤ :=
  HomologicalComplex₂.total H.bicomplex (ComplexShape.down ℤ)

/-- Weibel's DG Hochschild homology: homology of the direct-sum total complex
of the DG Hochschild bicomplex.

Source: Weibel, Definition 9.9.10, pp. 354--361 (FC05-C09-U149). -/
def dgHochschildHomology
    {D : DifferentialGradedAlgebra k A 𝒜}
    (H : DGHochschildDoubleComplexRealization k A 𝒜 D)
    [HomologicalComplex₂.HasTotal H.bicomplex (ComplexShape.down ℤ)]
    (n : ℤ) : ModuleCat k :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℤ) n).obj
    (dgHochschildTotalComplex k A 𝒜 H)

end LeanCategories.Homological
