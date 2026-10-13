/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DGHochschildHomology
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Differential-graded cyclic construction data

Weibel, *An Introduction to Homological Algebra* (1994), §9.9 after
Definition 9.9.10, pp. 354--361 (FC05-C09-U150).

Sweep III records the data appearing in the source construction: the Koszul
sign on cyclic rotation, the direct-sum indexing of the ordinary Tsygan total,
the product indexing of the periodic total, and the signs attached to the
three differential directions.  Proving the cyclic identities, assembling
these data into cyclic objects or chain complexes, and taking their homology
are result-layer work and are not manufactured here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open scoped BigOperators TensorProduct

universe u v

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]
variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- The positivity hypothesis used for periodic DG cyclic homology. -/
def IsNonnegativelyGraded : Prop :=
  ∀ q : ℤ, q < 0 → 𝒜 q = ⊥

/-- Koszul exponent for moving the last homogeneous Hochschild factor to the
front.  For degrees `a₀,…,aₙ` this is
`aₙ(a₀+⋯+aₙ₋₁)`. -/
def dgCyclicRotationExponent :
    (n : ℕ) → HomogeneousDGHochschildTensor k A 𝒜 n → ℤ
  | 0, _ => 0
  | n + 1, x =>
      x.degrees (Fin.last n) *
        (x.degree0 + ∑ j : Fin n, x.degrees j.castSucc)

/-- The signed cyclic rotation on a homogeneous pure Hochschild tensor.

This is the displayed source formula only.  No assertion that it descends to
a chain automorphism or satisfies a cyclic identity is part of this
definition. -/
def dgCyclicPureRotation :
    (n : ℕ) → HomogeneousDGHochschildTensor k A 𝒜 n →
      HochschildChainDegree (k := k) (R := A) (M := A) n
  | 0, x => x.toChain
  | n + 1, x =>
      (dgCyclicRotationExponent k A 𝒜 (n + 1) x).negOnePow •
        hochschildChainPure (k := k) (R := A) (M := A)
          (x.a (Fin.last n) : A)
          (Fin.cons (x.a0 : A) (fun j : Fin n => (x.a j.castSucc : A)))

/-- The two nonnegative indices of the ordinary DG Tsygan total: cyclic
column and Hochschild degree.  The internal degree is determined by the total
degree. -/
abbrev DGCyclicTotalIndex := ℕ × ℕ

/-- Internal degree belonging to a cyclic-column/Hochschild-degree pair in
total degree `n`. -/
def dgCyclicInternalDegree (n : ℤ) (j : DGCyclicTotalIndex) : ℤ :=
  n - (j.1 : ℤ) - (j.2 : ℤ)

/-- Degree-`n` carrier of the direct-sum DG Tsygan total, before a
differential is installed. -/
def dgCyclicTotalDegree (n : ℤ) :=
  DirectSum DGCyclicTotalIndex (fun j =>
    ↥(dgHochschildBidegree k A 𝒜 j.2 (dgCyclicInternalDegree n j)))

/-- Signs multiplying the horizontal, Hochschild, and internal differential
directions in cyclic column `i` and Hochschild degree `q`:
`(1,(-1)^i,(-1)^(i+q))`. -/
def dgCyclicTotalDifferentialSigns (i q : ℕ) : ℤ × ℤ × ℤ :=
  (1, ((i : ℤ).negOnePow : ℤ), (((i + q : ℕ) : ℤ).negOnePow : ℤ))

/-- The nonnegative Hochschild/internal indices of the periodic product
total.  In total degree `n`, the cyclic column is determined by these two
indices. -/
abbrev DGPeriodicCyclicTotalIndex := ℕ × ℕ

/-- Cyclic column attached to a periodic-total component in total degree
`n`. -/
def dgPeriodicCyclicColumn (n : ℤ) (j : DGPeriodicCyclicTotalIndex) : ℤ :=
  n - (j.1 : ℤ) - (j.2 : ℤ)

/-- Degree-`n` carrier of the periodic product total for a nonnegatively
graded DG-algebra.  The first index is Hochschild degree and the second is
internal degree; the cyclic column is `dgPeriodicCyclicColumn n j`. -/
def dgPeriodicCyclicTotalDegree (_n : ℤ) :=
  (j : DGPeriodicCyclicTotalIndex) →
    ↥(dgHochschildBidegree k A 𝒜 j.1 (j.2 : ℤ))

/-- Periodic-total signs for cyclic column `i` and Hochschild degree `q`.
These are the same three-direction signs as in the ordinary total. -/
def dgPeriodicCyclicTotalDifferentialSigns (i : ℤ) (q : ℕ) : ℤ × ℤ × ℤ :=
  (1, (i.negOnePow : ℤ), ((i + q).negOnePow : ℤ))

end LeanCategories.Homological
