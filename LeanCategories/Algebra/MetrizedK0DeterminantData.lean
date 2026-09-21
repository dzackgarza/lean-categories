/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.MetrizedModuleOperationsData
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Determinant data for metrized Grothendieck groups

Definition-level realization of Neukirch FC09-C03-U108.

For a projective metrized module `M` of rank `n`, Neukirch's determinant
object is its top exterior power equipped with the determinant metric.  Its
isometry class determines a class in the replete Picard group.  Extending this
class assignment linearly gives the representative-level map on the free
abelian group `F₀`.

The source then uses determinant multiplicativity in admissible short exact
sequences to show that the relation subgroup `R₀` maps to zero and therefore
that the representative map descends to `K₀ = F₀ / R₀`.

Sweep III records only the determinant object, the free extension, and the
representative formula expected of the descended map.  Exact-sequence
multiplicativity, annihilation of `R₀`, well-defined quotient descent, and
the assertion that the resulting map is a homomorphism are result-layer
statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe uR uM uP uPic

variable
  {R : Type uR} [CommRing R] [Star R]
  {M : Type uM} [AddCommGroup M] [Module R M]

/-- The underlying determinant line of a rank-`n` metrized module. -/
abbrev metrizedDeterminantLineData (n : ℕ) :=
  ⋀[R]^n M

/-- Neukirch's determinant metric on the top exterior power, obtained from
the determinant formula already realized in FC09-C03-U082. -/
def metrizedDeterminantMetricData
    (n : ℕ) (hM : MetricPairingData R M) :
    MetricPairingData R (metrizedDeterminantLineData (R := R) (M := M) n) :=
  exteriorPowerMetricData n hM

/-- Generic carrier of the source's replete Grothendieck quotient
`K₀ = F₀/R₀`, once the type `P` of isometry classes and relation subgroup
have been supplied by FC09-C03-U092/U093. -/
abbrev MetrizedKZeroCarrierData
    (P : Type uP) (relations : AddSubgroup (FreeAbelianGroup P)) :=
  FreeAbelianGroup P ⧸ relations

/-- The determinant-class assignment on the free abelian group `F₀`.

`detClass` is the already-mapped assignment sending an isometry class of a
projective metrized module to the corresponding class of its determinant line
in the replete Picard group.  The target is written additively solely to use
the universal property of `FreeAbelianGroup`; no quotient descent occurs
here. -/
def metrizedDeterminantFreeHomData
    {P : Type uP} {Pic : Type uPic} [CommGroup Pic]
    (detClass : P → Pic) :
    FreeAbelianGroup P →+ Additive Pic :=
  FreeAbelianGroup.lift fun p => Additive.ofMul (detClass p)

/-- Representative-level characterization of Neukirch's determinant map on
`K₀`.

This is the formula that the descended map must satisfy on every generator.
The fact that such a function is well defined on the quotient is precisely the
later determinant-multiplicativity/descent theorem. -/
def IsMetrizedKZeroDeterminantData
    {P : Type uP} {Pic : Type uPic} [CommGroup Pic]
    (relations : AddSubgroup (FreeAbelianGroup P))
    (detClass : P → Pic)
    (det :
      MetrizedKZeroCarrierData P relations → Additive Pic) : Prop :=
  ∀ p : P,
    det (QuotientAddGroup.mk' relations (FreeAbelianGroup.of p)) =
      Additive.ofMul (detClass p)

/-- Neukirch's determinant map on the Grothendieck quotient, selected by its
generator formula.

Sweep III deliberately records this as an ordinary function.  Proving that it
satisfies `IsMetrizedKZeroDeterminantData`, is additive/multiplicative in
Neukirch's sense, and is induced by the free homomorphism above all depend on
the exact-sequence determinant isometry of FC09-C03-U091 and remain Sweep IV. -/
def metrizedKZeroDeterminantData
    {P : Type uP} {Pic : Type uPic} [CommGroup Pic]
    (relations : AddSubgroup (FreeAbelianGroup P))
    (detClass : P → Pic) :
    MetrizedKZeroCarrierData P relations → Additive Pic :=
  Classical.epsilon (IsMetrizedKZeroDeterminantData relations detClass)

end LeanCategories.Algebra
