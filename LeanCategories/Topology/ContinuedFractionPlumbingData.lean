/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.DiscBundlePlumbingData
public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.Rev

/-!
# Continued-fraction disc-bundle plumbing

Definition-level realization of the construction clause in Peters--Sterk
FC11-C04-U050.

The source specializes tree plumbing to the linear graph with vertices
`0, ..., n` and weights `a_i = -m_i`, where the `m_i` are the coefficients
produced by the preceding Euclidean/continued-fraction discussion.  The
resulting plumbed disc-bundle space is denoted `Y(s,t)` after the later
identification with the lens-space boundary problem.

Sweep III records the finite negative continued fraction selecting the supplied
coefficient sequence, the linear weighted plumbing data, and its resulting
quotient.  Proving that the source Euclidean algorithm produces such a
sequence, and proving that the quotient has boundary the stated lens space, is
simply connected, deformation retracts onto the string of spheres, or has the
stated homology basis and intersection matrix are result-layer content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

/-- The linear graph underlying a continued-fraction plumbing with
`n + 1` vertices. -/
abbrev continuedFractionPlumbingGraph (n : ℕ) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.pathGraph (n + 1)

/-- Peters--Sterk's vertex weights `a_i = -m_i` for the linear plumbing. -/
def continuedFractionPlumbingWeight {n : ℕ}
    (m : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => -m i

/-- The source finite continued fraction
`[a₀, ..., aₙ] = a₀ - 1/(a₁ - 1/(... - 1/aₙ))`, represented by Mathlib's
generalized continued fraction with every partial numerator equal to `-1`. -/
def finiteNegativeContinuedFraction {n : ℕ}
    (a : Fin (n + 1) → ℤ) : GenContFract ℚ where
  h := a 0
  s := Stream'.Seq.ofList <| List.ofFn fun i : Fin n =>
    ⟨-1, a i.succ⟩

/-- The rational value of the finite negative continued fraction
`[a₀, ..., aₙ]`. -/
def finiteNegativeContinuedFractionValue {n : ℕ}
    (a : Fin (n + 1) → ℤ) : ℚ :=
  (finiteNegativeContinuedFraction a).convs' n

/-- The source relation between a lens-space pair `(s,t)` and the plumbing
coefficients `m₀, ..., mₙ`: in the source order,
`-t/s = [-mₙ, ..., -m₀]`.

This is a predicate on supplied data, not a proof that the Euclidean algorithm
produces such data. -/
def IsLensPlumbingCoefficientSequence
    (s t : ℤ) {n : ℕ} (m : Fin (n + 1) → ℤ) : Prop :=
  finiteNegativeContinuedFractionValue
      (fun i => -(m (Fin.rev i))) =
    -((t : ℚ) / (s : ℚ))

/-- A supplied realization of the source's linear weighted plumbing.

The coefficient family `m` is the output data of the preceding
Euclidean/continued-fraction construction.  The field
`isLensCoefficientSequence` records the defining continued-fraction equation
for the supplied pair `(s,t)`; it does not prove that the Euclidean algorithm
constructs such a sequence. -/
structure ContinuedFractionDiscBundlePlumbingData
    (s t : ℤ) (n : ℕ) (I : WeightedDiscBundleInterface.{u}) where
  m : Fin (n + 1) → ℤ
  isLensCoefficientSequence : IsLensPlumbingCoefficientSequence s t m
  plumbing : DiscBundleTreePlumbingData (Fin (n + 1)) I
  graph_eq : plumbing.graph = continuedFractionPlumbingGraph n
  weight_eq : plumbing.weight = continuedFractionPlumbingWeight m

/-- The underlying quotient carrier of the continued-fraction plumbing. -/
abbrev continuedFractionPlumbingYCarrier
    {s t : ℤ} {n : ℕ} {I : WeightedDiscBundleInterface.{u}}
    (P : ContinuedFractionDiscBundlePlumbingData s t n I) : Type u :=
  plumbedDiscBundleTree P.plumbing

/-- The source's data-level plumbed space `Y`: the linear specialization of
tree plumbing with weights `-m_i`.

The notation `Y(s,t)` becomes justified only after the later result relating
the Euclidean coefficient sequence to the lens-space boundary. -/
def continuedFractionPlumbingY
    {s t : ℤ} {n : ℕ} {I : WeightedDiscBundleInterface.{u}}
    (P : ContinuedFractionDiscBundlePlumbingData s t n I) : TopCat.{u} :=
  plumbedDiscBundleTreeTopCat P.plumbing

end LeanCategories.Topology
