/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.UniformSpace.Completion

/-!
# Completed maximal-unramified extension data

Definition-level realization of Neukirch FC09-C05-U014.

Let `K̃/K` be the maximal unramified extension of a nonarchimedean local
field, with arithmetic Frobenius `φ ∈ Aut_K(K̃)`.  Neukirch writes `K̂` for
the completion of `K̃` and extends `φ` to `K̂` by continuity.

The generic construction of the maximal unramified extension itself is not
available for an arbitrary local field in the checked libraries.  This unit
does not assert its existence: it takes the source-supplied model `K̃/K` and
its `K`-algebra Frobenius as inputs.  Mathlib already owns the Hausdorff
uniform completion and its map construction, so the two source conventions
are represented directly by `UniformSpace.Completion K̃` and
`UniformSpace.Completion.map φ`.

Uniform continuity of the supplied Frobenius is recorded as a predicate, not
as a prerequisite for constructing the raw completion map.  Agreement of the
completion map with `φ`, preservation of field operations, and the assertion
that it is an automorphism are result-layer statements once that continuity
input is available.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

variable
  (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ktilde : Type v) [Field Ktilde] [Algebra K Ktilde] [UniformSpace Ktilde]

/-- The source Frobenius datum on a supplied model of the maximal unramified
extension `K̃/K`.

The type is exactly the `K`-algebra automorphism occurring in Neukirch's
notation `φ ∈ G(K̃/K)`.  Maximality and unramifiedness describe the supplied
model `K̃`; U014 does not construct or prove those properties. -/
abbrev MaximalUnramifiedFrobeniusData := Ktilde ≃ₐ[K] Ktilde

/-- The continuity condition needed for the completion map to be the genuine
continuous extension of the source Frobenius in both directions.

This is kept as a predicate rather than bundled into the datum, so Sweep III
does not require a continuity proof in order to construct the completion or
its raw Frobenius map. -/
def IsUniformMaximalUnramifiedFrobeniusData
    (φ : MaximalUnramifiedFrobeniusData K Ktilde) : Prop :=
  UniformContinuous φ ∧ UniformContinuous φ.symm

/-- Neukirch's `K̂`: the Hausdorff uniform completion of the supplied maximal
unramified extension `K̃`. -/
abbrev completedMaximalUnramifiedExtensionData :=
  UniformSpace.Completion Ktilde

/-- The canonical map `K̃ → K̂` into the completion. -/
def maximalUnramifiedToCompletionData :
    Ktilde → completedMaximalUnramifiedExtensionData Ktilde :=
  fun x => x

/-- The raw extension of Frobenius to `K̂` supplied by the uniform completion
construction.

`Completion.map` is total for every map.  Under
`IsUniformMaximalUnramifiedFrobeniusData`, Mathlib's completion API identifies
this map with the continuous extension of `φ`; that identification and the
resulting automorphism laws are deliberately not proved in Sweep III. -/
def completedMaximalUnramifiedFrobeniusData
    (φ : MaximalUnramifiedFrobeniusData K Ktilde) :
    completedMaximalUnramifiedExtensionData Ktilde →
      completedMaximalUnramifiedExtensionData Ktilde :=
  UniformSpace.Completion.map φ

end LeanCategories.Algebra
