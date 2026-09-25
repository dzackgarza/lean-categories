/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Minimal regular presentations and generator number

Definition-level transcription of Matsumura, *Commutative Ring Theory*,
§21, p. 170 (`FC13-C07-U047`).

For a finite module `M` over a local ring `R`, Matsumura defines

`μ_R(M) = dim_{R / 𝔪} (M / 𝔪 M)`.

For a regular local ring `R`, a quotient presentation `R / I` is minimal
when `I ⊆ 𝔪²`. The later identity `ε₁(R/I) = μ_R(I)` is result content
and is deliberately not part of this file.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open IsLocalRing

universe u v

section GeneratorNumber

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Matsumura's minimal number of generators
`μ_R(M) = dim_{R / 𝔪}(M / 𝔪M)`.

The `Module.Finite R M` hypothesis is retained because it is part of the
source definition's quantified data. -/
def minimalGeneratorNumber : ℕ :=
  let _ : Module (ResidueField R)
      (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) :=
    Module.instQuotientIdealSubmoduleHSMulTop M (maximalIdeal R)
  Module.finrank (ResidueField R)
    (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M))

end GeneratorNumber

section MinimalPresentation

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- A quotient presentation `R / I` by a regular local ring is minimal when
its defining ideal is contained in the square of the maximal ideal. This is
precisely Matsumura's defining condition `I ⊆ 𝔪²`.

The presented ring itself is the native quotient `R ⧸ I`; no existence,
uniqueness, or comparison theorem is bundled into the predicate. -/
def IsMinimalRegularPresentation (I : Ideal R) : Prop :=
  I ≤ (maximalIdeal R) ^ 2

end MinimalPresentation

end LeanCategories.Algebra
