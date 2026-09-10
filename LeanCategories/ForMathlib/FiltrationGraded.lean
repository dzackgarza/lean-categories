/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Filtration

/-!
# The graded module attached to an ideal filtration

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed
pp. 106–107, FC04-C10-U030. The graded ring `A* = ⨁ n, I^n` already has its
multiplicative structure from Mathlib's graded powers of a submodule. For an
`I`-filtration `F`, the only missing compatibility is that a degree-`i` element
of `I^i` sends `F.N j` into `F.N (i+j)`; this is exactly `F.pow_smul_le`.
Mathlib then supplies the module structure on `⨁ n, F.N n` over `⨁ n, I^n`.

No stability hypothesis is required: stability is the later finite-generation
criterion, not part of the source construction of the graded module.
-/

@[expose] public section

open DirectSum

namespace Ideal.Filtration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Ideal R} (F : I.Filtration M)

/-- Ideal powers act homogeneously on the pieces of every ideal filtration. -/
instance gradedSMulPowers :
    SetLike.GradedSMul (fun n : ℕ => (I ^ n : Ideal R)) F.N where
  smul_mem {i j} {_ _} ha hb :=
    F.pow_smul_le i j (Submodule.smul_mem_smul ha hb)

-- The source's graded module is obtained directly from the existing direct-sum machinery.
example : Module (⨁ n : ℕ, (I ^ n : Ideal R)) (⨁ n : ℕ, F.N n) := inferInstance

-- Stability is deliberately not needed for the construction.
example (N : Submodule R M) :
    Module (⨁ n : ℕ, (I ^ n : Ideal R)) (⨁ n : ℕ, (I.trivialFiltration N).N n) := inferInstance

end Ideal.Filtration
