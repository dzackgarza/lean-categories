/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Integral and dominant integral weights

Definition-level realization of Humphreys FC14-C06-U015.  Integrality is
stated on every root coroot, while dominant integrality additionally requires
nonnegative integral values on the simple coroots of the chosen base.

The theorem that checking simple roots already implies integrality on all
roots, additive-lattice closure, and all representation-theoretic
consequences are not included here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open LieAlgebra LieModule Module

universe u v

variable
  {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H L]

/-- Humphreys' integral-weight predicate: every root coroot has an integer
value under `lam`. -/
def IsIntegralWeight (lam : Module.Dual K H) : Prop :=
  ∀ α : H.root, ∃ z : ℤ,
    lam ((LieAlgebra.IsKilling.rootSystem H).coroot α) = (z : K)

/-- Humphreys' dominant-integral predicate relative to a chosen base.  We
retain integrality on all roots explicitly and require natural-number values
on the simple coroots. -/
def IsDominantIntegralWeight
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (lam : Module.Dual K H) : Prop :=
  IsIntegralWeight lam ∧
    ∀ i ∈ b.support, ∃ n : ℕ,
      lam ((LieAlgebra.IsKilling.rootSystem H).coroot i) = (n : K)

/-- The carrier of the source weight lattice `Λ`, before adding any closure
theorems as bundled structure. -/
def integralWeightSet : Set (Module.Dual K H) :=
  {lam | IsIntegralWeight lam}

/-- The carrier `Λ⁺` of dominant integral weights for `b`. -/
def dominantIntegralWeightSet
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    Set (Module.Dual K H) :=
  {lam | IsDominantIntegralWeight b lam}

end LeanCategories.Algebra
