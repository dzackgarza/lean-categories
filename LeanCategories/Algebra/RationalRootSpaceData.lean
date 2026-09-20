/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Data.Real.Basic

/-!
# Rational and real root-space carriers

Definition-level realization of Humphreys FC14-C02-U063.

For a crystallographic root system in characteristic zero, the rational root
space `E_Q` is the `ℚ`-span of the roots.  The real root space is its scalar
extension `ℝ ⊗_ℚ E_Q`, with each root included as the pure tensor `1 ⊗ α`.

Mathlib already supplies the exact rational root pairing via
`RootPairing.restrictScalarsRat`.  The source statements identifying the
dimension and proving rationality and positive definiteness of the induced
form are result clauses and remain outside Sweep III.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

open Set Submodule

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {K : Type u₂} {M : Type u₃} {N : Type u₄}
  [Field K] [CharZero K] [AddCommGroup M] [AddCommGroup N]
  [Module K M] [Module K N]

/-- Humphreys' rational root space `E_Q`: the `ℚ`-span of the roots. -/
abbrev RationalRootSpaceData (P : RootPairing ι K M N) : Type _ :=
  letI : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  P.rootSpan ℚ

/-- The proof-complete rational root pairing already supplied by Mathlib.
Its root-side ambient space is `RationalRootSpaceData P`. -/
abbrev rationalRootPairingData (P : RootPairing ι K M N)
    [P.IsRootSystem] [P.IsCrystallographic] :=
  P.restrictScalarsRat

/-- Humphreys' real scalar extension `E = ℝ ⊗_ℚ E_Q`. -/
abbrev RealRootSpaceData (P : RootPairing ι K M N) : Type _ :=
  TensorProduct ℚ ℝ (RationalRootSpaceData P)

/-- A root viewed in the real scalar extension by `α ↦ 1 ⊗ α`. -/
def rootInRealRootSpaceData (P : RootPairing ι K M N) (i : ι) :
    RealRootSpaceData P :=
  letI : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  (1 : ℝ) ⊗ₜ[ℚ] P.rootSpanMem ℚ i

end LeanCategories.Algebra
