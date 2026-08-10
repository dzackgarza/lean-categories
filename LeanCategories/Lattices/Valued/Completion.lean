/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChange
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

universe u

/-- Extension to the `p`-adic integers preserves exact linear sequences. -/
theorem completeAtPrime_exact
    (p : ℕ) [Fact p.Prime]
    {M N O : Type u}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module ℤ M] [Module ℤ N] [Module ℤ O]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] O)
    (h : Function.Exact f g) :
    Function.Exact (LinearMap.baseChange ℤ_[p] f)
      (LinearMap.baseChange ℤ_[p] g) :=
  baseChange_exact ℤ ℤ_[p] f g h

/-- Extension to the `p`-adic field preserves exact linear sequences. -/
theorem extendToPadicField_exact
    (p : ℕ) [Fact p.Prime]
    {M N O : Type u}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module ℤ M] [Module ℤ N] [Module ℤ O]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] O)
    (h : Function.Exact f g) :
    Function.Exact (LinearMap.baseChange ℚ_[p] f)
      (LinearMap.baseChange ℚ_[p] g) :=
  baseChange_exact ℤ ℚ_[p] f g h

/-- Integral lattices completed over the `p`-adic integers. -/
noncomputable def completeIntegralAtPrime
    (p : ℕ) [Fact p.Prime] :
    IntegralLatticeCat ℤ ⥤ IntegralLatticeCat ℤ_[p] :=
  baseChangeIntegral ℤ ℤ_[p]

/-- Finite projective integral lattices completed over the `p`-adic integers. -/
noncomputable def completeFiniteIntegralAtPrime
    (p : ℕ) [Fact p.Prime] :
    FiniteProjectiveLatticeCat ℤ ℤ ⥤
      FiniteProjectiveLatticeCat ℤ_[p] ℤ_[p] :=
  baseChangeFiniteIntegral ℤ ℤ_[p]

/-- Integral lattices extended to the `p`-adic local field. -/
noncomputable def extendIntegralToPadicField
    (p : ℕ) [Fact p.Prime] :
    IntegralLatticeCat ℤ ⥤ IntegralLatticeCat ℚ_[p] :=
  baseChangeIntegral ℤ ℚ_[p]

/-- Finite projective integral lattices extended to the `p`-adic local field. -/
noncomputable def extendFiniteIntegralToPadicField
    (p : ℕ) [Fact p.Prime] :
    FiniteProjectiveLatticeCat ℤ ℤ ⥤
      FiniteProjectiveLatticeCat ℚ_[p] ℚ_[p] :=
  baseChangeFiniteIntegral ℤ ℚ_[p]

end LeanCategories.Lattices.Valued
