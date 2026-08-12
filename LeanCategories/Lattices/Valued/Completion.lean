/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChange
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open CategoryTheory
open IsDedekindDomain

namespace LeanCategories.Lattices.Valued

universe u

section HeightOne

variable (R K : Type u)
variable [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Integral lattice completion at a height-one place. -/
noncomputable def completeIntegralAtHeightOne
    (v : HeightOneSpectrum R) :
    IntegralLatticeCat R ⥤ IntegralLatticeCat (v.adicCompletionIntegers K) :=
  baseChangeIntegral R (v.adicCompletionIntegers K)

/-- Finite projective integral lattice completion at a height-one place. -/
noncomputable def completeFiniteIntegralAtHeightOne
    (v : HeightOneSpectrum R) :
    FiniteProjectiveLatticeCat R R ⥤
      FiniteProjectiveLatticeCat
        (v.adicCompletionIntegers K) (v.adicCompletionIntegers K) :=
  baseChangeFiniteIntegral R (v.adicCompletionIntegers K)

/-- Integral lattice extension to the completed fraction field at a height-one place. -/
noncomputable def extendIntegralToHeightOneField
    (v : HeightOneSpectrum R) :
    IntegralLatticeCat R ⥤ IntegralLatticeCat (v.adicCompletion K) :=
  baseChangeIntegral R (v.adicCompletion K)

/-- Finite projective integral lattice extension to a completed fraction field. -/
noncomputable def extendFiniteIntegralToHeightOneField
    (v : HeightOneSpectrum R) :
    FiniteProjectiveLatticeCat R R ⥤
      FiniteProjectiveLatticeCat (v.adicCompletion K) (v.adicCompletion K) :=
  baseChangeFiniteIntegral R (v.adicCompletion K)

end HeightOne

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
