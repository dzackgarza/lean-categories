/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Completion
public import LeanCategories.Lattices.Valued.IdealDual
public import LeanCategories.Lattices.Valued.MetricDual
public import LeanCategories.Lattices.Valued.ScaleAndEvenness

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

private instance primeTwoFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Completion of integral lattices over the dyadic integers. -/
noncomputable def completeIntegralAtTwo :
    IntegralLatticeCat ℤ ⥤ IntegralLatticeCat ℤ_[2] :=
  completeIntegralAtPrime 2

/-- Completion of finite integral lattices over the dyadic integers. -/
noncomputable def completeFiniteIntegralAtTwo :
    FiniteProjectiveLatticeCat ℤ ℤ ⥤
      FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  completeFiniteIntegralAtPrime 2

/-- Extension of integral lattices to the dyadic field. -/
noncomputable def extendIntegralToTwoAdicField :
    IntegralLatticeCat ℤ ⥤ IntegralLatticeCat ℚ_[2] :=
  extendIntegralToPadicField 2

/-- Extension of finite integral lattices to the dyadic field. -/
noncomputable def extendFiniteIntegralToTwoAdicField :
    FiniteProjectiveLatticeCat ℤ ℤ ⥤
      FiniteProjectiveLatticeCat ℚ_[2] ℚ_[2] :=
  extendFiniteIntegralToPadicField 2

/-- A unimodular dyadic lattice has type II when all norms lie in `2ℤ_[2]`. -/
def IsDyadicTypeII (L : IntegralLatticeCat ℤ_[2]) : Prop :=
  IsUnimodular ℤ_[2] L ∧ IsIEven L (Ideal.span {(2 : ℤ_[2])})

/-- A unimodular dyadic lattice has type I when it is not of type II. -/
def IsDyadicTypeI (L : IntegralLatticeCat ℤ_[2]) : Prop :=
  IsUnimodular ℤ_[2] L ∧ ¬IsIEven L (Ideal.span {(2 : ℤ_[2])})

end LeanCategories.Lattices.Valued
