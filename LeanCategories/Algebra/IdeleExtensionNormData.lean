/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IdeleGroup
public import Mathlib.RingTheory.Norm.Defs

/-!
# Raw extension norm data on idèles

Definition-level realization of Neukirch FC09-C06-U021.

For a finite field extension, the local norm is the determinant of
multiplication.  Mathlib's `Algebra.norm` is exactly that monoid
homomorphism.  Neukirch then says that the local norms induce a norm
`I_L → I_K` on the idèle groups.

Constructing that global map through the restricted-product API requires the
preservation theorem proved in the checked ClassFieldTheory reference.  Sweep
III therefore reuses the determinant norm and records the induced global map as
raw data; multiplicativity and restricted-product preservation are result
content.
-/

@[expose] public noncomputable section

namespace LeanCategories

universe u v

/-- The determinant norm on units of a finite-dimensional field extension.

`Algebra.norm K` is definitionally the determinant of multiplication by the
given element, exactly as in Neukirch's local norm definition. -/
def finiteExtensionUnitNormData
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- Raw idèle norm map attached to a finite extension.

The map is stored without a homomorphism proof because establishing that the
componentwise determinant prescription preserves the restricted product is a
result-layer obligation. -/
structure IdeleExtensionNormData
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] where
  norm : IdeleGroup L → IdeleGroup K

/-- The assertion that raw idèle norm data are multiplicative.

This predicate records the source phrase “norm homomorphism” without asking
Sweep III to prove it for the restricted-product construction. -/
def IsIdeleExtensionNormHomData
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (D : IdeleExtensionNormData K L) : Prop :=
  D.norm 1 = 1 ∧
    ∀ a b : IdeleGroup L, D.norm (a * b) = D.norm a * D.norm b

end LeanCategories
