/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Finite-dimensional separable algebras

Weibel, *An Introduction to Homological Algebra*, §9.2, pp. 306--310
(FC05-C09-U020).

Weibel calls a finite-dimensional semisimple `k`-algebra `R` separable when every scalar extension
`R ⊗[k] l` along a field extension `l/k` is again semisimple.  The definition below records this
criterion directly, using Mathlib's `FiniteDimensional` and `IsSemisimpleRing` predicates.
-/

@[expose] public section

open scoped TensorProduct

namespace LeanCategories.Algebra

universe u v

/-- A finite-dimensional separable `k`-algebra in the sense of Weibel §9.2: `R` is
finite-dimensional and semisimple over `k`, and every scalar extension to a field extension of `k`
in the ambient universe remains semisimple.

Source: Weibel, §9.2, pp. 306--310 (FC05-C09-U020). -/
def IsFiniteDimensionalSeparableAlgebra
    (k : Type u) (R : Type v) [Field k] [Ring R] [Algebra k R] : Prop :=
  FiniteDimensional k R ∧ IsSemisimpleRing R ∧
    ∀ (l : Type u) [Field l] [Algebra k l], IsSemisimpleRing (R ⊗[k] l)


/-- A field extension is separably generated when there is a transcendence basis over which the
remaining algebraic extension is separable.

This is the definition later added to Mathlib as `Algebra.IsSeparablyGenerated`; the project copy
keeps FC05 usable at the pinned Mathlib revision where that declaration is not yet present.

Source: Weibel, §9.3, pp. 311--318 (FC05-C09-U038); reference implementation:
Mathlib `5aedf732b6987e8c26ab3c9ebc855314f82b045f`,
`Mathlib/FieldTheory/TranscendentalSeparable.lean`. -/
class IsSeparablyGenerated (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] : Prop where
  /-- A transcendence basis after adjoining which `K` is separable. -/
  isSeparable : ∃ (s : Set K), IsTranscendenceBasis k ((↑) : s → K) ∧
    Algebra.IsSeparable (IntermediateField.adjoin k s) K

/-- A field extension is separable in Weibel's transcendental sense when each finitely generated
intermediate extension is separably generated.

Source: Weibel, §9.3, pp. 311--318 (FC05-C09-U041); reference implementation:
Mathlib `5aedf732b6987e8c26ab3c9ebc855314f82b045f`,
`Mathlib/FieldTheory/TranscendentalSeparable.lean`. -/
class IsTranscendentalSeparable (k : Type u) (K : Type v) [Field k] [Field K]
    [Algebra k K] : Prop where
  /-- Every finitely generated intermediate field is separably generated. -/
  forall_isSeparablyGenerated : ∀ (L : IntermediateField k K),
    Algebra.EssFiniteType k L → IsSeparablyGenerated k L

end LeanCategories.Algebra
