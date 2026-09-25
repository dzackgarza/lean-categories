/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.StandardBorelData

/-!
# One-dimensional standard-Borel action data

Humphreys FC14-C06-U009 writes the standard Borel as `B = H ⊕ N⁺` and
defines the one-dimensional weight-`λ` module by

`(h + n) · c = λ(h)c`.

Sweep III records that displayed action formula on the already-available
Cartan/positive-nilradical presentation.  It does not manufacture a
`LieModule` instance: proving that the formula is independent of a
decomposition and satisfies the Lie-module laws uses the directness/closure
and bracket facts for the standard Borel, which are result-layer statements.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v w

variable {I : Type u} {K : Type v} {L : Type w}
variable [Finite I] [Field K] [LieRing L] [LieAlgebra K L]
variable {H : LieSubalgebra K L}

/-- The underlying one-dimensional carrier of Humphreys' `D_λ`. -/
abbrev OneDimensionalBorelCarrierData := K

/-- The displayed action formula on an explicit `h + n` presentation of a
standard-Borel element.  The positive-nilradical coordinate acts trivially. -/
def oneDimensionalBorelPresentedActionData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H)
    (h : H) (_n : standardPositiveNilradical b) (c : K) : K :=
  lam h * c

/-- Graph relation for the source action on an ambient element `x : L`.

Keeping this relational avoids choosing a decomposition `x = h + n` before
the direct-sum result for the standard Borel has been established. -/
def IsOneDimensionalBorelActionData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H)
    (x : L) (c y : K) : Prop :=
  ∃ h : H, ∃ n : standardPositiveNilradical b,
    (h : L) + (n : L) = x ∧
      y = oneDimensionalBorelPresentedActionData b lam h n c

/-- Proof-free presentation of Humphreys' one-dimensional Borel module.

The carrier is the one-dimensional vector space `K`, and `actionGraph`
records exactly the source action relation on ambient Borel elements. The
result layer proves that the graph is functional on the standard Borel and
satisfies the Lie-module laws. -/
structure OneDimensionalBorelModulePresentationData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H) where
  actionGraph : L → K → K → Prop

/-- The source-prescribed presentation of `D_λ`. -/
def oneDimensionalBorelModulePresentationData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H) :
    OneDimensionalBorelModulePresentationData b lam where
  actionGraph := IsOneDimensionalBorelActionData b lam

end LeanCategories.Algebra
