/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# PBW filtration carrier data

Humphreys FC14-C05-U008 filters the tensor algebra by word degree, sends that
filtration through the canonical quotient to the universal enveloping algebra,
and forms the successive quotients and their direct sum.

These carrier constructions are the proof-free part of the source unit.  They
are adapted from TauCetiProject/TauCeti at
504ca297404f040f84870b8a624fea1e0ec7e7b8 (Apache-2.0), especially
`Algebra/WordFiltration/Basic.lean` and
`Algebra/Lie/UniversalEnveloping/PBW/AssociatedGraded.lean`.

The multiplication on the quotient pieces is not constructed here: its
well-definedness requires proving that lower filtration steps absorb products.
Likewise, commutativity of the PBW associated graded and the induced
`SymmetricAlgebra R L → gr U(L)` require the theorem that commutators lower
PBW degree.  Those proposition-valued obligations are outside Sweep III.
-/

@[expose] public section

open scoped DirectSum

namespace LeanCategories.Algebra

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "T" => TensorAlgebra R L
local notation "U" => UniversalEnvelopingAlgebra R L

/-- Tensor words of degree at most `k`: the `k`-th power of the scalar
and degree-one generator submodule. -/
def tensorPBWFiltrationData (k : ℕ) : Submodule R T :=
  (1 ⊔ LinearMap.range (TensorAlgebra.ι R)) ^ k

/-- Humphreys' filtration `U_k = π(T_k)` on the universal enveloping
algebra, using Mathlib's canonical tensor-algebra quotient map `π`. -/
def pbwFiltrationData (k : ℕ) : Submodule R U :=
  Submodule.map (UniversalEnvelopingAlgebra.mkAlgHom R L).toLinearMap
    (tensorPBWFiltrationData R L k)

/-- The filtration step immediately below degree `k`, with zero denominator
in degree zero. -/
def pbwFiltrationPreviousData : ℕ → Submodule R U
  | 0 => ⊥
  | k + 1 => pbwFiltrationData R L k

/-- The copy of `U_{k-1}` inside the degree-`k` carrier, expressed as a
preimage so no monotonicity proof is needed to form the submodule. -/
abbrev pbwGradedLowerData (k : ℕ) :
    Submodule R ↥(pbwFiltrationData R L k) :=
  Submodule.comap (pbwFiltrationData R L k).subtype
    (pbwFiltrationPreviousData R L k)

/-- Humphreys' degree-`k` associated-graded carrier
`G^k = U_k / U_{k-1}`. -/
abbrev PBWGradedPieceData (k : ℕ) :=
  ↥(pbwFiltrationData R L k) ⧸ pbwGradedLowerData R L k

/-- The proof-free carrier of the PBW associated graded,
`G = ⨁_k U_k/U_{k-1}`.

No multiplication or algebra instance is asserted here. -/
abbrev PBWAssociatedGradedCarrierData :=
  ⨁ k : ℕ, PBWGradedPieceData R L k

end LeanCategories.Algebra
