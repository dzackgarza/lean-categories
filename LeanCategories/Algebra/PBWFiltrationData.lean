/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

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

open scoped DirectSum TensorProduct

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

/-- Exact representative graph for multiplication of homogeneous PBW
associated-graded pieces.

The witness in degree `i+j` is required to be the product of representatives
in `U(L)`.  The proposition does not prove that such a witness exists for
every pair or that its quotient class is independent of the chosen
representatives.  Those are precisely filtration-multiplicativity and quotient
descent results. -/
def IsPBWGradedPieceMulData {i j : ℕ}
    (x : PBWGradedPieceData R L i)
    (y : PBWGradedPieceData R L j)
    (z : PBWGradedPieceData R L (i + j)) : Prop :=
  ∃ (u : ↥(pbwFiltrationData R L i))
      (v : ↥(pbwFiltrationData R L j))
      (w : ↥(pbwFiltrationData R L (i + j))),
    Submodule.Quotient.mk u = x ∧
    Submodule.Quotient.mk v = y ∧
    Submodule.Quotient.mk w = z ∧
    w.1 = u.1 * v.1

/-- Exact graph sending a homogeneous tensor of degree `n` to its PBW
symbol in `G^n`.

Membership of its enveloping-algebra image in `U_n` is carried by the
existential witness rather than proved during construction. -/
def IsPBWTensorPowerSymbolData (n : ℕ)
    (t : ⨂[R]^n L)
    (g : PBWGradedPieceData R L n) : Prop :=
  ∃ u : ↥(pbwFiltrationData R L n),
    u.1 =
      UniversalEnvelopingAlgebra.mkAlgHom R L
        (TensorPower.toTensorAlgebra t) ∧
    Submodule.Quotient.mk u = g

/-- Exact componentwise graph of the canonical tensor-algebra symbol map into
the PBW associated-graded carrier.

The tensor algebra is decomposed canonically into tensor powers.  No proof is
made that the resulting relation is functional. -/
def IsPBWTensorAssociatedGradedData
    (t : TensorAlgebra R L)
    (g : PBWAssociatedGradedCarrierData R L) : Prop :=
  ∀ n : ℕ,
    IsPBWTensorPowerSymbolData R L n
      ((TensorAlgebra.toDirectSum t) n) (g n)

/-- Exact graph of Humphreys' induced map
`S(L) → gr U(L)`.

A symmetric-algebra element is related to a graded element when some tensor
representative maps to the former under the canonical quotient and has the
latter as its PBW symbol.  The theorem that commutators lower filtration is
what later proves independence of the tensor representative, hence
functionality and algebra-map descent. -/
def IsPBWSymmetricAssociatedGradedData
    (s : SymmetricAlgebra R L)
    (g : PBWAssociatedGradedCarrierData R L) : Prop :=
  ∃ t : TensorAlgebra R L,
    SymmetricAlgebra.algHom R L t = s ∧
    IsPBWTensorAssociatedGradedData R L t g

end LeanCategories.Algebra
