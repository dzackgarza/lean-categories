/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# The Chevalley--Eilenberg complex

Weibel, *An Introduction to Homological Algebra* (1994), §7.7, pp. 238--241
(FC05-C07-U047, FC05-C07-U048).

For a Lie algebra `L` over a commutative ring `k`, put
`U = U(L)` and `V_p(L) = U ⊗_k Λ^p L`.  Mathlib already owns these degree
objects and the enveloping-algebra augmentation.  This file records a
source-faithful realization interface for the Chevalley--Eilenberg differential
on pure wedges.

The fact that the resulting augmented complex is a projective resolution under
Weibel's freeness hypotheses is Theorem 7.7.2 and is intentionally not asserted
here.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory
open scoped BigOperators TensorProduct

universe u

variable (k L : Type u) [CommRing k] [LieRing L] [LieAlgebra k L]

/-- The pure wedge `x₀ ∧ ⋯ ∧ x_{p-1}` as an element of `Λ^p L`. -/
def chevalleyEilenbergWedge {p : ℕ} (x : Fin p → L) :
    ⋀[k]^p L :=
  ⟨ExteriorAlgebra.ιMulti k p x,
    ExteriorAlgebra.ιMulti_range k p ⟨x, rfl⟩⟩

/-- A pure tensor `u ⊗ (x₀ ∧ ⋯ ∧ x_{p-1})` in `V_p(L)`. -/
def chevalleyEilenbergPure {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin p → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  u ⊗ₜ[k] chevalleyEilenbergWedge k L x

/-- Delete the `i`th factor from a wedge tuple. -/
def chevalleyEilenbergOmit {p : ℕ} (x : Fin (p + 1) → L)
    (i : Fin (p + 1)) : Fin p → L :=
  i.removeNth x

/-- Replace the `i`th surviving factor by `[x_i,x_j]` after deleting the
`j`th factor, for `i < j`.

Putting the bracket in the original `i`th position changes the standard
front-loaded bracket sign `(-1)^(i+j)` into `(-1)^j` in zero-based indexing. -/
def chevalleyEilenbergBracketTuple {p : ℕ} (x : Fin (p + 1) → L)
    (i j : Fin (p + 1)) (hij : i < j) : Fin p → L :=
  let i' : Fin p :=
    ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
  Function.update (j.removeNth x) i' ⁅x i, x j⁆

/-- The action part of the Chevalley--Eilenberg boundary on a pure wedge. -/
noncomputable def chevalleyEilenbergActionBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  ∑ i : Fin (p + 1),
    ((-1 : ℤ) ^ i.val) •
      chevalleyEilenbergPure k L
        (u * UniversalEnvelopingAlgebra.ι k (x i))
        (chevalleyEilenbergOmit L x i)

/-- The bracket part of the Chevalley--Eilenberg boundary on a pure wedge.
The bracket is kept in the original `i`th position, hence the equivalent
zero-based sign `(-1)^j`. -/
noncomputable def chevalleyEilenbergBracketBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
    if hij : i < j then
      ((-1 : ℤ) ^ j.val) •
        chevalleyEilenbergPure k L u
          (chevalleyEilenbergBracketTuple L x i j hij)
    else 0

/-- Weibel's full Chevalley--Eilenberg boundary formula on a pure wedge. -/
noncomputable def chevalleyEilenbergBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  chevalleyEilenbergActionBoundary k L u x +
    chevalleyEilenbergBracketBoundary k L u x

/-- A source-faithful realization of the Chevalley--Eilenberg standard complex.
The chain-complex laws, including `d²=0`, are part of `complex`; this structure
only fixes the degree objects and Weibel's differential formula on the spanning
pure wedges. -/
structure ChevalleyEilenbergRealization where
  /-- The realized standard complex. -/
  complex : ChainComplex (ModuleCat (UniversalEnvelopingAlgebra k L)) ℕ
  /-- Degree `p` is `U(L) ⊗_k Λ^p L`. -/
  degreeIso : ∀ p : ℕ,
    complex.X p ≅ ModuleCat.of (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L))
  /-- The differential is the alternating action-and-bracket formula on pure wedges. -/
  differential_pure : ∀ (p : ℕ) (u : UniversalEnvelopingAlgebra k L)
      (x : Fin (p + 1) → L),
    (degreeIso p).hom
        (complex.d (p + 1) p
          ((degreeIso (p + 1)).inv (chevalleyEilenbergPure k L u x))) =
      chevalleyEilenbergBoundary k L u x

end LeanCategories.Homological
