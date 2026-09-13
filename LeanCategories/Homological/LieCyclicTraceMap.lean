/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CyclicCoinvariantComplex
public import LeanCategories.Homological.HochschildComplex
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Loday--Quillen trace map on Lie chains

Weibel, *An Introduction to Homological Algebra* (1994), §9.10,
pp. 362--368 (FC05-C09-U154).

For `x₀,…,xₚ ∈ gl_m(R)`, the degree-`p` map

`λ : Λ^{p+1} gl_m(R) → C_p^λ(M_m(R))`

sends `x₀ ∧ ... ∧ xₚ` to the class of the signed alternating sum obtained by
fixing `x₀` and permuting the remaining `p` factors.  Lemma 9.10.1 proves that
these degreewise maps form a chain map and then passes to homology; that
result-layer assertion is not included here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial
open scoped BigOperators TensorProduct

universe u v

variable (k : Type u) [CommRing k]
variable (R : Type u) [Ring R] [Algebra k R]
variable (ι : Type v) [Fintype ι] [DecidableEq ι]

abbrev MatrixAlgebra := Matrix ι ι R

/-- A cyclic-module realization of the standard Hochschild chains of the
matrix algebra. -/
structure MatrixHochschildCyclicRealization where
  cyclic : CyclicObject (C := ModuleCat.{max u v} k)
  degreeIso : ∀ n : ℕ,
    cyclic.obj.obj (op ⦋n⦌) ≅
      ModuleCat.of k
        (HochschildChainDegree (k := k) (R := MatrixAlgebra R ι)
          (M := MatrixAlgebra R ι) n)

/-- The signed alternating Hochschild chain occurring in Weibel's formula for
`λ(x₀∧⋯∧xₚ)`. -/
def lieCyclicLambdaRaw (p : ℕ) (x : Fin (p + 1) → MatrixAlgebra R ι) :
    HochschildChainDegree (k := k) (R := MatrixAlgebra R ι)
      (M := MatrixAlgebra R ι) p := by
  classical
  exact ∑ σ : Equiv.Perm (Fin p),
    ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      hochschildChainPure (k := k) (R := MatrixAlgebra R ι)
        (M := MatrixAlgebra R ι) (x 0)
        (fun j => x (σ j).succ)

/-- The class of Weibel's alternating sum in the cyclic coinvariant quotient
`C_p^λ(M_m(R))`. -/
def lieCyclicLambdaPure
    (Z : MatrixHochschildCyclicRealization k R ι)
    (p : ℕ) (x : Fin (p + 1) → MatrixAlgebra R ι) :
    cyclicCoinvariantDegree k Z.cyclic p :=
  cyclicCoinvariantQuotient k Z.cyclic p
    ((Z.degreeIso p).inv (lieCyclicLambdaRaw k R ι p x))

/-- A realization of the degree-`p` Loday--Quillen map
`Λ^{p+1} gl_m(R) → C_p^λ(M_m(R))`.

The pure-wedge field is precisely the construction in Weibel §9.10.  Chain
compatibility and the induced map on homology are Lemma 9.10.1.

Source: Weibel, §9.10, pp. 362--368 (FC05-C09-U154). -/
structure LieCyclicLambdaRealization
    (Z : MatrixHochschildCyclicRealization k R ι) (p : ℕ) where
  map : ModuleCat.of k (⋀[k]^(p + 1) (MatrixAlgebra R ι)) ⟶
    cyclicCoinvariantDegree k Z.cyclic p
  map_pure : ∀ x : Fin (p + 1) → MatrixAlgebra R ι,
    map (exteriorPower.ιMulti k (p + 1) x) =
      lieCyclicLambdaPure k R ι Z p x

end LeanCategories.Homological
