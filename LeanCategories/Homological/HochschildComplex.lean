/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SimplicialChainComplexes
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Bimodule
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Standard Hochschild simplicial and cosimplicial modules

Weibel, *An Introduction to Homological Algebra* (1994), Definition/Construction 9.1.1,
pp. 300--305 (FC05-C09-U002).

For a `k`-algebra `R` and an `R`-bimodule `M`, Weibel's degree-`n` Hochschild
chains are `M ⊗_k R^{⊗ n}`.  The faces multiply adjacent factors, with the
outer faces using the right and left actions on `M`; degeneracies insert `1`.
The dual cosimplicial object has degree `Hom_k(R^{⊗ n}, M)` with the dual
coface/codegeneracy formulas.

As with the cotriple construction, this Definitions-sweep owner records an actual
simplicial/cosimplicial realization together with the exact pure-tensor formulas.
The verification of all simplicial identities is result-level work.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial
open scoped TensorProduct

universe u v w

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

/-- The degree-`n` standard Hochschild chain module `M ⊗_k R^{⊗ n}`. -/
abbrev HochschildChainDegree (n : ℕ) : Type max u v w :=
  M ⊗[k] TensorPower k n R

/-- A pure Hochschild chain `m ⊗ r₁ ⊗ ... ⊗ rₙ`. -/
def hochschildChainPure {n : ℕ} (m : M) (a : Fin n → R) :
    HochschildChainDegree (k := k) (R := R) (M := M) n :=
  m ⊗ₜ[k] PiTensorProduct.tprod k a

/-- Delete the first algebra factor. -/
def hochschildTail {n : ℕ} (a : Fin (n + 1) → R) : Fin n → R :=
  fun j => a j.succ

/-- Delete the last algebra factor. -/
def hochschildInit {n : ℕ} (a : Fin (n + 1) → R) : Fin n → R :=
  fun j => a j.castSucc

/-- For an interior Hochschild face, multiply the two factors adjacent to the
face and delete the second of them. -/
def hochschildMulAdjacent {n : ℕ} (a : Fin (n + 1) → R)
    (i : Fin (n + 2)) (h0 : i ≠ 0) (hlast : i ≠ Fin.last (n + 1)) :
    Fin n → R :=
  let q : Fin (n + 1) := i.castPred hlast
  let p : Fin (n + 1) := i.pred h0
  fun j =>
    if q.succAbove j = p then a p * a q else a (q.succAbove j)

/-- The pure-tensor formula for the `i`th Hochschild face. -/
def hochschildFaceData {n : ℕ} (m : M) (a : Fin (n + 1) → R)
    (i : Fin (n + 2)) : M × (Fin n → R) := by
  classical
  by_cases h0 : i = 0
  · exact ((MulOpposite.op (a 0) : Rᵐᵒᵖ) • m, hochschildTail R a)
  by_cases hlast : i = Fin.last (n + 1)
  · exact (a (Fin.last n) • m, hochschildInit R a)
  · exact (m, hochschildMulAdjacent R a i h0 hlast)

/-- The pure-tensor formula for the `i`th Hochschild degeneracy: insert the unit. -/
def hochschildDegeneracyData {n : ℕ} (m : M) (a : Fin n → R)
    (i : Fin (n + 1)) : M × (Fin (n + 1) → R) :=
  (m, Fin.insertNth i 1 a)

/-- A simplicial realization of the standard Hochschild chain formulas. -/
structure HochschildSimplicialRealization where
  /-- The realized simplicial `k`-module. -/
  obj : SimplicialObject (ModuleCat k)
  /-- Identification of degree `n` with `M ⊗_k R^{⊗n}`. -/
  degreeIso : ∀ n : ℕ,
    obj.obj (op ⦋n⦌) ≅
      ModuleCat.of k (HochschildChainDegree (k := k) (R := R) (M := M) n)
  /-- The face maps have Weibel's pure-tensor formulas. -/
  face_pure : ∀ (n : ℕ) (i : Fin (n + 2)) (m : M) (a : Fin (n + 1) → R),
    (degreeIso n).hom
        (obj.δ i ((degreeIso (n + 1)).inv
          (hochschildChainPure (k := k) (R := R) (M := M) m a))) =
      hochschildChainPure (k := k) (R := R) (M := M)
        (hochschildFaceData R M m a i).1 (hochschildFaceData R M m a i).2
  /-- The degeneracy maps insert the algebra unit. -/
  degeneracy_pure : ∀ (n : ℕ) (i : Fin (n + 1)) (m : M) (a : Fin n → R),
    (degreeIso (n + 1)).hom
        (obj.σ i ((degreeIso n).inv
          (hochschildChainPure (k := k) (R := R) (M := M) m a))) =
      hochschildChainPure (k := k) (R := R) (M := M)
        (hochschildDegeneracyData R M m a i).1 (hochschildDegeneracyData R M m a i).2

/-- Hochschild homology of a standard simplicial realization. -/
noncomputable def hochschildHomology
    (S : HochschildSimplicialRealization k R M) (n : ℕ) : ModuleCat k :=
  simplicialHomotopyObject S.obj n

/-- The degree-`n` Hochschild cochain module `Hom_k(R^{⊗n},M)`. -/
abbrev HochschildCochainDegree (n : ℕ) : Type max u v w :=
  TensorPower k n R →ₗ[k] M

/-- Evaluate a Hochschild cochain on a pure algebra tensor. -/
def hochschildCochainEval {n : ℕ}
    (f : HochschildCochainDegree (k := k) (R := R) (M := M) n)
    (a : Fin n → R) : M :=
  f (PiTensorProduct.tprod k a)

/-- The value of the `i`th Hochschild coface on a pure tensor. -/
def hochschildCofaceValue {n : ℕ}
    (f : HochschildCochainDegree (k := k) (R := R) (M := M) n)
    (i : Fin (n + 2)) (a : Fin (n + 1) → R) : M := by
  classical
  by_cases h0 : i = 0
  · exact a 0 • hochschildCochainEval (k := k) (R := R) (M := M) f (hochschildTail R a)
  by_cases hlast : i = Fin.last (n + 1)
  · exact (MulOpposite.op (a (Fin.last n)) : Rᵐᵒᵖ) •
      hochschildCochainEval (k := k) (R := R) (M := M) f (hochschildInit R a)
  · exact hochschildCochainEval (k := k) (R := R) (M := M) f
      (hochschildMulAdjacent R a i h0 hlast)

/-- The value of the `i`th Hochschild codegeneracy on a pure tensor. -/
def hochschildCodegeneracyValue {n : ℕ}
    (f : HochschildCochainDegree (k := k) (R := R) (M := M) (n + 1))
    (i : Fin (n + 1)) (a : Fin n → R) : M :=
  hochschildCochainEval (k := k) (R := R) (M := M) f (Fin.insertNth i 1 a)

/-- A cosimplicial realization of the standard Hochschild cochain formulas. -/
structure HochschildCosimplicialRealization where
  /-- The realized cosimplicial `k`-module. -/
  obj : CosimplicialObject (ModuleCat k)
  /-- Identification of degree `n` with `Hom_k(R^{⊗n},M)`. -/
  degreeIso : ∀ n : ℕ,
    obj.obj ⦋n⦌ ≅
      ModuleCat.of k (HochschildCochainDegree (k := k) (R := R) (M := M) n)
  /-- The cofaces have the standard Hochschild formulas on pure tensors. -/
  coface_eval : ∀ (n : ℕ) (i : Fin (n + 2))
      (f : HochschildCochainDegree (k := k) (R := R) (M := M) n)
      (a : Fin (n + 1) → R),
    hochschildCochainEval (k := k) (R := R) (M := M)
        ((degreeIso (n + 1)).hom (obj.δ i ((degreeIso n).inv f))) a =
      hochschildCofaceValue (k := k) (R := R) (M := M) f i a
  /-- The codegeneracies insert the algebra unit in the arguments. -/
  codegeneracy_eval : ∀ (n : ℕ) (i : Fin (n + 1))
      (f : HochschildCochainDegree (k := k) (R := R) (M := M) (n + 1))
      (a : Fin n → R),
    hochschildCochainEval (k := k) (R := R) (M := M)
        ((degreeIso n).hom (obj.σ i ((degreeIso (n + 1)).inv f))) a =
      hochschildCodegeneracyValue (k := k) (R := R) (M := M) f i a

/-- Hochschild cohomology of a standard cosimplicial realization. -/
noncomputable def hochschildCohomology
    (S : HochschildCosimplicialRealization k R M) (n : ℕ) : ModuleCat k :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).obj
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj S.obj)

end LeanCategories.Homological
