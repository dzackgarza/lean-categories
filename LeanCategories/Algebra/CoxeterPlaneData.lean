/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Bipartite Coxeter elements and the Coxeter plane

Definition-level realization of the construction part of Humphreys
FC15-C03-U035 (§3.17, pp. 76--78).

For a tree Coxeter graph, Humphreys renumbers the simple roots so that
`K = I ⊔ J` and roots in each part are pairwise orthogonal.  He writes

`y = ∏_{i∈I} s_i`, `z = ∏_{j∈J} s_j`, `w = yz`.

If `ω_i` is the basis dual to the simple roots for the Coxeter form and
`(c_i)` is a strictly positive eigenvector of its Gram matrix, he sets

`λ = Σ_{i∈I} c_i ω_i`, `μ = Σ_{j∈J} c_j ω_j`

and defines the Coxeter plane to be `span_R{λ, μ}`.

Sweep III records exactly those choices by their intrinsic graphs.  The tree
bipartition theorem, existence of the positive Perron eigenvector and dual
basis, the involutivity of `y,z`, invariance of the plane, the reflection
description, and the rotation-angle/order computation are result content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

/-- Exact graph of the bipartite numbering used in §3.17.  The two lists are
disjoint, cover all simple indices, contain no repetitions, and distinct
indices in either list have Coxeter label `2`, hence commute. -/
def IsCoxeterBipartitionData {S : Type u}
    (M : CoxeterMatrix S) (p : List S × List S) : Prop :=
  p.1.Nodup ∧ p.2.Nodup ∧
    (∀ s : S, s ∈ p.1 ∨ s ∈ p.2) ∧
    (∀ s : S, s ∈ p.1 → s ∉ p.2) ∧
    p.1.Pairwise (fun s t => M s t = 2) ∧
    p.2.Pairwise (fun s t => M s t = 2)

/-- The chosen source bipartition/numbering.  For a tree Coxeter graph the
source proves that the exact graph is inhabited. -/
def coxeterBipartitionData {S : Type u}
    (M : CoxeterMatrix S) : List S × List S :=
  Classical.epsilon (IsCoxeterBipartitionData M)

/-- Humphreys' `y`, the product of the commuting simple reflections in the
first bipartition class, in the chosen source ordering. -/
def coxeterBipartiteLeftElementData {S : Type u}
    (M : CoxeterMatrix S) : M.Group :=
  ((coxeterBipartitionData M).1.map M.simple).prod

/-- Humphreys' `z`, the product of the commuting simple reflections in the
second bipartition class. -/
def coxeterBipartiteRightElementData {S : Type u}
    (M : CoxeterMatrix S) : M.Group :=
  ((coxeterBipartitionData M).2.map M.simple).prod

/-- The bipartite Coxeter element `w = yz`. -/
def bipartiteCoxeterElementData {S : Type u}
    (M : CoxeterMatrix S) : M.Group :=
  coxeterBipartiteLeftElementData M * coxeterBipartiteRightElementData M

/-- The Gram matrix of the standard geometric Coxeter form in the simple-root
coordinates.  Mathlib's Coxeter convention uses `0` for the label `∞`. -/
def coxeterGeometricGramMatrixData {S : Type u}
    (M : CoxeterMatrix S) : Matrix S S ℝ :=
  fun i j =>
    if M i j = 0 then -1 else -Real.cos (Real.pi / (M i j : ℝ))

/-- Exact graph of the basis `ω_i` dual to the simple roots `α_i` for the
Coxeter form. -/
def IsCoxeterDualBasisData {S : Type u} [Fintype S] [DecidableEq S]
    (A : Matrix S S ℝ) (omega : S → (S → ℝ)) : Prop :=
  ∀ i j : S,
    Matrix.toBilin' A (omega i) (Pi.single j 1) = if i = j then 1 else 0

/-- The source dual basis selected by its exact pairing graph. -/
def coxeterDualBasisData {S : Type u} [Fintype S] [DecidableEq S]
    (A : Matrix S S ℝ) : S → (S → ℝ) :=
  Classical.epsilon (IsCoxeterDualBasisData A)

/-- Exact graph of the strictly positive Perron eigenpair used by Humphreys. -/
def IsPositiveCoxeterEigenpairData {S : Type u} [Fintype S]
    (A : Matrix S S ℝ) (p : ℝ × (S → ℝ)) : Prop :=
  0 < p.1 ∧ (∀ i : S, 0 < p.2 i) ∧ Matrix.mulVec A p.2 = p.1 • p.2

/-- The chosen positive eigenvalue/eigenvector pair of the Coxeter Gram
matrix.  The Perron--Frobenius result cited in §3.17 later proves inhabitation
of this exact graph. -/
def positiveCoxeterEigenpairData {S : Type u} [Fintype S]
    (A : Matrix S S ℝ) : ℝ × (S → ℝ) :=
  Classical.epsilon (IsPositiveCoxeterEigenpairData A)

/-- Humphreys' vector `λ = Σ_{i∈I} c_i ω_i`. -/
def coxeterPlaneLeftVectorData {S : Type u} [Fintype S] [DecidableEq S]
    (M : CoxeterMatrix S) : S → ℝ :=
  let A := coxeterGeometricGramMatrixData M
  let c := (positiveCoxeterEigenpairData A).2
  let omega := coxeterDualBasisData A
  (((coxeterBipartitionData M).1.map fun i => c i • omega i).sum)

/-- Humphreys' vector `μ = Σ_{j∈J} c_j ω_j`. -/
def coxeterPlaneRightVectorData {S : Type u} [Fintype S] [DecidableEq S]
    (M : CoxeterMatrix S) : S → ℝ :=
  let A := coxeterGeometricGramMatrixData M
  let c := (positiveCoxeterEigenpairData A).2
  let omega := coxeterDualBasisData A
  (((coxeterBipartitionData M).2.map fun j => c j • omega j).sum)

/-- The Coxeter plane `P = span_R{λ, μ}` from §3.17. -/
def coxeterPlaneData {S : Type u} [Fintype S] [DecidableEq S]
    (M : CoxeterMatrix S) : Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ
    ({coxeterPlaneLeftVectorData M, coxeterPlaneRightVectorData M} : Set (S → ℝ))

end LeanCategories.Algebra
