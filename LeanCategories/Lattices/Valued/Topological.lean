/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Topological realizations of integral lattices

An abstract finite projective `ℤ`-lattice becomes a topological lattice after a real realization is
chosen. A basis identifies its carrier with the integral span of a real basis. Mathlib proves that
this span is discrete and spans the ambient real vector space.
-/

@[expose] public section

noncomputable section

open Submodule

namespace LeanCategories.Lattices.Valued

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteProjectiveLatticeCat

/-- The integral realization determined by an integral basis and a real basis. -/
def realBasisMap (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) :
    L.obj.obj.carrier →ₗ[ℤ] E :=
  b.constr ℤ c

@[simp]
theorem realBasisMap_apply_basis (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) (i : I) :
    L.realBasisMap b c (b i) = c i :=
  b.constr_basis ℤ c i

/-- The image of an integral lattice in a basis-compatible real realization. -/
def realLatticeImage (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) : Submodule ℤ E :=
  LinearMap.range (L.realBasisMap b c)

/-- The realized carrier is exactly the integral span of the chosen real basis. -/
theorem realLatticeImage_eq_span (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) :
    L.realLatticeImage b c = span ℤ (Set.range c) := by
  exact b.constr_range ℤ

/-- The realized integral carrier has the discrete topology inherited from its real basis. -/
noncomputable instance realLatticeImageDiscreteTopology
    (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) :
    DiscreteTopology (L.realLatticeImage b c) := by
  rw [realLatticeImage_eq_span L b c]
  infer_instance

/-- A basis-compatible real realization is a topological `ℤ`-lattice. -/
instance realLatticeImageIsZLattice (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) :
    IsZLattice ℝ (L.realLatticeImage b c) where
  span_top := by
    rw [realLatticeImage_eq_span L b c]
    exact ZSpan.span_top c

section Covolume

variable [MeasurableSpace E] [BorelSpace E]

/-- The basis parallelepiped of a real realization. -/
def realFundamentalDomain (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (_b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) : Set E :=
  ZSpan.fundamentalDomain c

/-- The basis parallelepiped is an additive fundamental domain for the realized lattice. -/
theorem realFundamentalDomain_isAddFundamentalDomain
    (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (μ : MeasureTheory.Measure E) :
    MeasureTheory.IsAddFundamentalDomain
      (L.realLatticeImage b c) (L.realFundamentalDomain b c) μ := by
  rw [realLatticeImage_eq_span L b c]
  exact ZSpan.isAddFundamentalDomain c μ

variable [FiniteDimensional ℝ E]

/-- The covolume of an algebraic lattice in a basis-compatible real realization. -/
noncomputable def realLatticeCovolume (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (μ : MeasureTheory.Measure E) : ℝ :=
  ZLattice.covolume (L.realLatticeImage b c) μ

/-- A realized full lattice has positive covolume for every additive Haar measure. -/
theorem realLatticeCovolume_pos (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] :
    0 < L.realLatticeCovolume b c μ :=
  ZLattice.covolume_pos (L.realLatticeImage b c) μ

/-- Covolume is the measure of the basis parallelepiped. -/
theorem realLatticeCovolume_eq_measureReal_fundamentalDomain
    (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] :
    L.realLatticeCovolume b c μ = μ.real (L.realFundamentalDomain b c) :=
  ZLattice.covolume_eq_measure_fundamentalDomain
    (L.realLatticeImage b c) μ
    (L.realFundamentalDomain_isAddFundamentalDomain b c μ)

omit [BorelSpace E] in
/-- A realized lattice has a finite-measure fundamental domain. -/
theorem measure_realFundamentalDomain_ne_top
    (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] :
    μ (L.realFundamentalDomain b c) ≠ ⊤ :=
  ne_of_lt <| Bornology.IsBounded.measure_lt_top
    (ZSpan.fundamentalDomain_isBounded c)

end Covolume

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
