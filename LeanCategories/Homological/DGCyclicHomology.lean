/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DGHochschildHomology
public import LeanCategories.Homological.TsyganBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Cyclic homology of differential graded algebras

Weibel, *An Introduction to Homological Algebra* (1994), §9.9 after
Definition 9.9.10, pp. 354--361 (FC05-C09-U150).

For a DG-algebra, the signed graded tensor powers form a cyclic object in the
category of chain complexes.  Applying Tsygan's construction and flattening
the resulting triple complex defines DG cyclic homology.  For nonnegatively
graded DG-algebras, the corresponding periodic product total complex defines
DG periodic cyclic homology.

The structures below package these source constructions after the graded sign
identities have been verified.  Those sign verifications are theorem-layer
work; the homology objects themselves are definition-layer data.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]
variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- A graded algebra is nonnegatively graded when all negative homogeneous
pieces vanish.  This is the positivity hypothesis used for periodic DG cyclic
homology in Weibel §9.9. -/
def IsNonnegativelyGraded : Prop :=
  ∀ q : ℤ, q < 0 → 𝒜 q = ⊥

/-- A realization of the signed cyclic object `Z(A,d)` attached to a
DG-algebra.  Simplicial degree `n` is the internal chain complex underlying
Hochschild degree `n` of the DG Hochschild bicomplex. -/
structure DGCyclicObjectRealization
    {D : DifferentialGradedAlgebra k A 𝒜}
    (H : DGHochschildDoubleComplexRealization k A 𝒜 D) where
  /-- The cyclic object in integer chain complexes. -/
  cyclic : CyclicObject (C := ChainComplex (ModuleCat.{max u v} k) ℤ)
  /-- Its degree `n` object is the internal chain complex of DG Hochschild
  degree `n`. -/
  degreeIso : ∀ n : ℕ,
    cyclic.obj.obj (op ⦋n⦌) ≅ H.bicomplex.X (n : ℤ)

/-- A realization of Tsygan's bicomplex for the DG cyclic object together
with its flattened direct-sum total complex. -/
structure DGCyclicTsyganRealization
    {D : DifferentialGradedAlgebra k A 𝒜}
    (H : DGHochschildDoubleComplexRealization k A 𝒜 D)
    (Z : DGCyclicObjectRealization k A 𝒜 H) where
  /-- Tsygan's bicomplex in the abelian category of integer chain complexes. -/
  tsygan : TsyganBicomplexRealization Z.cyclic
  /-- The direct-sum flattening of the Tsygan bicomplex together with the
  internal DG direction. -/
  totalComplex : ChainComplex (ModuleCat.{max u v} k) ℤ

/-- DG cyclic homology `HC_n^DG(A)`.

Source: Weibel, §9.9 after Definition 9.9.10, pp. 354--361
(FC05-C09-U150). -/
def dgCyclicHomology
    {D : DifferentialGradedAlgebra k A 𝒜}
    {H : DGHochschildDoubleComplexRealization k A 𝒜 D}
    {Z : DGCyclicObjectRealization k A 𝒜 H}
    (T : DGCyclicTsyganRealization k A 𝒜 H Z) (n : ℤ) : ModuleCat.{max u v} k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k) (ComplexShape.down ℤ) n).obj
    T.totalComplex

/-- Product-total realization used to define periodic cyclic homology of a
nonnegatively graded DG-algebra. -/
structure DGPeriodicCyclicRealization
    {D : DifferentialGradedAlgebra k A 𝒜}
    {H : DGHochschildDoubleComplexRealization k A 𝒜 D}
    {Z : DGCyclicObjectRealization k A 𝒜 H}
    (T : DGCyclicTsyganRealization k A 𝒜 H Z)
    (hpos : IsNonnegativelyGraded k A 𝒜) where
  /-- The flattened product total complex of the two-sided periodic extension. -/
  productTotalComplex : ChainComplex (ModuleCat.{max u v} k) ℤ

/-- DG periodic cyclic homology `HP_n^DG(A)` for a nonnegatively graded
DG-algebra.

Source: Weibel, §9.9 after Definition 9.9.10, pp. 354--361
(FC05-C09-U150). -/
def dgPeriodicCyclicHomology
    {D : DifferentialGradedAlgebra k A 𝒜}
    {H : DGHochschildDoubleComplexRealization k A 𝒜 D}
    {Z : DGCyclicObjectRealization k A 𝒜 H}
    {T : DGCyclicTsyganRealization k A 𝒜 H Z}
    {hpos : IsNonnegativelyGraded k A 𝒜}
    (P : DGPeriodicCyclicRealization k A 𝒜 T hpos) (n : ℤ) : ModuleCat.{max u v} k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k) (ComplexShape.down ℤ) n).obj
    P.productTotalComplex

end LeanCategories.Homological
