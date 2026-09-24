/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CWSpectrum
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.SingularSet

/-!
# Geometric realization of chain complexes as CW spectra

Weibel, *An Introduction to Homological Algebra* (1994), Geometric
Realization 10.9.19, §10.9, pp. 407--416 (FC05-C10-U120).

For an unbounded chain complex of abelian groups, the `n`th spectrum level is
constructed by shifting the complex, taking its good nonnegative truncation,
applying inverse Dold--Kan, and geometrically realizing the resulting
simplicial abelian group.  These levels assemble into a CW spectrum, functorial
in the chain complex.

Sweep III records the canonical shifted/truncated Dold--Kan realization stages
and their functorial maps.  The truncated-cone argument which produces the
bonding maps, proves them cellular, and thereby upgrades the stages to a CW
prespectrum is result-layer content; the corresponding spectrification and
derived-category comparison remain downstream of that result.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- Forget the abelian-group structure of a simplicial abelian group. -/
def simplicialAbelianUnderlyingSSet
    (A : SimplicialObject AddCommGrpCat.{u}) : SSet.{u} :=
  A ⋙ forget AddCommGrpCat

/-- Inverse Dold--Kan applied to a nonnegative chain complex. -/
def doldKanSimplicialAbelian
    (K : ChainComplex AddCommGrpCat.{u} ℕ) :
    SimplicialObject AddCommGrpCat.{u} :=
  CategoryTheory.Abelian.DoldKan.Γ.obj K

/-- The ordinary geometric realization of the underlying simplicial set of
inverse Dold--Kan. -/
def doldKanGeometricTop
    (K : ChainComplex AddCommGrpCat.{u} ℕ) : TopCat.{u} :=
  SSet.toTop.obj
    (simplicialAbelianUnderlyingSSet (doldKanSimplicialAbelian K))

/-- The cochain presentation of Weibel's shift `C[-n]`.

The chain/cochain reindexing sends chain degree `i` to cochain degree `-i`.
Consequently the native cochain shift by `n` has chain degree `i` equal to
`C_{i-n}`.  The native shift also carries the factor `(-1)^n` on the
differential, so no separately supplied compatibility law is needed.

Source: Weibel, shift convention 1.2.8 and Geometric Realization 10.9.19
(FC05-C10-U120). -/
def chainComplexRealizationShift
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)).obj
    ((ChainComplex.cochainComplexEquivalence AddCommGrpCat.{u}).functor.obj C)

/-- The good nonnegative truncation `τ_{≥0}(C[-n])` used by Weibel.

After the chain/cochain reindexing, nonnegative chain degrees correspond to
nonpositive cochain degrees.  Mathlib's canonical `truncLE'` along
`embeddingDownNat` therefore replaces degree zero by the cycle object and
retains the positive chain degrees exactly as required.

Source: Weibel, Geometric Realization 10.9.19 (FC05-C10-U120). -/
noncomputable def chainComplexRealizationTruncation
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  (chainComplexRealizationShift C n).truncLE' ComplexShape.embeddingDownNat

/-- Inverse Dold--Kan applied to `τ_{≥0}(C[-n])`. -/
noncomputable def chainComplexRealizationSimplicialAbelian
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) :
    SimplicialObject AddCommGrpCat.{u} :=
  doldKanSimplicialAbelian (chainComplexRealizationTruncation C n)

/-- The underlying simplicial set of inverse Dold--Kan at realization stage
`n`. -/
noncomputable def chainComplexRealizationSSet
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) : SSet.{u} :=
  simplicialAbelianUnderlyingSSet (chainComplexRealizationSimplicialAbelian C n)

/-- The unbased geometric realization `|Γ(τ_{≥0}(C[-n]))|`. -/
noncomputable def chainComplexRealizationTop
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) : TopCat.{u} :=
  SSet.toTop.obj (chainComplexRealizationSSet C n)

/-- The point in a geometric realization represented by a chosen zero-simplex. -/
noncomputable def geometricRealizationVertex {X : SSet.{u}}
    (x : X.obj (op ⦋0⦌)) : (SSet.toTop.obj X) :=
  ((SSet.toTopSimplex.inv.app ⦋0⦌) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm x)) default

/-- The canonical basepoint of `|Γ(K)|`, represented by the zero zero-simplex
of the simplicial abelian group `Γ(K)`. -/
noncomputable def doldKanGeometricPoint
    (K : ChainComplex AddCommGrpCat.{u} ℕ) : doldKanGeometricTop K :=
  geometricRealizationVertex
    (X := simplicialAbelianUnderlyingSSet (doldKanSimplicialAbelian K))
    (0 : (doldKanSimplicialAbelian K).obj (op ⦋0⦌))

/-- The based geometric realization of inverse Dold--Kan. -/
noncomputable def doldKanGeometricBased
    (K : ChainComplex AddCommGrpCat.{u} ℕ) :
    LeanCategories.Topology.BasedTop.{u} :=
  Under.mk
    (TopCat.ofHom
      (ContinuousMap.const (TopCat.of PUnit) (doldKanGeometricPoint K)))

/-- Weibel's canonical raw level
`P(C)_n = |Γ(τ_{≥0}(C[-n]))|`, based at the zero simplex.

Source: Weibel, Geometric Realization 10.9.19 (FC05-C10-U120). -/
noncomputable def chainComplexGeometricLevel
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) :
    LeanCategories.Topology.BasedTop.{u} :=
  doldKanGeometricBased (chainComplexRealizationTruncation C n)

/-- The chain map on shifted cochain presentations induced by `f : C ⟶ D`. -/
def chainComplexRealizationShiftMap
    {C D : ChainComplex AddCommGrpCat.{u} ℤ} (f : C ⟶ D) (n : ℕ) :
    chainComplexRealizationShift C n ⟶ chainComplexRealizationShift D n :=
  (CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)).map
    ((ChainComplex.cochainComplexEquivalence AddCommGrpCat.{u}).functor.map f)

/-- The canonical map on good truncations induced by a chain map. -/
noncomputable def chainComplexRealizationTruncationMap
    {C D : ChainComplex AddCommGrpCat.{u} ℤ} (f : C ⟶ D) (n : ℕ) :
    chainComplexRealizationTruncation C n ⟶
      chainComplexRealizationTruncation D n :=
  HomologicalComplex.truncLE'Map (chainComplexRealizationShiftMap f n)
    ComplexShape.embeddingDownNat

/-- The induced map of simplicial sets on the `n`th realization stage. -/
noncomputable def chainComplexRealizationSSetMap
    {C D : ChainComplex AddCommGrpCat.{u} ℤ} (f : C ⟶ D) (n : ℕ) :
    chainComplexRealizationSSet C n ⟶ chainComplexRealizationSSet D n :=
  Functor.whiskerRight
    (CategoryTheory.Abelian.DoldKan.Γ.map
      (chainComplexRealizationTruncationMap f n))
    (forget AddCommGrpCat)

/-- The induced continuous map on the unbased geometric-realization stages. -/
noncomputable def chainComplexRealizationTopMap
    {C D : ChainComplex AddCommGrpCat.{u} ℤ} (f : C ⟶ D) (n : ℕ) :
    chainComplexRealizationTop C n ⟶ chainComplexRealizationTop D n :=
  SSet.toTop.map (chainComplexRealizationSSetMap f n)

/-- Result-layer bonding data singled out by Weibel's truncated-cone argument.

The canonical level objects above are definition data.  The source next proves,
using the truncated cone sequence, that there are cellular adjoint maps
`ΣP(C)_n ⟶ P(C)_{n+1}`.  That proof is outside Sweep III, so this structure is
only the precise interface consumed once those maps have been established; it
is not the construction owner for the levels.

Source: Weibel, Geometric Realization 10.9.19 (FC05-C10-U120). -/
structure ChainComplexGeometricBondingData
    (C : ChainComplex AddCommGrpCat.{u} ℤ) where
  structureMap : ∀ n : ℕ,
    suspensionObj (chainComplexGeometricLevel C n) ⟶
      chainComplexGeometricLevel C (n + 1)

/-- The prespectrum determined by the canonical realization levels once the
result-layer truncated-cone bonding maps are supplied. -/
noncomputable def chainComplexGeometricPrespectrum
    {C : ChainComplex AddCommGrpCat.{u} ℤ}
    (B : ChainComplexGeometricBondingData C) : Prespectrum.{u} where
  space := chainComplexGeometricLevel C
  structureMap := B.structureMap

/-- The raw spectrification data of the geometric-realization prespectrum.

This uses FC05-C10-U105's canonical colimit construction and deliberately does
not package a `Spectrum`: the colimit/loop homeomorphism and CW assertions are
Sweep-IV comparison results.
-/
noncomputable def chainComplexGeometricSpectrificationData
    {C : ChainComplex AddCommGrpCat.{u} ℤ}
    (B : ChainComplexGeometricBondingData C)
    (hCW : (chainComplexGeometricPrespectrum B).IsCW) :
    SpectrificationData (chainComplexGeometricPrespectrum B) :=
  spectrificationData (chainComplexGeometricPrespectrum B) hCW

end LeanCategories.Homological
