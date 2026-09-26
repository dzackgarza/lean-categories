/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Cellular homology data

Definition-level realization of Hatcher FC07-C02-U054, following the pinned
`sphere-six-complex` cellular-homology reference.

For a CW complex `X`, the degree-`n` cellular group is
`H_n(X^n, X^{n-1}; ℤ)`.  The cellular differential is characterized as the
connecting map for the pair `(X^{n+1}, X^n)`, followed by the canonical map
to `H_n(X^n, X^{n-1}; ℤ)`.

Sweep III records that exact graph as supplied boundary data.  It then records
exact cellular-chain-complex data relative to a supplied boundary family,
without proving that consecutive differentials compose to zero.  No arbitrary
differential or chain complex is selected before those results. The square-zero
theorem, and every comparison with singular homology, remain Sweep-IV content.
-/

@[expose] public noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open Topology

namespace LeanCategories.Topology

/-- Integral singular chains of a topological space. -/
abbrev cellularIntegralSingularChainComplexData (X : TopCat.{0}) :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of ℤ)).obj X

/-- The singular-chain map induced by a continuous map. -/
def cellularIntegralSingularChainMapData {X Y : TopCat.{0}} (f : X ⟶ Y) :
    cellularIntegralSingularChainComplexData X ⟶
      cellularIntegralSingularChainComplexData Y :=
  ((singularChainComplexFunctor AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of ℤ)).map f

/-- Relative integral singular chains as the cokernel of the chain map
induced by the subspace inclusion. -/
def cellularRelativeIntegralChainComplexData {X Y : TopCat.{0}} (i : X ⟶ Y) :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  cokernel (cellularIntegralSingularChainMapData i)

/-- Projection from absolute to relative singular chains. -/
def cellularRelativeIntegralProjectionData {X Y : TopCat.{0}} (i : X ⟶ Y) :
    cellularIntegralSingularChainComplexData Y ⟶
      cellularRelativeIntegralChainComplexData i :=
  cokernel.π (cellularIntegralSingularChainMapData i)

/-- The canonical short complex of absolute and relative singular chains.

Its short exactness for a subspace inclusion is deliberately not proved here;
it appears only existentially in the characterization of the connecting map. -/
def cellularRelativeIntegralShortComplexData {X Y : TopCat.{0}} (i : X ⟶ Y) :
    ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ) :=
  ShortComplex.mk (cellularIntegralSingularChainMapData i)
    (cellularRelativeIntegralProjectionData i)
    (cokernel.condition (cellularIntegralSingularChainMapData i))

/-- The union of cells of dimension strictly below `n`. -/
abbrev IntegralCWSkeletonLTData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :=
  {x : X // x ∈
    (Topology.RelCWComplex.skeletonLT
      (Set.univ : Set X) (n : ℕ∞) : Set X)}

/-- Inclusion of successive CW skeleta.  This uses only Mathlib's native
monotonicity of `skeletonLT`. -/
def integralCWSkeletonInclusionData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    TopCat.of (IntegralCWSkeletonLTData X n) ⟶
      TopCat.of (IntegralCWSkeletonLTData X (n + 1)) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, Topology.RelCWComplex.skeletonLT_mono
      (by exact_mod_cast Nat.le_succ n) x.2⟩, by fun_prop⟩

/-- Hatcher's degree-`n` cellular group
`H_n(X^n, X^{n-1}; ℤ)`. -/
abbrev integralCWRelativeCellObjectData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : AddCommGrpCat.{0} :=
  (cellularRelativeIntegralChainComplexData
    (integralCWSkeletonInclusionData X n)).homology n

/-- Exact graph of the cellular boundary map through the skeletal
long-exact sequence.

The short-exact witness is quantified over inside the proposition rather than
constructed in Sweep III. -/
def IsIntegralCWRelativeBoundaryData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (d : integralCWRelativeCellObjectData X (n + 1) ⟶
      integralCWRelativeCellObjectData X n) : Prop :=
  ∃ h :
      (cellularRelativeIntegralShortComplexData
        (integralCWSkeletonInclusionData X (n + 1))).ShortExact,
    d =
      h.δ (n + 1) n
          (ComplexShape.down_mk (n + 1) n (by omega)) ≫
        HomologicalComplex.homologyMap
          (cellularRelativeIntegralProjectionData
            (integralCWSkeletonInclusionData X n)) n

/-- Source-faithful degree-`n` cellular-boundary data: a candidate map
together with Hatcher's exact long-exact-sequence graph. -/
abbrev IntegralCWRelativeBoundaryData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Type _ :=
  {d :
      integralCWRelativeCellObjectData X (n + 1) ⟶
        integralCWRelativeCellObjectData X n //
    IsIntegralCWRelativeBoundaryData X n d}

/-- A source-facing family of valid cellular boundary maps. Existence and
square-zero are theorem content. -/
abbrev IntegralCWBoundarySystemData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :=
  ∀ n : ℕ, IntegralCWRelativeBoundaryData X n

/-- Exact graph of Hatcher's cellular chain complex.

The square-zero witness is existential data in the graph; this declaration
does not supply or prove it. -/
def IsIntegralCWCellularChainComplexData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (D : IntegralCWBoundarySystemData X)
    (K : ChainComplex AddCommGrpCat.{0} ℕ) : Prop :=
  ∃ hsq :
      ∀ n, (D (n + 1)).1 ≫ (D n).1 = 0,
    K =
      ChainComplex.of
        (fun n ↦ integralCWRelativeCellObjectData X n)
        (fun n ↦ (D n).1)
        hsq

/-- Source-faithful cellular chain-complex data relative to supplied valid
cellular boundaries.  The later square-zero theorem supplies existence. -/
abbrev IntegralCWCellularChainComplexData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (D : IntegralCWBoundarySystemData X) :=
  {K : ChainComplex AddCommGrpCat.{0} ℕ //
    IsIntegralCWCellularChainComplexData X D K}

/-- Integral cellular homology of supplied valid cellular-chain-complex data. -/
def integralCWCellularHomologyData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    {D : IntegralCWBoundarySystemData X}
    (K : IntegralCWCellularChainComplexData X D)
    (n : ℕ) : AddCommGrpCat.{0} :=
  K.1.homology n

end LeanCategories.Topology
