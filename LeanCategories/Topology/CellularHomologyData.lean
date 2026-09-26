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
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.CategoryTheory.Limits.MonoCoprod

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
  (cellularRelativeIntegralShortComplexData
    (integralCWSkeletonInclusionData X n)).X₃.homology n

/-- The inclusion of successive CW skeleta induces a monomorphism on
integral singular chain complexes. -/
theorem integralCWSkeletonChainMap_mono
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Mono (cellularIntegralSingularChainMapData
      (integralCWSkeletonInclusionData X n)) := by
  apply HomologicalComplex.mono_of_mono_f _
  intro k
  let i := integralCWSkeletonInclusionData X n
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : IntegralCWSkeletonLTData X (n + 1) => z.1) h
  change Mono ((CategoryTheory.Limits.sigmaConst.obj (AddCommGrpCat.of ℤ)).map
    ((TopCat.toSSet.map i).app (Opposite.op (SimplexCategory.mk k))))
  haveI : Mono ((TopCat.toSSet.map i).app
      (Opposite.op (SimplexCategory.mk k))) := by
    rw [CategoryTheory.mono_iff_injective]
    intro a b hab
    apply (TopCat.toSSetObjEquiv
      (X := TopCat.of (IntegralCWSkeletonLTData X n)) _).injective
    apply ContinuousMap.ext
    intro z
    apply hi
    exact congrArg
      (fun s => TopCat.toSSetObjEquiv
        (X := TopCat.of (IntegralCWSkeletonLTData X (n + 1))) _ s z) hab
  infer_instance

/-- The canonical absolute/absolute/relative singular-chain sequence for
successive CW skeleta is short exact. -/
noncomputable def integralCWRelativeShortExactData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    (cellularRelativeIntegralShortComplexData
      (integralCWSkeletonInclusionData X n)).ShortExact := by
  let S := cellularRelativeIntegralShortComplexData
    (integralCWSkeletonInclusionData X n)
  letI : Mono S.f := integralCWSkeletonChainMap_mono X n
  have hC : Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) := by
    refine ⟨?_⟩
    dsimp [S, cellularRelativeIntegralShortComplexData,
      cellularRelativeIntegralProjectionData]
    exact cokernelIsCokernel (cellularIntegralSingularChainMapData
      (integralCWSkeletonInclusionData X n))
  have h := (S.exact_and_epi_g_iff_g_is_cokernel).2 hC
  letI : Epi S.g := h.2
  exact { exact := h.1 }

/-- Integral singular homology of the `m`th skeleton in degree `n`. -/
abbrev integralCWSkeletonHomologyData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (m n : ℕ) : AddCommGrpCat.{0} :=
  (cellularIntegralSingularChainComplexData
    (TopCat.of (IntegralCWSkeletonLTData X m))).homology n

/-- The connecting morphism from the relative group in degree `n+1` to
absolute homology of the intermediate skeleton in degree `n`. -/
noncomputable def integralCWConnectingData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWRelativeCellObjectData X (n + 1) ⟶
      integralCWSkeletonHomologyData X (n + 1) n :=
  (integralCWRelativeShortExactData X (n + 1)).δ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by omega))

/-- Projection from absolute homology of the target skeleton to its relative
cellular group. -/
noncomputable def integralCWProjectionHomologyData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWSkeletonHomologyData X (n + 1) n ⟶
      integralCWRelativeCellObjectData X n :=
  HomologicalComplex.homologyMap
    (cellularRelativeIntegralProjectionData
      (integralCWSkeletonInclusionData X n)) n

/-- The projection in one skeletal long exact sequence followed by its
connecting morphism is zero. -/
theorem integralCWProjection_comp_connecting
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWProjectionHomologyData X (n + 1) ≫
      integralCWConnectingData X n = 0 := by
  exact (integralCWRelativeShortExactData X (n + 1)).comp_δ
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))

/-- Hatcher's cellular boundary map, constructed from the connecting
homomorphism for the canonical short exact sequence of successive skeleta,
followed by projection to the next relative group. -/
noncomputable def integralCWRelativeBoundaryData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWRelativeCellObjectData X (n + 1) ⟶
      integralCWRelativeCellObjectData X n :=
  integralCWConnectingData X n ≫ integralCWProjectionHomologyData X n

/-- Consecutive cellular boundaries compose to zero. -/
theorem integralCWRelativeBoundaryData_comp
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    integralCWRelativeBoundaryData X (n + 1) ≫
      integralCWRelativeBoundaryData X n = 0 := by
  rw [integralCWRelativeBoundaryData, integralCWRelativeBoundaryData]
  simp only [Category.assoc]
  rw [← Category.assoc (integralCWProjectionHomologyData X (n + 1)),
    integralCWProjection_comp_connecting X n, zero_comp, comp_zero]

/-- Hatcher's cellular chain complex, assembled from the actual relative
homology groups and connecting-map differentials. -/
noncomputable def integralCWCellularChainComplexData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  ChainComplex.of
    (fun n ↦ integralCWRelativeCellObjectData X n)
    (fun n ↦ integralCWRelativeBoundaryData X n)
    (integralCWRelativeBoundaryData_comp X)

/-- Integral cellular homology of the constructed cellular chain complex. -/
def integralCWCellularHomologyData
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : AddCommGrpCat.{0} :=
  (integralCWCellularChainComplexData X).homology n

end LeanCategories.Topology
