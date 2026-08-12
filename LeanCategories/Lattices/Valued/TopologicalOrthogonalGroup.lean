/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Constructions
public import LeanCategories.Modules.Bilinear.Valued.OrthogonalGroup
public import LeanCategories.Modules.Bilinear.Valued.TopologicalOrthogonalGroup
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Matrix presentations of lattice orthogonal groups

A basis identifies the intrinsic orthogonal group of a formed lattice with the matrix orthogonal
group of its Gram matrix. Thus the topological matrix group is a presentation of the existing
orthogonal group, not a second mathematical object.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u v

variable {R : Type u} [CommRing R]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- A basis identifies linear automorphisms with invertible matrices. -/
noncomputable def linearEquivMatrixEquiv (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) :
    (L.obj.carrier ≃ₗ[R] L.obj.carrier) ≃*
      Matrix.GeneralLinearGroup I R :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R L.obj.carrier).symm.trans <|
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv

@[simp]
theorem linearEquivMatrixEquiv_apply_coe (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier)
    (g : L.obj.carrier ≃ₗ[R] L.obj.carrier) :
    ((linearEquivMatrixEquiv L b g : Matrix.GeneralLinearGroup I R) : Matrix I I R) =
      LinearMap.toMatrix b b g.toLinearMap :=
  rfl

/-- The matrix equation for an isometry is equivalent to preservation of the formed pairing. -/
theorem linearEquivMatrixEquiv_mem_orthogonal_iff
    (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier)
    (g : L.obj.carrier ≃ₗ[R] L.obj.carrier) :
    linearEquivMatrixEquiv L b g ∈ MatrixOrthogonalGroup (gramMatrix L b) ↔
      ∀ x y, L.obj.pairing (g x) (g y) = L.obj.pairing x y := by
  change (LinearMap.toMatrix b b g.toLinearMap).transpose *
      LinearMap.BilinForm.toMatrix b L.obj.bilinMap *
      LinearMap.toMatrix b b g.toLinearMap =
        LinearMap.BilinForm.toMatrix b L.obj.bilinMap ↔ _
  rw [← LinearMap.BilinForm.toMatrix_comp]
  constructor
  · intro h x y
    have hform : LinearMap.BilinForm.comp L.obj.bilinMap
        g.toLinearMap g.toLinearMap = L.obj.bilinMap :=
      (LinearMap.BilinForm.toMatrix b).injective h
    exact LinearMap.congr_fun (LinearMap.congr_fun hform x) y
  · intro h
    congr 1
    ext x y
    exact h x y

/-- A basis identifies the intrinsic and matrix orthogonal groups. -/
noncomputable def orthogonalGroupMatrixEquiv (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) :
    BilinModuleCat.OrthogonalGroup L.obj ≃*
      MatrixOrthogonalGroup (gramMatrix L b) := by
  let e := linearEquivMatrixEquiv L b
  have hsub : e.mapSubgroup (BilinModuleCat.orthogonalSubgroup L.obj) =
      MatrixOrthogonalGroup (gramMatrix L b) := by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (linearEquivMatrixEquiv_mem_orthogonal_iff L b g).mpr hg
    · intro hA
      refine ⟨e.symm A, ?_, e.apply_symm_apply A⟩
      exact (linearEquivMatrixEquiv_mem_orthogonal_iff L b (e.symm A)).mp <| by
        rw [e.apply_symm_apply]
        exact hA
  exact (e.subgroupMap (BilinModuleCat.orthogonalSubgroup L.obj)).trans
    (MulEquiv.subgroupCongr hsub)

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The topology on the intrinsic orthogonal group transported from a matrix presentation. -/
@[reducible] noncomputable def orthogonalGroupTopology (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) :
    TopologicalSpace (BilinModuleCat.OrthogonalGroup L.obj) :=
  TopologicalSpace.induced (orthogonalGroupMatrixEquiv L b) inferInstance

/-- The transported topology makes the intrinsic orthogonal group a topological group. -/
theorem orthogonalGroup_isTopologicalGroup (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) :
    @IsTopologicalGroup (BilinModuleCat.OrthogonalGroup L.obj)
      (orthogonalGroupTopology L b) inferInstance :=
  topologicalGroup_induced (orthogonalGroupMatrixEquiv L b)

/-- The matrix presentation transports local compactness to the intrinsic orthogonal group. -/
theorem orthogonalGroupLocallyCompactSpace
    [T2Space R] [LocallyCompactSpace R]
    (L : IntegralLatticeCat R) (b : Module.Basis I R L.obj.carrier) :
    @LocallyCompactSpace (BilinModuleCat.OrthogonalGroup L.obj)
      (orthogonalGroupTopology L b) := by
  letI : TopologicalSpace (BilinModuleCat.OrthogonalGroup L.obj) :=
    orthogonalGroupTopology L b
  let e := orthogonalGroupMatrixEquiv L b
  exact (show Topology.IsInducing e from ⟨rfl⟩).locallyCompactSpace <| by
    rw [Set.range_eq_univ.mpr e.surjective]
    exact isOpen_univ.isLocallyClosed

/-- Haar measure on the intrinsic orthogonal group in a basis presentation. -/
noncomputable def orthogonalGroupHaarMeasure [T2Space R] [LocallyCompactSpace R]
    (L : IntegralLatticeCat R) (b : Module.Basis I R L.obj.carrier) :
    @MeasureTheory.Measure (BilinModuleCat.OrthogonalGroup L.obj)
      (@borel (BilinModuleCat.OrthogonalGroup L.obj) (orthogonalGroupTopology L b)) := by
  letI : TopologicalSpace (BilinModuleCat.OrthogonalGroup L.obj) :=
    orthogonalGroupTopology L b
  letI : IsTopologicalGroup (BilinModuleCat.OrthogonalGroup L.obj) :=
    orthogonalGroup_isTopologicalGroup L b
  letI : LocallyCompactSpace (BilinModuleCat.OrthogonalGroup L.obj) :=
    orthogonalGroupLocallyCompactSpace L b
  letI : MeasurableSpace (BilinModuleCat.OrthogonalGroup L.obj) := borel _
  letI : BorelSpace (BilinModuleCat.OrthogonalGroup L.obj) := ⟨rfl⟩
  exact MeasureTheory.Measure.haar

end Topology

end LeanCategories.Lattices.Valued
