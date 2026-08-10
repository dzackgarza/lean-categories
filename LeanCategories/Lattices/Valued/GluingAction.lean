/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantAction
public import LeanCategories.Lattices.Valued.Gluing

@[expose] public section

open scoped Pointwise

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R}
variable {hL : IsGenericallyNondegenerate R L}

/-- The subgroup of `O(L)` that preserves an isotropic gluing subgroup. -/
noncomputable abbrev gluingStabilizer
    (H : DiscriminantIsotropicSubgroup R hL) :
    Subgroup (OrthogonalGroup L) :=
  OrthogonalGroup.discriminantSubmoduleStabilizer H.1

/-- An isometry is compatible with gluing when it preserves the gluing subgroup. -/
def OrthogonalGroup.IsCompatibleWithGluing
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL) : Prop :=
  g ∈ gluingStabilizer H

theorem OrthogonalGroup.isCompatibleWithGluing_iff
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL) :
    OrthogonalGroup.IsCompatibleWithGluing g H ↔
      H.1.map (OrthogonalGroup.actOnDefect g).toLinearMap = H.1 :=
  Submodule.mem_stabilizer_submodule_iff_map_eq

theorem OrthogonalGroup.actOnMetricDual_mem_metricDualPreimage
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL)
    (hg : OrthogonalGroup.IsCompatibleWithGluing g H)
    {x : metricDual R L}
    (hx : x ∈ metricDualPreimage R hL H) :
    OrthogonalGroup.actOnMetricDual g hL x ∈
      metricDualPreimage R hL H := by
  have hmap := (OrthogonalGroup.isCompatibleWithGluing_iff g H).mp hg
  change metricDualToDiscriminant R L
      (OrthogonalGroup.actOnMetricDual g hL x) ∈ H.1
  rw [OrthogonalGroup.metricDualToDiscriminant_actOnMetricDual]
  have hx' : metricDualToDiscriminant R L x ∈ H.1 := hx
  have hmem : OrthogonalGroup.actOnDefect g
      (metricDualToDiscriminant R L x) ∈
        H.1.map (OrthogonalGroup.actOnDefect g).toLinearMap :=
    ⟨metricDualToDiscriminant R L x, hx', rfl⟩
  rwa [hmap] at hmem

theorem OrthogonalGroup.map_metricDualPreimage
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL)
    (hg : OrthogonalGroup.IsCompatibleWithGluing g H) :
    (metricDualPreimage R hL H).map
        (OrthogonalGroup.actOnMetricDual g hL).toLinearMap =
      metricDualPreimage R hL H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact OrthogonalGroup.actOnMetricDual_mem_metricDualPreimage g H hg hx
  · intro x hx
    have hginv : OrthogonalGroup.IsCompatibleWithGluing g⁻¹ H :=
      (gluingStabilizer H).inv_mem hg
    refine ⟨OrthogonalGroup.actOnMetricDual g⁻¹ hL x,
      OrthogonalGroup.actOnMetricDual_mem_metricDualPreimage g⁻¹ H hginv hx, ?_⟩
    symm
    simpa using OrthogonalGroup.actOnMetricDual_mul_apply g g⁻¹ hL x

/-- A compatible isometry restricts to the metric-dual preimage of the gluing subgroup. -/
noncomputable def OrthogonalGroup.actOnMetricDualPreimage
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL)
    (hg : OrthogonalGroup.IsCompatibleWithGluing g H) :
    metricDualPreimage R hL H ≃ₗ[R] metricDualPreimage R hL H :=
  (OrthogonalGroup.actOnMetricDual g hL).ofSubmodules _ _
    (OrthogonalGroup.map_metricDualPreimage g H hg)

@[simp]
theorem OrthogonalGroup.actOnMetricDualPreimage_coe
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL)
    (hg : OrthogonalGroup.IsCompatibleWithGluing g H)
    (x : metricDualPreimage R hL H) :
    ((OrthogonalGroup.actOnMetricDualPreimage g H hg x :
        metricDualPreimage R hL H) : metricDual R L) =
      OrthogonalGroup.actOnMetricDual g hL x :=
  rfl

/-- The metric-dual preimage is the carrier of the constructed overlattice. -/
noncomputable def gluingCarrierEquiv
    (H : DiscriminantIsotropicSubgroup R hL) :
    metricDualPreimage R hL H ≃ₗ[R]
      (overlatticeFromIsotropicSubgroup R hL H).carrier :=
  (metricDual R L).equivSubtypeMap (metricDualPreimage R hL H)

/-- A gluing-compatible isometry acts on the constructed overlattice. -/
noncomputable def OrthogonalGroup.actOnGluedOverlattice
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL)
    (hg : OrthogonalGroup.IsCompatibleWithGluing g H) :
    (overlatticeFromIsotropicSubgroup R hL H).carrier ≃ₗ[R]
      (overlatticeFromIsotropicSubgroup R hL H).carrier :=
  (gluingCarrierEquiv H).symm |>.trans
    (OrthogonalGroup.actOnMetricDualPreimage g H hg) |>.trans
      (gluingCarrierEquiv H)

/-- The gluing action is the restriction of the rational action. -/
theorem OrthogonalGroup.actOnGluedOverlattice_coe
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL)
    (hg : OrthogonalGroup.IsCompatibleWithGluing g H)
    (x : (overlatticeFromIsotropicSubgroup R hL H).carrier) :
    (OrthogonalGroup.actOnGluedOverlattice g H hg x : RationalSpan R L) =
      OrthogonalGroup.actOnRationalSpan g x := by
  change (OrthogonalGroup.actOnMetricDual g hL
      (((gluingCarrierEquiv H).symm x : metricDualPreimage R hL H) :
        metricDual R L) : RationalSpan R L) = _
  rw [OrthogonalGroup.actOnMetricDual_coe]
  rfl

/-- The gluing action extends the original lattice isometry. -/
theorem OrthogonalGroup.actOnGluedOverlattice_inclusion
    (g : OrthogonalGroup L) (H : DiscriminantIsotropicSubgroup R hL)
    (hg : OrthogonalGroup.IsCompatibleWithGluing g H)
    (x : L.obj.carrier) :
    OrthogonalGroup.actOnGluedOverlattice g H hg
        ((overlatticeFromIsotropicSubgroup R hL H).inclusion x) =
      (overlatticeFromIsotropicSubgroup R hL H).inclusion (g.1 x) := by
  apply Subtype.ext
  change (OrthogonalGroup.actOnGluedOverlattice g H hg
      ((overlatticeFromIsotropicSubgroup R hL H).inclusion x) :
        RationalSpan R L) = toRationalSpan R L (g.1 x)
  rw [OrthogonalGroup.actOnGluedOverlattice_coe]
  simp [OrthogonalGroup.actOnRationalSpan, Overlattice.inclusion,
    toRationalSpan]

end LeanCategories.Lattices.Valued
