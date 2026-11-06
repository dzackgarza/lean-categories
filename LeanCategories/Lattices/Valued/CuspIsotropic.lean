/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantAction
public import LeanCategories.Lattices.Valued.CuspDescent
public import LeanCategories.Modules.Bilinear.Valued.Witt

/-!
# The isotropic subgroup `J_N = (N_ℚ ∩ L^∨)/N` of the discriminant form (#113 item 3)

For a primitive isotropic sublattice `N ⊆ L`, the subgroup of `A_L` carried by `N` is
`J_N = (N_ℚ ∩ L^∨)/N`: the rational span of `N` intersected with the dual lattice, modulo `N`. It is
not the dual of `N` — `N` is isotropic, so everything in `N_ℚ` pairs to zero with `N` and that dual
is all of `N_ℚ`.

The construction here avoids fraction-field scalars. Everything is an `R`-module: the dual lattice is
`metricDual R L`, the image `N'` of `N` is `N.toSubmodule.map (toMetricDual R L)`, and the rational
span intersected with `L^∨` is the *saturation* of `N'`,

`{x ∈ L^∨ | ∃ r ≠ 0, r • x ∈ N'}`,

which is `Sublattice.saturation N'` — the same construction that gives primitive closure in
`Sublattice.lean`, and its membership lemma `mem_saturation_iff` is what the isotropy argument
consumes. `metricDualToDiscriminant` then carries the saturation into `A_L = L.obj.defect`, and the
image is `J_N`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R] {L : IntegralLatticeCat R}

/-- The image of the primitive isotropic sublattice `N` in the dual lattice `L^∨`. -/
noncomputable abbrev metricDualImage {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R ↥(metricDual R L) :=
  N.toSubmodule.map (toMetricDual R L)

/-- `N_ℚ ∩ L^∨`: the saturation of the image of `N` in the dual lattice, i.e. the elements killed
into that image by a nonzero scalar. -/
noncomputable abbrev metricDualSaturation {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R ↥(metricDual R L) :=
  saturation (M := ↥(metricDual R L)) (metricDualImage N)

/-- `J_N = (N_ℚ ∩ L^∨)/N`, as a subgroup of the discriminant module `A_L`. -/
noncomputable abbrev isotropicSubgroup {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R L.obj.defect :=
  (metricDualSaturation N).map (metricDualToDiscriminant R L)

theorem discriminantBilinMap_eq_zero_of_mem_isotropicSubgroup
    (hL : IsFractionFieldPerfect R L) {k : ℕ} (N : PrimitiveIsotropic L k)
    {u v : L.obj.defect} (hu : u ∈ isotropicSubgroup N) (hv : v ∈ isotropicSubgroup N) :
    discriminantBilinMap R L hL u v = 0 := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hu
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
  rw [show discriminantBilinMap R L hL (metricDualToDiscriminant R L x)
        (metricDualToDiscriminant R L y) =
      fractionValueProjection R (rationalizedForm R L (↑x) (↑y)) from
    discriminant_pairing_metricDualToDiscriminant R hL x y]
  obtain ⟨r, hr, hrx⟩ := (mem_saturation_iff (metricDualImage N) x).mp hx
  obtain ⟨s, hs, hsy⟩ := (mem_saturation_iff (metricDualImage N) y).mp hy
  obtain ⟨a', ha', hra'⟩ := Submodule.mem_map.mp hrx
  obtain ⟨b', hb', hsb'⟩ := Submodule.mem_map.mp hsy
  have hxr : r • (↑x : RationalSpan R L) = ↑(toMetricDual R L a') := by
    rw [← Submodule.coe_smul, ← hra']
  have hys : s • (↑y : RationalSpan R L) = ↑(toMetricDual R L b') := by
    rw [← Submodule.coe_smul, ← hsb']
  have hpair : rationalizedForm R L (↑(toMetricDual R L a')) (↑(toMetricDual R L b')) = 0 := by
    rw [rationalizedForm_toMetricDual, ← IntegralLatticeCat.asBilinForm_apply,
      N.isotropic a' ha' b' hb', map_zero]
  have hfac : rationalizedForm R L (r • (↑x : RationalSpan R L)) (s • (↑y : RationalSpan R L)) =
      algebraMap R (FractionRing R) r * (algebraMap R (FractionRing R) s *
        rationalizedForm R L (↑x) (↑y)) := by
    rw [← IsScalarTower.algebraMap_smul (A := FractionRing R) r (↑x : RationalSpan R L),
      ← IsScalarTower.algebraMap_smul (A := FractionRing R) s (↑y : RationalSpan R L),
      LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_left]
    ring
  rw [hxr, hys, hpair] at hfac
  have hne : algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) s ≠ 0 := by
    rw [← map_mul]
    intro h0
    exact mul_ne_zero hr hs (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
  have hzero : rationalizedForm R L (↑x) (↑y) = 0 := by
    have h0 : algebraMap R (FractionRing R) r * (algebraMap R (FractionRing R) s *
        rationalizedForm R L (↑x) (↑y)) = 0 := hfac.symm
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (fun h1 => hr (IsFractionRing.injective R (FractionRing R)
        (by rw [h1, map_zero])))
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (fun h1 => hs (IsFractionRing.injective R (FractionRing R)
          (by rw [h1, map_zero])))
      · exact h'
  rw [hzero, map_zero]

/-- In `L^∨`, the saturation of `N` meets the kernel of the projection to `A_L` exactly along the
image of `N` itself, because the kernel is `toMetricDual`-of `L` and `N` is primitive. -/
theorem ker_inf_saturation (hL : IsFractionFieldPerfect R L) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    LinearMap.ker (metricDualToDiscriminant R L) ⊓ metricDualSaturation N = metricDualImage N := by
  rw [ker_metricDualToDiscriminant R L hL]
  apply le_antisymm
  · rintro x ⟨⟨a, rfl⟩, hx⟩
    obtain ⟨r, hr, hrx⟩ := (mem_saturation_iff (metricDualImage N) (toMetricDual R L a)).mp hx
    obtain ⟨b, hb, hrb⟩ := Submodule.mem_map.mp hrx
    have hb' : b = r • a := by
      apply toMetricDual_injective
      rw [hrb, map_smul]
    have ha' : r • a ∈ N.toSubmodule := hb' ▸ hb
    have ha : a ∈ saturation (M := L.obj.carrier) N.toSubmodule := by
      rw [mem_saturation_iff]
      exact ⟨r, hr, ha'⟩
    rw [(isPrimitiveSubmodule_iff_saturation_eq N.toSubmodule).mp N.primitive] at ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    refine ⟨⟨a, rfl⟩, le_saturation (M := ↥(metricDual R L)) (metricDualImage N) hx⟩

end LeanCategories.Lattices.Valued
