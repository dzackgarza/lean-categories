/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.LinearGraph
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# Winding number of planar loops

This file realizes the definitional layer of Munkres FC02-C10-U027 and FC02-C10-U032.
No reusable Lean implementation of the source winding-number definition was found in Sweep II.
The construction uses pinned Mathlib's standard `AddCircle` covering and path-lifting API.
-/

namespace LeanCategories.Topology

open Set

abbrev WindingInterval := unitInterval

/-- The period-one universal cover of the unit circle. -/
noncomputable def standardCircleCover : ℝ → Circle :=
  fun t => AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0) (t : AddCircle (1 : ℝ))

@[simp]
theorem standardCircleCover_zero : standardCircleCover 0 = 1 := by
  simp [standardCircleCover, AddCircle.homeomorphCircle_apply]

/-- The period-one map `ℝ → S¹` is a covering map. -/
theorem isCoveringMap_standardCircleCover : IsCoveringMap standardCircleCover := by
  change IsCoveringMap
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0) ∘
      ((↑) : ℝ → AddCircle (1 : ℝ)))
  exact (AddCircle.isCoveringMap_coe (p := (1 : ℝ))).homeomorph_comp
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0))

/-- A loop in the unit circle, with its closing equality retained as data. -/
structure CircleLoop where
  map : C(WindingInterval, Circle)
  closes : map 0 = map 1

namespace CircleLoop

/-- Rotate a circle loop so that it is based at `1`. -/
noncomputable def basedMap (γ : CircleLoop) : C(WindingInterval, Circle) where
  toFun t := γ.map t * (γ.map 0)⁻¹
  continuous_toFun := γ.map.continuous.mul (continuous_inv.comp continuous_const)

@[simp]
theorem basedMap_zero (γ : CircleLoop) : γ.basedMap 0 = 1 := by
  simp [basedMap]

@[simp]
theorem basedMap_one (γ : CircleLoop) : γ.basedMap 1 = 1 := by
  simp [basedMap, ← γ.closes]

/-- The unique lift of the based circle loop starting at `0`. -/
noncomputable def lift (γ : CircleLoop) : C(WindingInterval, ℝ) :=
  isCoveringMap_standardCircleCover.liftPath γ.basedMap 0 (by simp)

@[simp]
theorem lift_zero (γ : CircleLoop) : γ.lift 0 = 0 := by
  exact isCoveringMap_standardCircleCover.liftPath_zero _ _ _

theorem cover_lift (γ : CircleLoop) : standardCircleCover ∘ γ.lift = γ.basedMap :=
  isCoveringMap_standardCircleCover.liftPath_lifts _ _ _

theorem cover_lift_one (γ : CircleLoop) : standardCircleCover (γ.lift 1) = 1 := by
  have h := congr_fun γ.cover_lift 1
  simpa using h

/-- The endpoint of the canonical lift is an integer. -/
theorem lift_one_is_integer (γ : CircleLoop) : ∃ n : ℤ, (n : ℝ) = γ.lift 1 := by
  have h : standardCircleCover (γ.lift 1) = standardCircleCover 0 := by
    rw [γ.cover_lift_one, standardCircleCover_zero]
  have hc : ((γ.lift 1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).injective
    exact h
  rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hc with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  norm_num at hn ⊢
  exact hn

/-- The integer endpoint is unique. -/
theorem lift_one_is_unique_integer (γ : CircleLoop) :
    ∃! n : ℤ, (n : ℝ) = γ.lift 1 := by
  rcases γ.lift_one_is_integer with ⟨n, hn⟩
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact_mod_cast hm.trans hn.symm

/-- Winding number of a circle loop: the integer endpoint of its canonical lifted based loop. -/
noncomputable def windingNumber (γ : CircleLoop) : ℤ :=
  Classical.choose γ.lift_one_is_integer

theorem windingNumber_coe_eq_lift_one (γ : CircleLoop) :
    (γ.windingNumber : ℝ) = γ.lift 1 :=
  Classical.choose_spec γ.lift_one_is_integer

end CircleLoop

/-- Normalize a nonzero complex number to the unit circle. -/
noncomputable def normalizeComplex (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    change z / (‖z‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z), div_self]
    exact norm_ne_zero_iff.mpr hz⟩

/-- Pointwise normalization of a continuous nonvanishing complex-valued map. -/
noncomputable def normalizeContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) (h : ∀ x, f x ≠ 0) : C(X, Circle) where
  toFun x := normalizeComplex (f x) (h x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact f.continuous.div
      (Complex.continuous_ofReal.comp (continuous_norm.comp f.continuous))
      (fun x => by exact_mod_cast norm_ne_zero_iff.mpr (h x))

/-- A closed planar loop. We identify the plane with `ℂ`. -/
structure PlanarLoop where
  map : C(WindingInterval, ℂ)
  closes : map 0 = map 1

namespace PlanarLoop

/-- Translate a planar loop by `-a`. -/
noncomputable def translateFrom (γ : PlanarLoop) (a : ℂ) : C(WindingInterval, ℂ) where
  toFun t := γ.map t - a
  continuous_toFun := γ.map.continuous.sub continuous_const

/-- The normalized circle loop associated to a planar loop avoiding `a`. -/
noncomputable def normalizedAbout (γ : PlanarLoop) (a : ℂ) (ha : ∀ t, γ.map t ≠ a) : CircleLoop where
  map := normalizeContinuousMap (γ.translateFrom a) (fun t => sub_ne_zero.mpr (ha t))
  closes := by
    apply Circle.ext
    change (γ.map 0 - a) / (‖γ.map 0 - a‖ : ℂ) =
      (γ.map 1 - a) / (‖γ.map 1 - a‖ : ℂ)
    rw [γ.closes]

/-- Munkres' winding number `n(f,a)` (FC02-C10-U027). -/
noncomputable def windingNumberAt (γ : PlanarLoop) (a : ℂ) (ha : ∀ t, γ.map t ≠ a) : ℤ :=
  (γ.normalizedAbout a ha).windingNumber

/-- The image set of a planar loop. -/
def image (γ : PlanarLoop) : Set ℂ := Set.range γ.map

/-- A planar loop is simple in the sense of Munkres: no repeated points except the two endpoint
parameters of the loop. -/
def IsSimple (γ : PlanarLoop) : Prop := IsSimpleLoop γ.map

/-- A point lies in a bounded connected component of the complement of the loop image. -/
def InBoundedComplementComponent (γ : PlanarLoop) (a : ℂ) : Prop :=
  a ∉ γ.image ∧ Bornology.IsBounded (connectedComponentIn γ.imageᶜ a)

/-- A simple planar loop is counterclockwise when its winding number is `+1` at some point in a
bounded complementary component (definitional content of FC02-C10-U032). The source theorem that
this value is independent of the chosen point in that component belongs to Sweep IV. -/
def IsCounterclockwise (γ : PlanarLoop) : Prop :=
  γ.IsSimple ∧ ∃ a : ℂ, ∃ ha : ∀ t, γ.map t ≠ a,
    γ.InBoundedComplementComponent a ∧ γ.windingNumberAt a ha = 1

/-- A simple planar loop is clockwise when its winding number is `-1` at some point in a bounded
complementary component (FC02-C10-U032). -/
def IsClockwise (γ : PlanarLoop) : Prop :=
  γ.IsSimple ∧ ∃ a : ℂ, ∃ ha : ∀ t, γ.map t ≠ a,
    γ.InBoundedComplementComponent a ∧ γ.windingNumberAt a ha = -1

end PlanarLoop

end LeanCategories.Topology
