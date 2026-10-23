/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ChangeValueLifts
public import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Catalogue

@[expose] public section

/-!
# A prescribed kernel model and two successive restrictions

This independently selected example is separate from the ordinary projection
with source form `diag(2,3)`. Here the source form is `2(a+b)(c+d)`, the target
form is `2su+5tv`, and the formed map is `(a,b) ↦ (a+b,0)`.
The selected module-kernel coordinate is `i₀(t)=(2t,-2t)`, so the first forward
comparison is genuinely `α(a,-a)=a/2`.

For the second stage retain an additional chosen form, the ordinary dot product
`ac+bd`. A pair of forms is an object of the already existing category with
value module `ℚ × ℚ`. The existing `changeValue fst` forgets this second form.
The first stage's actual formed inclusion is the second stage's input. The
second restricted form is `2ac` on vectors `(a,-a),(c,-c)`, or `8st` in the
selected `i₀` coordinates. Thus this stage retains nonzero additional data.

The original map is formed after projection to the first value. It need not
preserve the extra dot product: the composed operation is the prescribed lift
of its module-kernel inclusion through two specified functors.

Source: the independently supplied `genuine-formed-lift-proposal.md`, Mathlib's
matrix bilinear maps, and the existing `MonoLift.comp`.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts

open CasCatalogue.Algebra

/-- The independently specified degenerate source form. -/
def source : BilinModuleCat ℚ ℚ :=
  BilinModuleCat.ofBilinMap (Matrix.toBilin' (!![2, 2; 2, 2] : Matrix (Fin 2) (Fin 2) ℚ))

/-- The independently specified target form. -/
def target : BilinModuleCat ℚ ℚ :=
  BilinModuleCat.ofBilinMap (Matrix.toBilin' (!![2, 0; 0, 5] : Matrix (Fin 2) (Fin 2) ℚ))

theorem source_pairing (x y : Fin 2 → ℚ) :
    source.pairing x y = 2 * (x 0 + x 1) * (y 0 + y 1) := by
  simp [source, Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

theorem target_pairing (x y : Fin 2 → ℚ) :
    target.pairing x y = 2 * x 0 * y 0 + 5 * x 1 * y 1 := by
  simp [target, Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

/-- The ordinary map is independently fixed by the matrix `[[1,1],[0,0]]`. -/
def underlyingMap : source.carrierObj ⟶ target.carrierObj :=
  LinearAlgebra.matrixLinearMap 2 (CommRingCat.of ℚ) !![1, 1; 0, 0]

theorem underlyingMap_apply (x : Fin 2 → ℚ) :
    underlyingMap.hom x = ![x 0 + x 1, 0] := by
  ext j
  fin_cases j <;>
    simp [underlyingMap, LinearAlgebra.matrixLinearMap_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The universal pairing equation makes the fixed matrix a genuine formed arrow. -/
def formedMap : source ⟶ target :=
  BilinModuleCat.homMk underlyingMap.hom (by
    intro x y
    rw [underlyingMap_apply, underlyingMap_apply, target_pairing, source_pairing]
    simp)

/-- The selected, nontrivially scaled coordinate inclusion. -/
def kernelInclusion : ModuleCat.of ℚ ℚ ⟶ source.carrierObj :=
  ModuleCat.ofHom
    { toFun t := ![2 * t, -2 * t]
      map_add' s t := by
        ext j
        fin_cases j <;> simp <;> ring
      map_smul' r t := by
        ext j
        fin_cases j <;> simp <;> ring }

theorem kernelInclusion_apply (t : ℚ) :
    kernelInclusion.hom t = ![2 * t, -2 * t] := rfl

instance kernelInclusion_mono : Mono kernelInclusion := by
  apply (ModuleCat.mono_iff_injective _).2
  intro s t h
  have h₀ := congrFun h 0
  change 2 * s = 2 * t at h₀
  linarith

/-- This selected model lies in the kernel of the actual formed arrow. -/
theorem kernel_condition : kernelInclusion ≫ (forget ℚ ℚ).map formedMap = 0 := by
  ext t j
  change underlyingMap.hom (kernelInclusion.hom t) j = 0
  rw [underlyingMap_apply, kernelInclusion_apply]
  fin_cases j <;> simp <;> ring

/-- The image is the entire module kernel, not a smaller isotropic submodule. -/
theorem kernel_range : LinearMap.range kernelInclusion.hom = underlyingMap.hom.ker := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    rw [LinearMap.mem_ker, underlyingMap_apply, kernelInclusion_apply]
    ext j
    fin_cases j <;> simp <;> ring
  · intro hx
    have hx₀ := congrFun (LinearMap.mem_ker.mp hx) 0
    rw [underlyingMap_apply] at hx₀
    change x 0 + x 1 = 0 at hx₀
    refine ⟨x 0 / 2, ?_⟩
    ext j
    fin_cases j <;> simp [kernelInclusion_apply] <;> linarith

/-- The full universal factorization for the independently selected module-kernel model. -/
theorem kernel_universal (T : ModuleCat.{0} ℚ) (h : T ⟶ source.carrierObj)
    (hh : h ≫ (forget ℚ ℚ).map formedMap = 0) :
    ∃! g : T ⟶ ModuleCat.of ℚ ℚ, g ≫ kernelInclusion = h := by
  let g : T ⟶ ModuleCat.of ℚ ℚ :=
    ModuleCat.ofHom ((1 / 2 : ℚ) • (LinearMap.proj 0).comp h.hom)
  have hg : g ≫ kernelInclusion = h := by
    ext t j
    have ht := congrArg (fun k : T ⟶ target.carrierObj => k.hom t 0) hh
    change underlyingMap.hom (h.hom t) 0 = 0 at ht
    rw [underlyingMap_apply] at ht
    change h.hom t 0 + h.hom t 1 = 0 at ht
    fin_cases j <;> change _ = _ <;> dsimp [g, kernelInclusion] <;> linarith
  refine ⟨g, hg, ?_⟩
  intro k hk
  exact (cancel_mono kernelInclusion).mp (hk.trans hg.symm)

/-- The first stage is the existing form restriction along the selected module inclusion. -/
noncomputable def firstLift := Kernels.forgetMonoLift ℚ ℚ

noncomputable def firstObject : BilinModuleCat ℚ ℚ := firstLift.obj source kernelInclusion
noncomputable def firstInclusion : firstObject ⟶ source := firstLift.hom source kernelInclusion
noncomputable def alpha : firstObject.carrierObj ⟶ ModuleCat.of ℚ ℚ :=
  firstLift.computation.forward source kernelInclusion
noncomputable def beta : ModuleCat.of ℚ ℚ ⟶ firstObject.carrierObj :=
  firstLift.computation.backward source kernelInclusion

/-- A point of the actual first lifted carrier, with its range membership. -/
def firstPoint (a : ℚ) : firstObject.carrier :=
  ⟨![a, -a], ⟨a / 2, by
    ext j
    fin_cases j <;> simp [kernelInclusion_apply] <;> ring⟩⟩

/-- The backward comparison retains the independently prescribed factor two. -/
theorem beta_value (t : ℚ) : (beta.hom t).val = ![2 * t, -2 * t] := rfl

/-- The forward comparison is derived from the actual defining-map factorization. -/
theorem alpha_value (x : firstObject.carrier) : alpha.hom x = x.val 0 / 2 := by
  have h := congrArg (fun k : firstObject.carrierObj ⟶ source.carrierObj => k.hom x 0)
    (firstLift.fac source kernelInclusion)
  change x.val 0 = 2 * alpha.hom x at h
  linarith

theorem alpha_four : alpha.hom (firstPoint 4) = 2 := by
  rw [alpha_value]
  norm_num [firstPoint]

theorem first_defining_map (t : ℚ) :
    BilinModuleCat.underlyingMap firstInclusion (beta.hom t) = ![2 * t, -2 * t] := rfl

theorem first_pairing (s t : ℚ) :
    firstObject.pairing (beta.hom s) (beta.hom t) = 0 := by
  change source.pairing ![2 * s, -2 * s] ![2 * t, -2 * t] = 0
  rw [source_pairing]
  simp

theorem first_inverse_forward_backward : alpha ≫ beta = 𝟙 firstObject.carrierObj :=
  firstLift.computation_forward_backward source kernelInclusion

theorem first_inverse_backward_forward : beta ≫ alpha = 𝟙 (ModuleCat.of ℚ ℚ) :=
  firstLift.computation_backward_forward source kernelInclusion

theorem first_factorization :
    (forget ℚ ℚ).map firstInclusion = alpha ≫ kernelInclusion :=
  firstLift.computation_fac source kernelInclusion

/-- The genuinely additional chosen form is the ordinary dot product. -/
def dotSource : BilinModuleCat ℚ ℚ :=
  BilinModuleCat.ofBilinMap (Matrix.toBilin' (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ))

theorem dotSource_pairing (x y : Fin 2 → ℚ) :
    dotSource.pairing x y = x 0 * y 0 + x 1 * y 1 := by
  simp [dotSource, Matrix.toBilin'_apply, Fin.sum_univ_two]

/-- A pair of chosen forms uses the existing fixed value module `ℚ × ℚ`. -/
def pairedSource : BilinModuleCat ℚ (ℚ × ℚ) :=
  Opposite.op ⟨Opposite.op source.carrierObj, source.form.prod dotSource.form⟩

/-- Forgetting the second value recovers exactly the original selected formed source. -/
theorem pairedSource_first :
    (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).obj pairedSource = source := rfl

theorem pairedSource_pairing (x y : Fin 2 → ℚ) :
    pairedSource.pairing x y =
      (2 * (x 0 + x 1) * (y 0 + y 1), x 0 * y 0 + x 1 * y 1) := by
  change (source.pairing x y, dotSource.pairing x y) = _
  rw [source_pairing, dotSource_pairing]

/-- The second stage restores the additional chosen form on the first stage's actual carrier. -/
def secondLift :=
  ChangeValueLifts.changeValueMonoLift ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)

/-- The composed lift uses `firstInclusion` as its second input, by `MonoLift.comp`. -/
noncomputable def compositeLift := secondLift.comp firstLift

noncomputable def finalObject : BilinModuleCat ℚ (ℚ × ℚ) :=
  compositeLift.obj pairedSource kernelInclusion
noncomputable def finalInclusion : finalObject ⟶ pairedSource :=
  compositeLift.hom pairedSource kernelInclusion

noncomputable def finalAlpha : finalObject.carrierObj ⟶ ModuleCat.of ℚ ℚ :=
  compositeLift.computation.forward pairedSource kernelInclusion
noncomputable def finalBeta : ModuleCat.of ℚ ℚ ⟶ finalObject.carrierObj :=
  compositeLift.computation.backward pairedSource kernelInclusion

/-- This is one composed run: the first defining map is the actual second-stage input. -/
theorem final_object_is_successive :
    finalObject = secondLift.obj pairedSource firstInclusion := rfl

/-- The final defining map is the actual second-stage defining map. -/
theorem final_inclusion_is_second :
    finalInclusion = secondLift.hom pairedSource firstInclusion := rfl

/-- The first nonidentity coordinate comparison survives the second stage. -/
theorem final_alpha_value (x : finalObject.carrier) :
    finalAlpha.hom x = x.val 0 / 2 := alpha_value x

theorem final_beta_value (t : ℚ) :
    (finalBeta.hom t).val = ![2 * t, -2 * t] := rfl

/-- Both forms survive: the first vanishes on the kernel and the additional form does not. -/
theorem final_pairing (s t : ℚ) :
    finalObject.pairing (finalBeta.hom s) (finalBeta.hom t) = (0, 8 * s * t) := by
  change pairedSource.pairing ![2 * s, -2 * s] ![2 * t, -2 * t] = _
  rw [pairedSource_pairing]
  simp
  ring

/-- The final inclusion has a nonzero image and keeps the selected scaled coordinate. -/
theorem final_defining_map (t : ℚ) :
    BilinModuleCat.underlyingMap finalInclusion (finalBeta.hom t) = ![2 * t, -2 * t] := rfl

theorem final_defining_map_three_halves :
    BilinModuleCat.underlyingMap finalInclusion (finalBeta.hom (3 / 2)) = ![3, -3] := by
  rw [final_defining_map]
  norm_num

theorem final_inverse_forward_backward :
    finalAlpha ≫ finalBeta = 𝟙 finalObject.carrierObj :=
  compositeLift.computation_forward_backward pairedSource kernelInclusion

theorem final_inverse_backward_forward :
    finalBeta ≫ finalAlpha = 𝟙 (ModuleCat.of ℚ ℚ) :=
  compositeLift.computation_backward_forward pairedSource kernelInclusion

theorem final_factorization :
    ((changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)) ⋙ forget ℚ ℚ).map
      finalInclusion = finalAlpha ≫ kernelInclusion :=
  compositeLift.computation_fac pairedSource kernelInclusion

/-- The additional chosen form distinguishes the second stage from returning only the first. -/
theorem final_pairing_one :
    finalObject.pairing (finalBeta.hom 1) (finalBeta.hom 1) = (0, 8) := by
  rw [final_pairing]
  norm_num

end CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.bilin_module.degenerate_plane"⟩, category := CategoryId.bilinModule
    name := "DegeneratePlane"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.source }
normalized_registry .object
  { id := ⟨"obj.bilin_module.degenerate_plane_target"⟩, category := CategoryId.bilinModule
    name := "DegeneratePlaneTarget"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.target }
normalized_registry .morphism
  { id := ⟨"mor.bilin_module.degenerate_plane_map"⟩, category := CategoryId.bilinModule
    name := "degenerate_plane_map"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.formedMap }
normalized_registry .object
  { id := ⟨"obj.bilin_module.degenerate_plane_with_dot"⟩, category := CategoryId.bilinModule
    name := "DegeneratePlaneWithDot"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.pairedSource }

end CasCatalogue
