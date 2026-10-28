/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
public import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
public import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients

@[expose] public section

/-!
# Mathematical checks of the complete comparison interfaces

These source propositions use the existing two-subset, cyclic-quotient and
formed-cone constructions. They check whole maps and exact endpoints. They
are mathematical compilation checks, not observations of any computation.
-/

open CategoryTheory

namespace CasCatalogue.Independent.InterfaceCompletionTests

open Foundation

/-- Reversal acts by direct image on every actual two-element subset. -/
theorem twoSubsets_reversal_extent (n : ℕ) (s : TwoSubsets.twoSubsets (Fin n)) :
    ((TwoSubsets.onCore.map (CoreIsomorphisms.finRevCore n) s).val : Set (Fin n)) =
      Fin.rev '' (s : Set (Fin n)) :=
  TwoSubsets.map_extent (CoreIsomorphisms.finRevCore n).iso.toEquiv.toEmbedding s

/-- Both retained inverse directions give the identity on the whole two-subset object. -/
theorem twoSubsets_reversal_twice (n : ℕ) :
    TwoSubsets.onCore.map (CoreIsomorphisms.finRevCore n) ≫
      TwoSubsets.onCore.map (CoreIsomorphisms.finRevCore n) =
        𝟙 (TwoSubsets.twoSubsets (Fin n)) := by
  rw [← TwoSubsets.onCore.map_comp, CoreIsomorphisms.finRevCore_comp,
    TwoSubsets.onCore.map_id]
  rfl

/-- The selected reversal on the original five-element set is nonidentity. -/
theorem fin_five_reversal_ne_identity :
    CoreIsomorphisms.finRevCore 5 ≠ 𝟙 (Core.mk (Fin 5)) := by
  intro h
  have h₀ := congrArg
    (fun f : Core.mk (Fin 5) ⟶ Core.mk (Fin 5) => f.iso.hom (0 : Fin 5)) h
  exact (by decide : (4 : Fin 5) ≠ 0) h₀

open Algebra.AutomorphismArrows Algebra.CyclicQuotients

/-- The public projected arrow has the complete unit-coordinate action. -/
theorem quotient_forward_coordinate (n : ℕ) (u : (ZMod n)ˣ) (x : cyclicQuotient n) :
    @Multiplicative.toAdd (ZMod n)
        ((residueComparison n).hom (groupsForward (cyclicQuotient n) (byUnit n u) x)) =
      (u : ZMod n) *
        @Multiplicative.toAdd (ZMod n) ((residueComparison n).hom x) :=
  byUnit_coordinate n u x

/-- The inverse projection has the full reciprocal-unit action at every point. -/
theorem quotient_backward_coordinate (n : ℕ) (u : (ZMod n)ˣ) (x : cyclicQuotient n) :
    @Multiplicative.toAdd (ZMod n)
        ((residueComparison n).hom (groupsBackward (cyclicQuotient n) (byUnit n u) x)) =
      (↑(u⁻¹) : ZMod n) *
        @Multiplicative.toAdd (ZMod n) ((residueComparison n).hom x) := by
  have h := byUnit_coordinate n u⁻¹ x
  rw [byUnit_inv] at h
  exact h

/-- At modulus five the fixed inverse of doubling acts by tripling on the whole group. -/
theorem quotient_five_backward_two (x : cyclicQuotient 5) :
    @Multiplicative.toAdd (ZMod 5)
        ((residueComparison 5).hom (groupsBackward (cyclicQuotient 5) (byUnit 5 unitTwo) x)) =
      3 * @Multiplicative.toAdd (ZMod 5) ((residueComparison 5).hom x) :=
  quotient_backward_coordinate 5 unitTwo x

/-- Conjugation retains the actual selected quotient/residue comparison and whole arrows. -/
theorem quotient_conjugate_forward (n : ℕ) (a : Aut (cyclicQuotient n)) :
    groupsForward (Algebra.FiniteGroups.cyclic n)
        ((Algebra.Automorphisms.automorphisms GrpCat).map
          (show Core.mk (cyclicQuotient n) ⟶ Core.mk (Algebra.FiniteGroups.cyclic n)
            from CoreHom.mk (residueComparison n)) a) =
      (residueComparison n).inv ≫ groupsForward (cyclicQuotient n) a ≫
        (residueComparison n).hom :=
  forward_conjugate (Cat.of GrpCat) _ _ (residueComparison n) a

open LeanCategories.Modules.Bilinear.Valued
open Modules.Bilinear.Valued
open DegeneratePlaneLifts DegeneratePlaneFactorization

/-- The existing monicity proof at its second-stage target, which is exactly
`source` by `pairedSource_first`. This retains the same first inclusion. -/
local instance firstInclusionAtPairedSource_mono : Mono
    (show firstObject ⟶ (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).obj pairedSource
      from firstInclusion) := firstInclusion_mono

/-- The exact source comparison for the nonmonic paired cone, with both original
formed objects retained. Its source is the changed-value paired cone source. -/
theorem paired_cone_comparison_triangle :
    (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map pairedCone =
      ChangeValueLifts.pulledBackForward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
        pairedSource cone ≫ cone :=
  (ChangeValueLifts.pulledBackForward_hom ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
    pairedSource cone).symm

/-- For every first factor with the required original source, its composition
with the actual comparison is an admissible base arrow at the second stage. -/
theorem paired_cone_factor_compatibility (h₁ : zeroSource ⟶ firstObject)
    (hh₁ : h₁ ≫ firstInclusion = cone) :
    (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map pairedCone =
      (ChangeValueLifts.pulledBackForward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
        pairedSource cone ≫ h₁) ≫ firstInclusion := by
  rw [Category.assoc, hh₁]
  exact paired_cone_comparison_triangle

set_option backward.isDefEq.respectTransparency false in
/-- Every pair of actual factors has the required whole-map comparison.
The proof uses the defining maps and monicity of the first inclusion; it
never identifies the two cone-source objects by equality of their carriers. -/
theorem paired_factor_comparison (h₁ : zeroSource ⟶ firstObject)
    (hh₁ : h₁ ≫ firstInclusion = cone) (h₂ : pairedConeSource ⟶ finalObject)
    (hh₂ : h₂ ≫ finalInclusion = pairedCone) :
    (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map h₂ ≫
        secondLift.computation.forward pairedSource firstInclusion =
      ChangeValueLifts.pulledBackForward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
        pairedSource cone ≫ h₁ := by
  apply (cancel_mono firstInclusion).mp
  rw [Category.assoc]
  rw [← secondLift.computation_fac pairedSource firstInclusion]
  change (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map h₂ ≫
      (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).map finalInclusion = _
  rw [← Functor.map_comp, hh₂]
  exact paired_cone_factor_compatibility h₁ hh₁

end CasCatalogue.Independent.InterfaceCompletionTests
