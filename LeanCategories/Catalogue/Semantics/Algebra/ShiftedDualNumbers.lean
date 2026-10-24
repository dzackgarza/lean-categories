/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
public meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

@[expose] public section

/-!
# A nonidentity comparison of rational dual-number presentations

The independently chosen pair is Q[X]/(X²) and Q[Y]/((Y+1)²). Mathlib's Taylor
algebra equivalence and the existing `PolynomialPresentation.translate` own the
comparison. The selected generator goes to Y+1 and the inverse goes to X-1.
The source proves that the forward generator action differs from Y itself.
These are commutative quotient rings, with no claim that dual numbers are fields.
-/

open CategoryTheory Polynomial CasCatalogue.Foundation.PowerSets
namespace CasCatalogue.Algebra.ShiftedDualNumbers
open LeanCategories.Algebra.PolynomialPresentation
open PolynomialPresentations

/-- The defining polynomial `X²` over `ℚ` for the source dual-number presentation. -/
noncomputable abbrev sourcePolynomial : ℚ[X] := X ^ 2
/-- The defining polynomial `(Y + 1)²` over `ℚ` for the target dual-number presentation. -/
noncomputable abbrev targetPolynomial : ℚ[X] := Polynomial.taylor 1 sourcePolynomial
/-- The selected commutative ring `ℚ[X]/(X²)`, with the class of `X` as its named generator. -/
noncomputable abbrev sourceRing : CommRingCat := quotientRing (CommRingCat.of ℚ) sourcePolynomial
/-- The selected commutative ring `ℚ[Y]/((Y + 1)²)`, with the class of `Y` as its named generator. -/
noncomputable abbrev targetRing : CommRingCat := quotientRing (CommRingCat.of ℚ) targetPolynomial
/-- The underlying set of the selected presentation `ℚ[X]/(X²)`. -/
noncomputable abbrev sourceSet : SetsCat := AdjoinRoot sourcePolynomial
/-- The underlying set of the selected presentation `ℚ[Y]/((Y + 1)²)`. -/
noncomputable abbrev targetSet : SetsCat := AdjoinRoot targetPolynomial
/-- The closed point selecting the class of `X` in `ℚ[X]/(X²)`. -/
noncomputable def sourceGenerator : Foundation.Objects.fin 1 ⟶ sourceSet :=
  generator (CommRingCat.of ℚ) sourcePolynomial
/-- The closed point selecting the class of `Y` in `ℚ[Y]/((Y + 1)²)`. -/
noncomputable def targetGenerator : Foundation.Objects.fin 1 ⟶ targetSet :=
  generator (CommRingCat.of ℚ) targetPolynomial

/-- The coefficient map `c ↦ [c]` from `ℚ` into `ℚ[X]/(X²)`. -/
noncomputable def sourceConstants : (ℚ : SetsCat) ⟶ sourceSet :=
  constants (CommRingCat.of ℚ) sourcePolynomial
/-- The coefficient map `c ↦ [c]` from `ℚ` into `ℚ[Y]/((Y + 1)²)`. -/
noncomputable def targetConstants : (ℚ : SetsCat) ⟶ targetSet :=
  constants (CommRingCat.of ℚ) targetPolynomial

def sourceIdentification : (forget CommRingCat).obj sourceRing ≅ sourceSet := Iso.refl _
def targetIdentification : (forget CommRingCat).obj targetRing ≅ targetSet := Iso.refl _

/-- The chosen isomorphism `ℚ[X]/(X²) ≅ ℚ[Y]/((Y + 1)²)` sends `[X]` to
`[Y] + 1`; its inverse sends `[Y]` to `[X] - 1`. Both directions fix rational
coefficients. These generator and coefficient actions are proved below. -/
noncomputable def shiftedComparison : sourceRing ≅ targetRing :=
  translation (CommRingCat.of ℚ) sourcePolynomial 1

@[simp] theorem shiftedComparison_root :
    shiftedComparison.hom (AdjoinRoot.root sourcePolynomial) =
      AdjoinRoot.root targetPolynomial + 1 := by
  change translate sourcePolynomial (1 : ℚ) (AdjoinRoot.root sourcePolynomial) = _
  simpa only [map_one] using translate_root sourcePolynomial (1 : ℚ)

@[simp] theorem shiftedComparison_inv_root :
    shiftedComparison.inv (AdjoinRoot.root targetPolynomial) =
      AdjoinRoot.root sourcePolynomial - 1 := by
  change (translate sourcePolynomial (1 : ℚ)).symm
    (AdjoinRoot.root targetPolynomial) = _
  apply (translate sourcePolynomial (1 : ℚ)).injective
  simp only [AlgEquiv.apply_symm_apply, map_sub, translate_root, map_one,
    add_sub_cancel_right]

@[simp] theorem shiftedComparison_constants (c : ℚ) :
    shiftedComparison.hom (sourceConstants c) = targetConstants c :=
  (translate sourcePolynomial (1 : ℚ)).commutes c

@[simp] theorem shiftedComparison_inv_constants (c : ℚ) :
    shiftedComparison.inv (targetConstants c) = sourceConstants c :=
  (translate sourcePolynomial (1 : ℚ)).symm.commutes c

/-- The actual defining relation retained by the source quotient. -/
theorem source_root_square : (AdjoinRoot.root sourcePolynomial) ^ 2 = 0 := by
  simpa [sourcePolynomial] using
    AdjoinRoot.eval₂_root sourcePolynomial

/-- Constants embed in the displayed target quotient. -/
theorem target_degree : targetPolynomial.degree = 2 := by
  rw [targetPolynomial, sourcePolynomial, Polynomial.taylor_apply,
    Polynomial.pow_comp, Polynomial.X_comp]
  compute_degree <;> norm_num

/-- The comparison really changes the distinguished generator. -/
theorem shiftedComparison_root_ne :
    shiftedComparison.hom (AdjoinRoot.root sourcePolynomial) ≠
      AdjoinRoot.root targetPolynomial := by
  rw [shiftedComparison_root]
  intro h
  have h1 : AdjoinRoot.of targetPolynomial (1 : ℚ) =
      AdjoinRoot.of targetPolynomial 0 := by
    simpa only [map_one, map_zero] using add_eq_left.mp h
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero
    (f := targetPolynomial) (by rw [target_degree]; norm_num)
  have : (1 : ℚ) = 0 := hinj h1
  norm_num at this

/-- The translated target generator satisfies precisely the transported source relation. -/
theorem target_shifted_root_square : (AdjoinRoot.root targetPolynomial + 1) ^ 2 = 0 := by
  rw [← shiftedComparison_root, ← map_pow, source_root_square, map_zero]

/-- Evaluate the prescribed comparison using its source-proved generator actions. -/
meta def shiftedEvaluation : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_one, map_ofNat,
      CategoryTheory.Iso.hom_inv_id_apply, CategoryTheory.Iso.inv_hom_id_apply]))
  unless (← Lean.Elab.Tactic.getGoals).isEmpty do
    Lean.Elab.Tactic.evalTactic (← `(tactic| repeat' first
      | rw [shiftedComparison_root]
      | rw [shiftedComparison_inv_root]
      | rw [shiftedComparison_constants]
      | rw [shiftedComparison_inv_constants]))

end CasCatalogue.Algebra.ShiftedDualNumbers

namespace CasCatalogue
open Algebra.NamedRings
normalized_registry .object
  { id := ⟨"obj.sets.rational_dual_x"⟩, category := CategoryId.sets, name := "RationalDualX"
    declaration := `CasCatalogue.Algebra.ShiftedDualNumbers.sourceSet
    generator := some `CasCatalogue.Algebra.ShiftedDualNumbers.sourceGenerator }
normalized_registry .object
  { id := ⟨"obj.sets.rational_dual_y"⟩, category := CategoryId.sets, name := "RationalDualY"
    declaration := `CasCatalogue.Algebra.ShiftedDualNumbers.targetSet
    generator := some `CasCatalogue.Algebra.ShiftedDualNumbers.targetGenerator }
normalized_registry .object
  { id := ⟨"obj.commutative_rings.rational_dual_x"⟩, category := CategoryId.commutativeRings
    name := "RationalDualX", declaration := `CasCatalogue.Algebra.ShiftedDualNumbers.sourceRing
    refines := some
      { base := ⟨"obj.sets.rational_dual_x"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.ShiftedDualNumbers.sourceIdentification } }
normalized_registry .object
  { id := ⟨"obj.commutative_rings.rational_dual_y"⟩, category := CategoryId.commutativeRings
    name := "RationalDualY", declaration := `CasCatalogue.Algebra.ShiftedDualNumbers.targetRing
    refines := some
      { base := ⟨"obj.sets.rational_dual_y"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.ShiftedDualNumbers.targetIdentification } }
normalized_registry .morphism
  { id := ⟨"mor.sets.rational_dual_x_constants"⟩, category := CategoryId.sets
    name := "RationalDualX_constants"
    declaration := `CasCatalogue.Algebra.ShiftedDualNumbers.sourceConstants }
normalized_registry .morphism
  { id := ⟨"mor.sets.rational_dual_y_constants"⟩, category := CategoryId.sets
    name := "RationalDualY_constants"
    declaration := `CasCatalogue.Algebra.ShiftedDualNumbers.targetConstants }
normalized_registry .presentation
  { id := ⟨"cmp.rational_dual.translation"⟩, name := "rationalDualTranslation"
    source := ⟨"obj.commutative_rings.rational_dual_x"⟩
    target := ⟨"obj.commutative_rings.rational_dual_y"⟩
    declaration := `CasCatalogue.Algebra.ShiftedDualNumbers.shiftedComparison
    evaluation := some `CasCatalogue.Algebra.ShiftedDualNumbers.shiftedEvaluation }
end CasCatalogue
