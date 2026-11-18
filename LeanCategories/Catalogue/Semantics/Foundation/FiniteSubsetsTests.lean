/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public meta import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# The finite-subset functor's laws and its natural inclusion into `𝒫`

`𝒫_fin : Sets ⥤ Sets` sends `X` to `Finset X` and `f` to `Finset.image f`; `𝒫 : Sets ⥤ Sets`
sends `X` to `Set X` and `f` to `A ↦ f '' A`; and `inclusionCell : 𝒫_fin ⟶ 𝒫` sends a finite
subset to its extent. Each check below is carried out on the smallest input that distinguishes the
registered mathematics from a lookalike:

* the action on `{1, 2} ⊆ Fin 3` under the collapsing map `Fin 3 → Fin 2`;
* both functor laws, applied to concrete subsets rather than read off the proof fields;
* the cell's component *is* the registered object inclusion of finite subsets into `𝒫`, and its
  naturality square commutes at the collapsing map (`inclusionCell.naturality`, i.e.
  `inclusion_natural`, i.e. `Finset.coe_image`);
* the inclusion is not natural into the contravariant preimage action, which is why its target is
  the covariant `𝒫` and not a preimage-valued power-set functor;
* the registration is load-bearing: the registered cell validates, and a row naming the wrong
  functor on either side, or the powerset *object* in place of the functor, is refused.

The rows exercised are `fun.sets.finite_subsets.direct_image`, `fun.sets.power_set` and
`cell.sets.finite_subsets.inclusion`, all written in `lean-categories` itself: the kernel and the
leaves register no part of this semantics.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.FiniteSubsetsTests

open CasCatalogue
open CasCatalogue.Foundation.Objects CasCatalogue.Foundation.PowerSets
open CasCatalogue.Foundation.FiniteSubsets

/-- The map `Fin 3 → Fin 2` collapsing everything to `0`. -/
def collapse : (Fin 3 : SetsCat.{0}) ⟶ (Fin 2 : SetsCat.{0}) := TypeCat.ofHom fun _ => 0

/-- The map `Fin 2 → Fin 1` collapsing everything to `0`. -/
def collapseSmall : (Fin 2 : SetsCat.{0}) ⟶ (Fin 1 : SetsCat.{0}) := TypeCat.ofHom fun _ => 0

/-- The action of `𝒫` on a subset is the direct image along the underlying function. -/
theorem powerSetFunctor_map_apply {X Y : SetsCat.{0}} (f : X ⟶ Y) (A : Set X) :
    (ConcreteCategory.hom (powerSetFunctor.map f) A : Set Y) = Set.image ⇑f A := rfl

/-- The inclusion's component at `X` sends a finite subset to its extent. -/
theorem inclusion_apply {X : SetsCat.{0}} (A : Finset X) :
    (ConcreteCategory.hom (inclusion X) A : Set X) = (A : Set X) := rfl

/-- The object half of `𝒫_fin` is `Finset X`. -/
example : directImage.obj (Fin 3) = Finset (Fin 3) := rfl

/-- The object half of `𝒫` is `Set X`. -/
example : powerSetFunctor.obj (Fin 2) = Set (Fin 2) := rfl

/-- The extent of the direct image of `{1, 2} ⊆ Fin 3` under the collapsing map is `{0}`: the
action on finite subsets is Mathlib's `Finset.coe_image`, `A ↦ f '' A`. -/
example :
    (ConcreteCategory.hom (powerSetFunctor.map collapse)
      (ConcreteCategory.hom (inclusion (Fin 3)) ({1, 2} : Finset (Fin 3))) : Set (Fin 2)) =
      ({0} : Set (Fin 2)) := by
  rw [inclusion_apply, powerSetFunctor_map_apply]
  change Set.image ⇑collapse (↑({1, 2} : Finset (Fin 3)) : Set (Fin 3)) = ({0} : Set (Fin 2))
  ext x
  fin_cases x <;> simp [collapse]

/-- The identity law of `𝒫`, on `{0, 1} ⊆ Fin 2`. -/
example :
    (ConcreteCategory.hom (powerSetFunctor.map (𝟙 (Fin 2 : SetsCat.{0})))
      ({0, 1} : Set (Fin 2)) : Set (Fin 2)) = ({0, 1} : Set (Fin 2)) := by
  rw [powerSetFunctor_map_apply]
  rw [show ⇑(ConcreteCategory.hom (𝟙 (Fin 2 : SetsCat.{0}))) = id from rfl]
  exact Set.image_id _

/-- The composition law of `𝒫`, on `{1, 2} ⊆ Fin 3` through the two collapsing maps. -/
example :
    (ConcreteCategory.hom (powerSetFunctor.map (collapse ≫ collapseSmall))
        ({1, 2} : Set (Fin 3)) : Set (Fin 1)) =
      (ConcreteCategory.hom (powerSetFunctor.map collapseSmall)
        (ConcreteCategory.hom (powerSetFunctor.map collapse) ({1, 2} : Set (Fin 3))) :
        Set (Fin 1)) := by
  rw [powerSetFunctor_map_apply, powerSetFunctor_map_apply, powerSetFunctor_map_apply]
  rw [← Set.image_comp]
  rw [show ⇑(ConcreteCategory.hom (collapse ≫ collapseSmall)) =
      ⇑(ConcreteCategory.hom collapseSmall) ∘ ⇑(ConcreteCategory.hom collapse) from rfl]

/-- The cell's component is the registered object inclusion of finite subsets into `𝒫`. -/
example (X : Type) : inclusionCell.app X = inclusion X := rfl

/-- The naturality square of the registered cell, at the collapsing map: the two composites of
`directImage.map collapse` with the inclusion are equal, which is the cell's `naturality` field
(`inclusion_natural`, i.e. `Finset.coe_image`). -/
example : directImage.map collapse ≫ inclusionCell.app (Fin 2) =
    inclusionCell.app (Fin 3) ≫ powerSetFunctor.map collapse :=
  inclusionCell.naturality collapse

/-- The inclusion is not natural into the contravariant preimage action: the constant map
`Fin 2 → Fin 2` sends `{1}` to `{0}`, whose preimage contains `0`, which is not in `{1}`. The
covariant `𝒫` is therefore the variance in which the inclusion is natural, and a
preimage-valued power-set functor is not a target for it. -/
theorem not_natural_into_preimage :
    ∃ x : Fin 2, x ∈ (fun _ : Fin 2 => (0 : Fin 2)) ⁻¹'
        ((({1} : Finset (Fin 2)).image fun _ => (0 : Fin 2)) : Set (Fin 2)) ∧
      x ∉ ({1} : Set (Fin 2)) := by
  refine ⟨0, ?_, ?_⟩ <;> simp

open Lean Meta in
run_meta do
  let state ← semanticState
  let expectRefusal (label : String) (operation : MetaM Unit) := do
    let failure ← try operation; pure none catch e => pure (some (← e.toMessageData.toString))
    unless failure.isSome do throwError "accepted {label}"
  let some cell := state.cells.find? (·.id.raw == "cell.sets.finite_subsets.inclusion")
    | throwError "missing the registered finite-subset inclusion cell"
  validateCell state cell
  expectRefusal "the inclusion as an endomorphism of the finite-subset functor" <|
    validateCell state { cell with right := #[.functor FunctorId.finiteSubsetsDirectImage] }
  expectRefusal "the inclusion into the identity functor" <|
    validateCell state { cell with right := #[] }
  expectRefusal "the power-set functor on the source side" <|
    validateCell state { cell with left := #[.functor FunctorId.setsPowerSet] }
  let some powerSetRow := state.functor? FunctorId.setsPowerSet
    | throwError "missing the registered power-set functor"
  validateSemanticEntryDeclaration (.functor powerSetRow)
  expectRefusal "the powerset object registered as the functor" <|
    validateSemanticEntryDeclaration (.functor { powerSetRow with
      declaration := `CasCatalogue.Foundation.PowerSets.powerSet })
  expectRefusal "the direct-image action registered in place of the functor" <|
    validateSemanticEntryDeclaration (.functor { powerSetRow with
      declaration := `CasCatalogue.Foundation.FiniteSubsets.directImage })

open Lean Meta in
run_meta do
  let state ← semanticState
  -- Neither `𝒫_fin` nor `𝒫` is a resolution edge: a construction functor is not `structural`, and
  -- the structural graph is built from `structural` rows only (`SemanticState.structuralEdges`), so
  -- the "selected structural routes" of #95 have no row to name.
  for id in [FunctorId.finiteSubsetsDirectImage, FunctorId.setsPowerSet] do
    let some row := state.functor? id
      | throwError "missing the registered functor {id.raw}"
    if row.structural then
      throwError "functor {id.raw} is registered as a structural route"
    if state.structuralEdges.any (·.ref == .functor id) then
      throwError "functor {id.raw} is a structural edge"
  -- Every row of this semantics is written in a `lean-categories` module, so neither the kernel nor
  -- a leaf supplies it: the registry refuses any other module root (`addSemanticEntryChecked`).
  let env ← getEnv
  for declaration in [`CasCatalogue.Foundation.FiniteSubsets.directImage,
      `CasCatalogue.Foundation.PowerSets.powerSetFunctor,
      `CasCatalogue.Foundation.FiniteSubsets.inclusionCell] do
    let some index := env.getModuleIdxFor? declaration
      | throwError "declaration {declaration} is not in the environment"
    let module := env.header.moduleNames[index.toNat]!
    unless module.getRoot == `LeanCategories do
      throwError "declaration {declaration} is supplied by {module}, not by `lean-categories`"

end CasCatalogue.Foundation.FiniteSubsetsTests
