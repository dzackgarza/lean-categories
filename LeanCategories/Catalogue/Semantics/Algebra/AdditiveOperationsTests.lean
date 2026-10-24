/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.AdditiveOperations
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import LeanCategories.Catalogue.Semantics.Modules.LinearMaps
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.LinearMaps

@[expose] public section

open CategoryTheory
open CasCatalogue.Algebra.AdditiveOperations
open CasCatalogue.Modules.CatalogueRegistration

namespace CasCatalogue.Algebra.AdditiveOperationsTests

universe u v

/-- Every module gets its own whole addition through the existing total-category
additive-group projection, with the scalar fibre and module retained. -/
example (R : RingCat.{u}) (M : ModuleCat.{v} R) :
    add (additiveGroupsMonoid.obj (modulesAdditiveGroupDeclaration.obj
      ((modulesFibreInclusionDeclaration R).obj M))) =
        (TypeCat.ofHom fun p : M × M => p.1 + p.2) := rfl

/-- The whole doubled map satisfies the existing linear-map admission over any
selected ring, including noncommutative rings. -/
example (R : RingCat.{u}) (M : ModuleCat.{v} R) :
    IsLinearMap R (M := M) (M₂ := M) (fun m : M =>
      (add (additiveGroupsMonoid.obj (modulesAdditiveGroupDeclaration.obj
        ((modulesFibreInclusionDeclaration R).obj M))) (m, m) : M)) := by
  change IsLinearMap R (fun m : M => m + m)
  run_tac CasCatalogue.Modules.LinearMaps.linearEvidence

/-- A non-scalar-carrier module uses componentwise addition, not scalar-ring
addition selected by a coincident representation. -/
example (x y : Fin 2 → ℤ) :
    add (additiveGroupsMonoid.obj (modulesAdditiveGroupDeclaration.obj
      ((modulesFibreInclusionDeclaration (RingCat.of ℤ)).obj
        (ModuleCat.of ℤ (Fin 2 → ℤ))))) (x, y) = fun i => x i + y i := rfl

/-- The generic additive operation does not alter the selected ring binding. -/
example (R : RingCat.{0}) :
    add (additiveGroupsMonoid.obj (Ports.ringsAdditive.toFunctor.obj R)) =
      NamedRings.add R := rfl

/-- The same bare carrier admits a different additive-monoid structure. -/
example : add (AddMonCat.of ℤ) ((2 : ℤ), 3) = (5 : ℤ) := rfl

example : add (AddMonCat.of (Additive ℤ))
    (Additive.ofMul (2 : ℤ), Additive.ofMul (3 : ℤ)) =
      Additive.ofMul (6 : ℤ) := rfl

example : add (AddMonCat.of ℤ) ≠ add (AddMonCat.of (Additive ℤ)) := by
  intro h
  have impossible := congrArg (fun f => f ((2 : ℤ), 3)) h
  change (5 : ℤ) = 6 at impossible
  exact (by decide : (5 : ℤ) ≠ 6) impossible

open Lean Meta in
run_meta do
  let state ← semanticState
  let groups := Catalogue.Magmas.AdditiveGroups
  let monoids := Catalogue.Magmas.AdditiveMonoids
  let routes := state.routes groups monoids
  unless routes.size == 1 do
    throwError "the selected additive group must have its actual additive-monoid route"
  let some route := routes[0]?
    | throwError "the selected additive-group route is missing"
  unless state.isFirstOperationBindingRoute "+" route do
    throwError "the generic addition must be available along the additive route"
  let rings := Catalogue.Rings.Rings
  for route in state.routes rings monoids do
    if state.isFirstOperationBindingRoute "+" route then
      throwError "a farther additive binding replaced the explicit selected ring addition"
  unless (state.operations.filter fun op =>
      op.category == CategoryId.additiveMonoids && op.name == "+").size == 1 do
    throwError "addition must have one generic additive-monoid binding"

end CasCatalogue.Algebra.AdditiveOperationsTests
