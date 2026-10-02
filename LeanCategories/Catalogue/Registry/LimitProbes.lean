/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Limits.Registration

@[expose] public section

/-!
# Probes of the limit row's registration checks (CC-UNIV)

A limit row is accepted when its declaration is a family `∀ params (d : D), LimitCone (F d)` whose
input `d` is an object of its registered category of diagrams `D`, and whose diagrams `F d` have its
registered shape `J` and land in its registered category `C`. The registered pullback of sets is
accepted again below; each malformed row is refused, for the reason named. No probe row is
registered.
-/

open CategoryTheory Limits

namespace CasCatalogue.LimitProbes

universe u

/-- Products of two sets given as two parameters: no object of `Fun(WalkingPair, Sets)` is taken. -/
def productOfTwoSets (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) : LimitCone (pair X Y) :=
  Types.binaryProductLimitCone X Y

/-- One fixed product, with no input at all. -/
def fixedProduct : LimitCone (pair (PUnit.{1} : Type) (PUnit.{1} : Type)) :=
  Types.binaryProductLimitCone _ _

end CasCatalogue.LimitProbes

namespace CasCatalogue

open Lean Meta in
run_meta do
  let state ← semanticState
  let pullback : LimitEntry :=
    { id := ⟨"lim.probe"⟩, category := CategoryId.sets, shape := CategoryId.walkingCospan,
      diagrams := CategoryId.setsCospanDiagrams,
      declaration := `CasCatalogue.Limits.Registration.setsPullback }
  validateLimit state pullback
  let product : LimitEntry :=
    { pullback with
      shape := CategoryId.walkingPair, diagrams := CategoryId.setsPairDiagrams,
      declaration := `CasCatalogue.Limits.Registration.setsProduct }
  validateLimit state product
  let cases : List (LimitEntry × String) :=
    [({ product with declaration := `CasCatalogue.LimitProbes.productOfTwoSets },
        "is not an object of"),
     ({ product with declaration := `CasCatalogue.LimitProbes.fixedProduct }, "takes no input"),
     ({ pullback with shape := CategoryId.walkingPair }, "not of the shape"),
     ({ pullback with diagrams := CategoryId.setsPairDiagrams }, "is not an object of"),
     ({ pullback with category := CategoryId.groups }, "are not in"),
     ({ pullback with diagrams := ⟨"cat.probe.unregistered"⟩ }, "unregistered category of diagrams"),
     ({ product with
          declaration := `CasCatalogue.Limits.Registration.groupsKernel,
          shape := CategoryId.walkingParallelPair, category := CategoryId.groups },
        "is not an object of")]
  for (row, fragment) in cases do
    let refused ← try validateLimit state row; pure none
      catch e => pure (some (← e.toMessageData.toString))
    match refused with
    | some message =>
        unless (message.splitOn fragment).length > 1 do
          throwError "limit refused for another reason than '{fragment}': {message}"
    | none => throwError "limit accepted: {row.declaration} ('{fragment}')"

end CasCatalogue
