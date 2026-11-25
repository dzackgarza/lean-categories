/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.WellOrderedSetsRegistration
public meta import LeanCategories.Catalogue.Registry.Semantic

/-!
# The property-subcategory atom check answers, and does not leave a metavariable behind

`validateNotPropertyAtom` refuses an atom category that is a property subcategory of a registered
category, and admits an atom that is not. The second answer used to be a crash: the ambient category
was returned as an `Expr` out of the elaboration scope that created it, so an ambient matching no
registered category left an unassigned universe metavariable which the enclosing
`normalized_registry` command reported as `unknown universe metavariable ?_uniq.N` at the row. That
is what refused #97's category row before it was registered as a classifier total.

This module decides all three answers, on the smallest declarations that separate them.
-/

@[expose] public section

open CategoryTheory

namespace CasCatalogue

/-- An ambient category no registry row names, used only as the ambient of the admission control
below. Its carrier is `Bool` rather than a subsingleton so that its generated injectivity lemma is
not simp-provable (the `simpNF` linter refuses such a lemma), and it carries its own `Category`
instance rather than reusing one of a registered category. -/
structure ProbeAmbient where
  /-- Which of the two objects. -/
  object : Bool

instance : Category ProbeAmbient where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()

/-- A bundled category over the full subcategory of `ProbeAmbient` on `True`. Its ambient is that
unregistered category, so the check has nothing to match and must admit it. -/
def probeUnregisteredAmbient : LeanCategories.ObjCat :=
  Cat.of (ObjectProperty.FullSubcategory (C := ProbeAmbient) fun _ => True)

/-- A property subcategory of the linear orders that no row registers: the same ambient as the
well-ordered sets, with a different property, so neither the classifier-total rule nor a registered
total matches it. -/
def probeLinOrdSubcategory : LeanCategories.ObjCat :=
  Cat.of (ObjectProperty.FullSubcategory (C := LinOrd.{0}) fun _ => True)

open Lean Meta in
run_meta do
  let state ← semanticState
  let atom (id : String) (declaration : Name) : NamedCategoryEntry :=
    { id := ⟨id⟩, declaration, expression := .atom ⟨id⟩, realization := declaration }
  -- Run the check and return the message it refused with, if it refused.
  let refusal (entry : NamedCategoryEntry) : MetaM (Option String) := do
    try
      validateNotPropertyAtom state entry
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  -- (1) the well-ordered sets are a registered classifier's total, so an atom row for them is
  -- refused as that total: this is the #97 case, and the refusal names the classifier
  let some _ := state.category? Foundation.TotallyOrderedSets
    | throwError "the linear orders are not registered, so the refusal cases cannot be decided"
  let total := atom "cat.probe.property_subcategory" `LeanCategories.Foundation.WellOrderedSets
  match ← refusal total with
  | none => throwError "the check admitted a registered classifier's total"
  | some message =>
      unless message.contains "is the total of classifier clf.linear_orders.well_ordered" do
        throwError "the refusal does not name the classifier total: {message}"
      if message.contains "unknown universe metavariable" then
        throwError "the check leaked a universe metavariable: {message}"
  -- (2) a property subcategory of a registered category that is no registered total is refused by
  -- the name of its ambient category
  let subcategory := atom "cat.probe.linord_subcategory" `CasCatalogue.probeLinOrdSubcategory
  match ← refusal subcategory with
  | none => throwError "the check admitted a property subcategory of the linear orders"
  | some message =>
      unless message.contains "is a property subcategory of cat.totally_ordered_sets" do
        throwError "the refusal does not name the ambient category: {message}"
      if message.contains "unknown universe metavariable" then
        throwError "the check leaked a universe metavariable: {message}"
  -- (3) a full subcategory of an ambient that no row names is admitted, with no leftover
  let unregistered := atom "cat.probe.unregistered_ambient" `CasCatalogue.probeUnregisteredAmbient
  match ← refusal unregistered with
  | some message =>
      throwError "the check refused a full subcategory of an unregistered ambient: {message}"
  | none => pure ()
  -- (4) a category that is not a full subcategory at all is admitted
  let plain := atom "cat.probe.not_a_subcategory" `LeanCategories.Foundation.PartiallyOrderedSets
  match ← refusal plain with
  | some message => throwError "the check refused a category that is not a subcategory: {message}"
  | none => pure ()

end CasCatalogue
