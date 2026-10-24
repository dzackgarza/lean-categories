/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Named carrier presentations retain their whole selected families

The two orders have different surface names and actual order structures, while
their existing carrier comparisons both land in `fin n`. The local negative
rows below are not registered. They distinguish a complete presentation from
one specialized at five, an omitted structural route, and a comparison made in
the wrong category.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.FiniteOrdersTests

open CasCatalogue.Foundation.FiniteOrders
open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- A valid set isomorphism only at one size, not a presentation of the family. -/
def fixedCarrier (_n : ℕ) : linearOrdersForget.toFunctor.obj (ordinary 5) ≅ fin 5 :=
  ordinaryCarrier 5

/-- An order isomorphism is not the required set-valued carrier comparison. -/
def orderIdentity (n : ℕ) : ordinary n ≅ ordinary n := Iso.refl _

open Lean Meta in
run_meta do
  let state ← semanticState
  let expectRefusal (label : String) (operation : MetaM Unit) := do
    let failure ← try operation; pure none catch e => pure (some (← e.toMessageData.toString))
    unless failure.isSome do throwError "accepted {label}"
  let some ordinary := state.objects.find? (·.id.raw == "obj.linear_orders.fin_ordinary")
    | throwError "missing ordinary finite order"
  let some reverse := state.objects.find? (·.id.raw == "obj.linear_orders.fin_reverse")
    | throwError "missing reverse finite order"
  let ordinaryProbe := { ordinary with
    id := ⟨"obj.probe.ordinary_finite_order"⟩, name := "probe ordinary finite order" }
  let reverseProbe := { reverse with
    id := ⟨"obj.probe.reverse_finite_order"⟩, name := "probe reverse finite order" }
  validateObject state ordinaryProbe
  validateObject state reverseProbe
  let some presentation := ordinaryProbe.refines
    | throwError "ordinary finite order has no carrier presentation"
  expectRefusal "a carrier presentation specialized at one size" <|
    validateObject state { ordinaryProbe with
      refines := some { presentation with identification := ``fixedCarrier } }
  expectRefusal "a presentation without its structural route" <|
    validateObject state { ordinaryProbe with
      refines := some { presentation with route := #[] } }
  expectRefusal "an order isomorphism substituted for a set carrier comparison" <|
    validateObject state { ordinaryProbe with
      refines := some { presentation with identification := ``orderIdentity } }

end CasCatalogue.Foundation.FiniteOrdersTests
