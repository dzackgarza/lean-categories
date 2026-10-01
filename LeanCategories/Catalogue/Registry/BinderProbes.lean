/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import Lean
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Probes of the binder row's registration checks (`lean-cas-dsl/specs/binders.md`)

A binder row is accepted when its operation is a morphism family whose source is a registered object
admitting maps `D → Y`, and its domain takes exactly the operation's parameters. Each malformed row
below is refused, for the reason named. No probe row is registered.
-/

open CategoryTheory

namespace CasCatalogue.BinderProbes

open CasCatalogue.Algebra.Calculus CasCatalogue.Algebra.NumberSystems
open CasCatalogue.Foundation.PowerSets

/-- `f ↦ ∫_a^b f` on `C(ℝ)`, with the bounds `a b : 1 ⟶ ℝ` as parameters. -/
noncomputable def integral (a b : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) :
    continuousMaps ⟶ reals :=
  TypeCat.ofHom fun f => ∫ t in (ConcreteCategory.hom (C := Type) a 0)..
    (ConcreteCategory.hom (C := Type) b 0), f t

/-- The variable of `∫_a^b` ranges over `ℝ`. -/
def line (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) : SetsCat.{0} := reals

/-- The integral again, with a parameter whose type depends on an earlier one (`h : 0 < n`). -/
noncomputable def integralDependent (n : ℕ) (_ : 0 < n)
    (a b : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) : continuousMaps ⟶ reals :=
  integral a b

/-- Its domain, with the same dependent parameters. -/
def lineDependent (n : ℕ) (_ : 0 < n) (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) :
    SetsCat.{0} := reals

/-- A domain whose dependent parameter differs (`h : n < 7`). -/
def lineOtherDependent (n : ℕ) (_ : n < 7) (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) :
    SetsCat.{0} := reals

/-- A domain with one bound only: not the operation's parameters. -/
def lineOneBound (_ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) : SetsCat.{0} := reals

/-- A domain that is not an object of `Sets`. -/
def notAnObject (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) : ℕ := 0

/-- An operation out of `ℝ`, an object with no admission. -/
def fromReals (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) : reals ⟶ reals := 𝟙 _

/-- An operation out of `ℝˣ`, whose admission admits elements of `ℝ`, not maps. -/
noncomputable def fromUnits (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) :
    CasCatalogue.Algebra.Units.units ℝ ⟶ reals :=
  TypeCat.ofHom fun u => (u : ℝ)

/-- Not a morphism family. -/
def notAMorphism (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) : ℕ := 0

/-- `Fin n ↪ Fin m` for `n ≤ m`: an inclusion between objects at different parameters, with an
obligation on them. -/
def finCastLE (n m : ℕ) (h : n ≤ m) :
    CasCatalogue.Foundation.Objects.fin n ⟶ CasCatalogue.Foundation.Objects.fin m :=
  TypeCat.ofHom (Fin.castLE h)

theorem finCastLE_mono (n m : ℕ) (h : n ≤ m) : Mono (finCastLE n m h) :=
  (CategoryTheory.mono_iff_injective _).2 (Fin.castLE_injective h)

end CasCatalogue.BinderProbes

namespace CasCatalogue

open Lean Meta in
run_meta do
  let state ← semanticState
  let probe : BinderEntry :=
    { id := ⟨"bind.probe"⟩, category := CategoryId.sets, token := "probe∫"
      operation := `CasCatalogue.BinderProbes.integral, domain := `CasCatalogue.BinderProbes.line }
  validateBinder state probe
  let dependent : BinderEntry := { probe with
    operation := `CasCatalogue.BinderProbes.integralDependent
    domain := `CasCatalogue.BinderProbes.lineDependent }
  validateBinder state dependent
  let cases : List (BinderEntry × String) :=
    [({ probe with token := "" }, "no notation token"),
     ({ probe with domain := `CasCatalogue.BinderProbes.lineOneBound }, "exactly the parameters"),
     ({ probe with domain := `CasCatalogue.BinderProbes.notAnObject }, "does not return an object"),
     ({ probe with operation := `CasCatalogue.BinderProbes.notAMorphism },
        "is not a morphism family"),
     ({ probe with operation := `CasCatalogue.BinderProbes.fromReals },
        "with an admission and evidence"),
     ({ probe with operation := `CasCatalogue.BinderProbes.fromUnits }, "not maps"),
     ({ dependent with domain := `CasCatalogue.BinderProbes.lineOtherDependent }, "parameters of")]
  for (row, fragment) in cases do
    let refused ← try validateBinder state row; pure none
      catch e => pure (some (← e.toMessageData.toString))
    match refused with
    | some message =>
        unless (message.splitOn fragment).length > 1 do
          throwError "binder refused for another reason than '{fragment}': {message}"
    | none => throwError "binder accepted: {row.operation}, {row.domain} ('{fragment}')"
  -- `ℝˣ` admits elements of `ℝ`, its element binder, not of its parameter `M : Type`.
  let fromUnits : BinderEntry :=
    { probe with operation := `CasCatalogue.BinderProbes.fromUnits }
  let units ← try validateBinder state fromUnits; pure ""
    catch e => e.toMessageData.toString
  if (units.splitOn "Type").length > 1 then
    throwError "the element of the admission of ℝˣ is read as a parameter: {units}"

-- An inclusion relates objects at whatever arguments its parameters determine.
open Lean Meta in
run_meta do
  validateInclusion (← semanticState)
    { id := ⟨"incl.probe.fin_cast_le"⟩, category := CategoryId.sets, sub := ⟨"obj.sets.fin"⟩
      super := ⟨"obj.sets.fin"⟩, declaration := `CasCatalogue.BinderProbes.finCastLE
      mono := `CasCatalogue.BinderProbes.finCastLE_mono }

end CasCatalogue
