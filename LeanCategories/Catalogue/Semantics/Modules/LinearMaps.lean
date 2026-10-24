/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Actual module morphisms and their checked function admission

The mathematical owner is Mathlib's `ModuleCat.Hom`: a bundled `LinearMap` for
the selected scalar ring and both selected modules. `IsLinearMap R f` supplies
exactly the addition and scalar preservation laws of the entire function;
`IsLinearMap.mk'` and `ModuleCat.ofHom` bundle that same function. These
declarations expose those existing constructors through the ordinary object
admission interface. They introduce no alternate notion of linearity.

Sources: `Mathlib/Algebra/Module/LinearMap/Defs.lean` and
`Mathlib/Algebra/Category/ModuleCat/Basic.lean` at
`db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0); the source comparison
and Formalization Corpus searches are recorded in FOUNDATIONS Definition 13.1.
The ring may be noncommutative. In particular, an arbitrary scalar action is
not declared to be a module endomorphism without the same linearity laws.
-/

open CategoryTheory

namespace CasCatalogue.Modules.LinearMaps

universe u v

/-- The actual hom set of two selected modules in the same scalar fibre. -/
def linearMaps (R : RingCat.{u}) (M N : ModuleCat.{v} R) : Type v := M ⟶ N

/-- Evaluation of an actual module morphism on its original domain. -/
def linearApplication (R : RingCat.{u}) (M N : ModuleCat.{v} R) :
    (linearMaps R M N × M : Type v) ⟶ (N : Type v) :=
  TypeCat.ofHom fun p => (show M ⟶ N from p.1).hom p.2

/-- Forgetting the linearity laws keeps the whole underlying function. -/
def linearInclusion (R : RingCat.{u}) (M N : ModuleCat.{v} R) :
    linearMaps R M N ⟶ (M → N : Type v) :=
  TypeCat.ofHom fun f => (show M ⟶ N from f).hom

/-- Module morphisms are determined by their underlying functions. -/
instance linearInclusion_mono (R : RingCat.{u}) (M N : ModuleCat.{v} R) :
    Mono (linearInclusion R M N) := by
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro f g h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact congrFun h

/-- Bundle the original function only after proving both defining linearity laws. -/
def admitLinear (R : RingCat.{u}) (M N : ModuleCat.{v} R) (f : M → N)
    (h : IsLinearMap R f) : (PUnit.{v + 1} : Type v) ⟶ linearMaps R M N :=
  TypeCat.ofHom fun _ => ModuleCat.ofHom (IsLinearMap.mk' f h)

/-- The admission changes no value of the given function. -/
theorem linearInclusion_admit (R : RingCat.{u}) (M N : ModuleCat.{v} R)
    (f : M → N) (h : IsLinearMap R f) :
    admitLinear R M N f h ≫ linearInclusion R M N = TypeCat.ofHom (fun _ => f) := rfl

open Lean Elab Tactic in
/-- Establish a module identity, including selected product or function coordinates. -/
meta partial def linearIdentity : TacticM Unit :=
  CasCatalogue.Evidence.closeByFirst m!"the linearity identity is not established"
    [do evalTactic (← `(tactic| abel)),
     do evalTactic (← `(tactic| simp [ModuleCat.smul, smul_add, add_smul, two_smul] <;> abel)),
     do evalTactic (← `(tactic| simp [ModuleCat.smul, smul_add, add_smul, two_smul] <;> module)),
     do evalTactic (← `(tactic| simp <;> ring)),
     do
       evalTactic (← `(tactic| apply Prod.ext))
       for goal in ← getGoals do
         setGoals [goal]
         linearIdentity,
     do
       evalTactic (← `(tactic| funext i))
       linearIdentity]

open Lean Elab Tactic in
/-- Prove the full addition and scalar preservation laws, never a finite sample. -/
meta def linearEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Linearity" do
    CasCatalogue.Algebra.Units.normalizeBundledObjects
    CasCatalogue.Evidence.closeByFirst m!"the complete linearity laws are not established"
      [do evalTactic (← `(tactic| exact IsLinearMap.isLinearMap_smul _)),
       do
         evalTactic (← `(tactic| constructor <;> intros))
         for goal in ← getGoals do
           setGoals [goal]
           linearIdentity]

end CasCatalogue.Modules.LinearMaps

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.module_morphisms"⟩, category := CategoryId.sets, name := "ModuleMorphisms"
    declaration := `CasCatalogue.Modules.LinearMaps.linearMaps
    application := some `CasCatalogue.Modules.LinearMaps.linearApplication
    inclusion := some `CasCatalogue.Modules.LinearMaps.linearInclusion
    admission := some `CasCatalogue.Modules.LinearMaps.admitLinear
    evidence := some `CasCatalogue.Modules.LinearMaps.linearEvidence }

end CasCatalogue
