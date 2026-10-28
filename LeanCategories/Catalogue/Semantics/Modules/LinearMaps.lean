/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Algebra.AdditiveOperations
public import LeanCategories.Catalogue.Semantics.Modules.CoordinateLinearity
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

Coordinate closure uses the existing `LinearMap.pi`, `prod`, `vecCons`, and
`vecEmpty` through `CoordinateLinearity.lean`. Its evidence is uniform in
index types and finite dimensions, and proves each coordinate's complete laws.
The existing whole `ModuleCat.Hom` functions, their compositions, and the actual
`ModuleCat.smul` action are read at their selected module structures. The last
is an additive-group endomorphism in general; its module-linearity is still
proved, never inferred merely from its being bundled as an additive map.
The evidence first uses the retained bundled presentation. When necessary it
also reads catalogue wrappers by the existing definitional `Units.readCatalogue`
procedure and proves the same laws in that presentation. `LinearMap.isLinear`
consumes an actual bundled linear map. No wrapper changes the underlying
function, scalar ring, or selected domain and codomain modules.

Definitionally equal closed presentations of those selected structures are
also admitted: for example, a commutative ring viewed through its forgetful
functor, a module formed by the published restriction-of-scalars family, and
the underlying function of that family's actual morphism action. Lean's
default automation guard compares implicit arguments at restricted transparency.
Within this proof procedure only, implicit selected structures are compared at
ordinary definitional transparency instead. This reads their definitions; it
does not identify different actions on one carrier. The original complete
`IsLinearMap` proposition is still proved and checked by `Evidence.establish`.
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
/-- Prove the full addition and scalar preservation laws, never a finite sample.
The local conversion scope unfolds definitionally equal implicit selected
structures, including restriction of scalars. It changes no structure or law.
Lean 4.33's `Meta.isDefEqArgs` otherwise compares these arguments at `.implicit`
transparency even inside a wider `withTransparency` scope. -/
meta partial def linearEvidence : TacticM Unit :=
  withOptions (fun options => options.setBool `backward.isDefEq.respectTransparency false) <|
  CasCatalogue.Evidence.establish "Linearity" do
    CasCatalogue.Algebra.Units.normalizeBundledObjects
    let prove : TacticM Unit :=
      CasCatalogue.Evidence.closeByFirst m!"the complete linearity laws are not established"
      [do evalTactic (← `(tactic| exact LinearMap.isLinear _)),
       do evalTactic (← `(tactic| exact IsLinearMap.isLinearMap_smul _)),
       do evalTactic (← `(tactic| exact CoordinateLinearity.vecEmpty)),
       do
         evalTactic (← `(tactic| apply CoordinateLinearity.vecCons))
         for goal in ← getGoals do
           setGoals [goal]
           linearEvidence,
       do
         evalTactic (← `(tactic| apply CoordinateLinearity.prod))
         for goal in ← getGoals do
           setGoals [goal]
           linearEvidence,
       do
         evalTactic (← `(tactic| apply CoordinateLinearity.pi))
         evalTactic (← `(tactic| intro i))
         linearEvidence,
       do
         evalTactic (← `(tactic| constructor <;> intros))
         for goal in ← getGoals do
           setGoals [goal]
           linearIdentity]
    CasCatalogue.Evidence.closeByFirst m!"the complete linearity laws are not established"
      [prove, do
        CasCatalogue.Algebra.Units.readCatalogue
        prove]

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
