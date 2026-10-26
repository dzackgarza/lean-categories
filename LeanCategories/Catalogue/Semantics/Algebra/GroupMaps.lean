/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import Mathlib.Algebra.Group.Hom.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Actual group morphisms and checked admission of their whole functions

The objects are the hom sets of the selected `GrpCat` groups. Mathlib's
`MonoidHom.mk'` bundles a function after its multiplication preservation law is
proved; its group codomain supplies the derived unit law. `GrpCat.ofHom` then
forms the actual categorical morphism. Admission changes no value or endpoint.

The evidence procedure proves this entire law. In particular `mul_pow` is
available only when the selected carrier has its required commutative monoid
structure; arbitrary powers on arbitrary groups are not declared morphisms.

Reuse sources: Mathlib `Algebra/Group/Hom/Defs.lean` (`MonoidHom.mk'`),
`Algebra/Group/Hom/Basic.lean` (`powMonoidHom`), and
`Algebra/Category/Grp/Basic.lean` (`GrpCat.Hom`, `GrpCat.ofHom`), at
`db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0, Lean 4.33.0.
The public formalization-corpus query `MonoidHom.mk` on 2026-10-24 was followed
by inspection of these pinned definitions and their exact hypotheses.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.GroupMaps

universe u

/-- The actual hom set of the two selected groups. -/
def groupMaps (G H : GrpCat.{u}) : Type u := G ⟶ H

/-- Evaluation of the complete group morphism on its original domain. -/
def groupApplication (G H : GrpCat.{u}) :
    (groupMaps G H × G : Type u) ⟶ (H : Type u) :=
  TypeCat.ofHom fun p => (show G ⟶ H from p.1).hom p.2

/-- Forgetting only the homomorphism laws retains the whole original function. -/
def groupInclusion (G H : GrpCat.{u}) : groupMaps G H ⟶ (G → H : Type u) :=
  TypeCat.ofHom fun f => (show G ⟶ H from f).hom

instance groupInclusion_mono (G H : GrpCat.{u}) : Mono (groupInclusion G H) := by
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro f g h
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  exact congrFun h

/-- Bundle the exact function only after establishing its full multiplication law. -/
def admitGroup (G H : GrpCat.{u}) (f : G → H)
    (h : ∀ a b : G, f (a * b) = f a * f b) :
    (PUnit.{u + 1} : Type u) ⟶ groupMaps G H :=
  TypeCat.ofHom fun _ => GrpCat.ofHom (MonoidHom.mk' f h)

theorem groupInclusion_admit (G H : GrpCat.{u}) (f : G → H)
    (h : ∀ a b : G, f (a * b) = f a * f b) :
    admitGroup G H f h ≫ groupInclusion G H = TypeCat.ofHom (fun _ => f) := rfl

open Lean Elab Tactic in
/-- Establish the whole multiplication law from existing group-homomorphism
laws or a commutative power law, without sampling or adding structure. -/
meta def groupEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Group homomorphism" do
    CasCatalogue.Algebra.Units.readCatalogue
    CasCatalogue.Evidence.closeByFirst m!"the complete group homomorphism law is not established"
      [do evalTactic (← `(tactic| intros; simp only [map_mul])),
       do evalTactic (← `(tactic| intros; simp only [mul_pow])),
       do evalTactic (← `(tactic| intros; simp)),
       do evalTactic (← `(tactic| intros; rfl))]

end CasCatalogue.Algebra.GroupMaps

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.group_morphisms"⟩, category := CategoryId.sets, name := "GroupMorphisms"
    declaration := `CasCatalogue.Algebra.GroupMaps.groupMaps
    application := some `CasCatalogue.Algebra.GroupMaps.groupApplication
    inclusion := some `CasCatalogue.Algebra.GroupMaps.groupInclusion
    admission := some `CasCatalogue.Algebra.GroupMaps.admitGroup
    evidence := some `CasCatalogue.Algebra.GroupMaps.groupEvidence }

end CasCatalogue
