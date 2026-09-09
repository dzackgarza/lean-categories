/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace LeanCategories.CategoryTheory

universe w' w v₁ v₂ u₁ u₂

variable {C : Type u₁} [_root_.CategoryTheory.Category.{v₁} C]
variable {D : Type u₂} [_root_.CategoryTheory.Category.{v₂} D]
variable {J : Type w} [_root_.CategoryTheory.Category.{w'} J]

/-- `F` strictly creates the limit of `K` when every specified limit cone over `K ⋙ F`
has an exact lift to a limiting cone over `K`, and every exact lift is that cone
(FC03-C03-U043). -/
def StrictlyCreatesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop :=
  ∀ (c : Cone (K ⋙ F)), IsLimit c →
    ∃ d : Cone K, F.mapCone d = c ∧ Nonempty (IsLimit d) ∧ ∀ d' : Cone K, F.mapCone d' = c → d' = d

/-- Dual strict creation notion for colimits (FC03-C03-U043). -/
def StrictlyCreatesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop :=
  ∀ (c : Cocone (K ⋙ F)), IsColimit c →
    ∃ d : Cocone K, F.mapCocone d = c ∧ Nonempty (IsColimit d) ∧
      ∀ d' : Cocone K, F.mapCocone d' = c → d' = d

/-- The identity functor strictly creates every limit: the basic intended example. -/
theorem strictlyCreatesLimit_id (K : J ⥤ C) : StrictlyCreatesLimit K (𝟭 C) := by
  intro c hc
  refine ⟨c, rfl, ⟨hc⟩, ?_⟩
  intro d hd
  cases hd
  rfl

/-- The identity functor strictly creates every colimit: the dual intended example. -/
theorem strictlyCreatesColimit_id (K : J ⥤ C) : StrictlyCreatesColimit K (𝟭 C) := by
  intro c hc
  refine ⟨c, rfl, ⟨hc⟩, ?_⟩
  intro d hd
  cases hd
  rfl

/-- Strict limit creation gives an exact lift, the clause absent from ordinary `CreatesLimit`. -/
theorem StrictlyCreatesLimit.hasExactLift {K : J ⥤ C} {F : C ⥤ D}
    (h : StrictlyCreatesLimit K F) (c : Cone (K ⋙ F)) (hc : IsLimit c) :
    ∃ d : Cone K, F.mapCone d = c := by
  rcases h c hc with ⟨d, hd, _, _⟩
  exact ⟨d, hd⟩

/-- Dual exact-lift consequence. -/
theorem StrictlyCreatesColimit.hasExactLift {K : J ⥤ C} {F : C ⥤ D}
    (h : StrictlyCreatesColimit K F) (c : Cocone (K ⋙ F)) (hc : IsColimit c) :
    ∃ d : Cocone K, F.mapCocone d = c := by
  rcases h c hc with ⟨d, hd, _, _⟩
  exact ⟨d, hd⟩


section AcceptanceExamples

/- A separating model for FC03-C03-U043. Ordinary `CreatesLimit` permits a chosen lift up to
isomorphism, while strict creation requires a unique literal lift. The constant functor from the
two-object codiscrete category to the one-object codiscrete category creates the empty-diagram
limit in Mathlib's ordinary sense, but cannot strictly create it because the two distinct source
objects give two exact limiting lifts of the same target cone. -/
namespace StrictCreationSeparator

abbrev Source := _root_.CategoryTheory.Codiscrete Bool
abbrev Target := _root_.CategoryTheory.Codiscrete PUnit

def forgetObjects : Source ⥤ Target :=
  _root_.CategoryTheory.Codiscrete.functorOfFun (fun _ : Bool => PUnit.unit)

def emptyDiagram : _root_.CategoryTheory.Discrete PEmpty ⥤ Source :=
  _root_.CategoryTheory.Functor.empty Source

def targetCone : Cone (emptyDiagram ⋙ forgetObjects) :=
  asEmptyCone (_root_.CategoryTheory.Codiscrete.mk PUnit.unit)

def falseCone : Cone emptyDiagram :=
  asEmptyCone (_root_.CategoryTheory.Codiscrete.mk false)

def trueCone : Cone emptyDiagram :=
  asEmptyCone (_root_.CategoryTheory.Codiscrete.mk true)

instance : forgetObjects.Faithful where
  map_injective _ := Subsingleton.elim _ _

instance : forgetObjects.Full where
  map_surjective _ := ⟨default, Subsingleton.elim _ _⟩

noncomputable example : CreatesLimit emptyDiagram forgetObjects := by
  let hc : IsLimit targetCone := IsTerminal.ofUnique _
  exact createsLimitOfFullyFaithfulOfLift' hc falseCone (Iso.refl _)

example : ¬ StrictlyCreatesLimit.{0,0,0,0,0,0} emptyDiagram forgetObjects := by
  intro h
  have hc : IsLimit targetCone := IsTerminal.ofUnique _
  rcases h targetCone hc with ⟨d, _, _, unique⟩
  have hf : falseCone = d := unique falseCone (by rfl)
  have ht : trueCone = d := unique trueCone (by rfl)
  have hft : falseCone = trueCone := hf.trans ht.symm
  have hp : (falseCone.pt : Source) = trueCone.pt := congrArg Cone.pt hft
  exact Bool.false_ne_true (congrArg _root_.CategoryTheory.Codiscrete.as hp)

end StrictCreationSeparator

end AcceptanceExamples

end LeanCategories.CategoryTheory
