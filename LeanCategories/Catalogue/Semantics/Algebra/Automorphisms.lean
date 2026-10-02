/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Subgroups
public import LeanCategories.Catalogue.Semantics.Algebra.Ports
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import LeanCategories.Catalogue.Semantics.Modules.Rank
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Conj
public import Mathlib.GroupTheory.GroupAction.Basic
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public meta import LeanCategories.Catalogue.Semantics.Modules.Expressions
public meta import LeanCategories.Catalogue.Semantics.Algebra.Ports
public meta import LeanCategories.Catalogue.Semantics.Algebra.Subgroups
public meta import LeanCategories.Catalogue.Semantics.Modules.Rank

@[expose] public section

/-!
# Group-valued constructions land in `Grp` and `Subobjects(Grp)` (CC-UNIV, LC-16)

A group-valued construction is a functor into `Grp`, and a subgroup-valued one a functor into
`Subobjects(Grp)`, so that its values are groups and subgroups by construction: they inherit what
every group and every subgroup has (`Subobjects(Grp) → Grp → Mon → Sets`, `inclusion`), including
what is registered there later, with no declaration of their own.

* **Units.** `(−)ˣ : Mon ⥤ Grp` is Mathlib's right adjoint to the group-to-monoid
  forgetful functor. `Algebra.Units` registers it, the chosen group object, and
  its underlying-set presentation at the same `MonCat` parameter. The checked
  `ObjectFunctorPresentation` cites the identification; inversion is registered
  once on all groups, with `inverse_eq_groupInverse` retaining the element-calculus law.
* **Automorphisms.** For every category `C`, `Aut : Core(C) ⥤ Grp`, `X ↦ Aut(X)` with
  `g h = h ≫ g` (Mathlib `Aut`), and an isomorphism `e : X ≅ Y` acting by conjugation
  `a ↦ e⁻¹ ≫ a ≫ e` (Mathlib `Aut.autMulEquivOfIso`). It is defined on the core: a morphism that is
  not invertible induces no map of automorphism groups. Likewise `End : Core(C) ⥤ Mon`
  (`Iso.conj`), and `Aut ≅ End ⋙ (−)ˣ` (Mathlib `Aut.unitsEndEquivAut`): `Aut(X)` is the group of
  units of the monoid `End(X)`, as `GLₙ(K) = Matₙ(K)ˣ`.
* **Stabilizers.** For `U : C ⥤ Sets` and an element `x ∈ U(X)`, the stabilizer of `x` is the
  automorphism group of `(X, x)` in the category of elements `Elements(U)`, included into `Aut(X)`
  along the faithful projection `π : Elements(U) ⥤ C` (Mathlib `Functor.mapAut`). Its image is
  `{g ∈ Aut(X) | U(g) x = x}` (`mem_range_stabilizerInclusion_iff`); for `U = 𝟭 Sets` it is Mathlib's
  `MulAction.stabilizer` of `x` in `Perm(X) ≅ Aut(X)` (`stabilizer_sets`). So
  `Stab : Core(Elements(U)) ⥤ Subobjects(Grp)`, with ambient group `Aut(X)`
  (`stabilizersCodomainIso`). For a group `G` acting on a set `X`, with action map
  `ρ : G →* Perm(X) ≅ Aut(X)`, Mathlib's `MulAction.stabilizer G x` is the preimage
  `ρ⁻¹(Stab(X, x))` (`Subgroup.comap`, the pullback of the mono `Stab(X, x) ↪ Aut(X)` along `ρ` in
  `Grp`) (`stabilizer_action`).

Registered here: `(−)ˣ` with its adjunction, and the `Aut`/`End` functors with their units
comparison on `Core(Sets)` (symmetric groups), `Core(Grp)` (automorphism groups of groups) and
`Core(Mod_R)` (`GL(M)`); the stabilizers of points of sets, `Core(Sets_*) ⥤ Subobjects(Grp)` with
`Sets_* = Elements(𝟭 Sets)`, and their ambient-group comparison. `Aut` and `Stab` are not
presented as methods: a method is inherited along structural functors (CC-UNIFORM), and the
automorphisms of a group are not those of its underlying set (`COMPLAINTS.md`).
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra

namespace CasCatalogue.Algebra.Automorphisms

universe u v

section Generic

variable (C : Type u) [Category.{v} C]

/-- `End : Core(C) ⥤ Mon`. -/
def endomorphisms : Core C ⥤ MonCat.{v} where
  obj X := MonCat.of (End X.of)
  map e := MonCat.ofHom e.iso.conj.toMonoidHom
  map_id X := by ext a; simp [Iso.conj_apply]
  map_comp e f := by ext a; simp [Iso.conj_apply]

/-- `Aut : Core(C) ⥤ Grp`. -/
def automorphisms : Core C ⥤ GrpCat.{v} where
  obj X := GrpCat.of (Aut X.of)
  map e := GrpCat.ofHom (Aut.autMulEquivOfIso e.iso).toMonoidHom
  map_id X := by
    ext a : 2; apply Iso.ext
    change (Iso.refl X.of).inv ≫ a.hom ≫ (Iso.refl X.of).hom = a.hom
    simp
  map_comp e f := by
    ext a : 2; apply Iso.ext
    change (e.iso ≪≫ f.iso).inv ≫ a.hom ≫ (e.iso ≪≫ f.iso).hom =
      f.iso.inv ≫ (e.iso.inv ≫ a.hom ≫ e.iso.hom) ≫ f.iso.hom
    simp

/-- `Aut ≅ End ⋙ (−)ˣ`. -/
def automorphismsIsoUnits : automorphisms C ≅ endomorphisms C ⋙ MonCat.units :=
  NatIso.ofComponents (fun X => (Aut.unitsEndEquivAut X.of).symm.toGrpIso) fun e => by
    ext a : 2; apply Units.ext
    change e.iso.inv ≫ a.hom ≫ e.iso.hom = e.iso.conj a.hom
    simp [Iso.conj_apply]

end Generic

section Stabilizers

variable {C : Type u} [Category.{v} C] (U : C ⥤ Type v)

/-- The inclusion `Aut(X, x) ↪ Aut(X)`. -/
def stabilizerInclusion (p : U.Elements) : Aut p →* Aut p.1 :=
  (CategoryOfElements.π U).mapAut p

theorem stabilizerInclusion_injective (p : U.Elements) :
    Function.Injective (stabilizerInclusion U p) := fun _ _ h =>
  Iso.ext ((CategoryOfElements.π U).map_injective (congrArg Iso.hom h))

theorem mem_range_stabilizerInclusion_iff (p : U.Elements) (g : Aut p.1) :
    g ∈ (stabilizerInclusion U p).range ↔ U.map g.hom p.2 = p.2 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.hom.2
  · intro h
    refine ⟨⟨⟨g.hom, h⟩, ⟨g.inv, ?_⟩, ?_, ?_⟩, rfl⟩
    · conv_lhs => rw [← h]
      exact Iso.hom_inv_id_apply (U.mapIso g) p.2
    · exact CategoryOfElements.ext _ _ _ g.hom_inv_id
    · exact CategoryOfElements.ext _ _ _ g.inv_hom_id

/-- An isomorphism `e : (X, x) ≅ (Y, y)` of elements conjugates `Aut(X, x) ↪ Aut(X)` onto
`Aut(Y, y) ↪ Aut(Y)`: the inclusions commute with conjugation by `e` and by `π e`. -/
theorem stabilizerInclusion_conj {p q : Core U.Elements} (e : p ⟶ q) :
    (automorphisms U.Elements).map e ≫ GrpCat.ofHom (stabilizerInclusion U q.of) =
      GrpCat.ofHom (stabilizerInclusion U p.of) ≫
        (automorphisms C).map ((CategoryOfElements.π U).core.map e) := by
  refine GrpCat.ext fun a => Iso.ext ?_
  change (CategoryOfElements.π U).map (e.iso.inv ≫ a.hom ≫ e.iso.hom) =
    (CategoryOfElements.π U).map e.iso.inv ≫ (CategoryOfElements.π U).map a.hom ≫
      (CategoryOfElements.π U).map e.iso.hom
  simp only [Functor.map_comp]

/-- `Stab : Core(Elements(U)) ⥤ Subobjects(Grp)`, `(X, x) ↦ (Aut(X, x) ↪ Aut(X))`. -/
def stabilizers : Core U.Elements ⥤ (LeanCategories.isMonoArrow GrpCat.{v}).FullSubcategory where
  obj p := ⟨Arrow.mk (GrpCat.ofHom (stabilizerInclusion U p.of)),
    (GrpCat.mono_iff_injective _).mpr (stabilizerInclusion_injective U p.of)⟩
  map e := ObjectProperty.homMk (Arrow.homMk ((automorphisms U.Elements).map e)
    ((automorphisms C).map ((CategoryOfElements.π U).core.map e)) (stabilizerInclusion_conj U e))
  map_id p := ObjectProperty.hom_ext _ (Arrow.hom_ext _ _ ((automorphisms U.Elements).map_id p)
    ((automorphisms C).map_id _))
  map_comp e f := ObjectProperty.hom_ext _ (Arrow.hom_ext _ _
    ((automorphisms U.Elements).map_comp e f)
    (((automorphisms C).congr_map ((CategoryOfElements.π U).core.map_comp e f)).trans
      ((automorphisms C).map_comp _ _)))

/-- The ambient group of `Stab(X, x)` is `Aut(X)`. -/
def stabilizersCodomainIso :
    stabilizers U ⋙ (LeanCategories.isMonoArrow GrpCat.{v}).ι ⋙ Arrow.rightFunc ≅
      (CategoryOfElements.π U).core ⋙ automorphisms C :=
  NatIso.ofComponents (fun p => Iso.refl ((automorphisms C).obj ⟨p.of.1⟩)) fun _ => by
    simp only [Iso.refl_hom]
    rfl

end Stabilizers

/-- The stabilizer of a point `x ∈ X` of a set is Mathlib's `MulAction.stabilizer` of `x` in the
permutations `Perm(X) ≅ Aut(X)` (`Aut.mulEquivPerm`). -/
theorem stabilizer_sets (p : (𝟭 (Type u)).Elements) :
    (stabilizerInclusion (𝟭 (Type u)) p).range.map Aut.mulEquivPerm.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm p.1) (show p.1 from p.2) := by
  ext σ
  rw [Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_range_stabilizerInclusion_iff _ p g).mp hg
  · intro hσ
    refine ⟨Aut.mulEquivPerm.symm σ, (mem_range_stabilizerInclusion_iff _ p _).mpr hσ, ?_⟩
    simp

/-- The action map `G →* Aut(X)` of a group action on a set: `g ↦ (x ↦ g • x)`. -/
def actionHom (G : Type*) [Group G] (X : Type u) [MulAction G X] : G →* Aut X :=
  Aut.mulEquivPerm.symm.toMonoidHom.comp (MulAction.toPermHom G X)

/-- The stabilizer of `x` under a group action is the preimage of `Stab(X, x) ≤ Aut(X)` along the
action map. -/
theorem stabilizer_action (G : Type*) [Group G] {X : Type u} [MulAction G X] (x : X) :
    MulAction.stabilizer G x =
      (stabilizerInclusion (𝟭 (Type u)) ((𝟭 (Type u)).elementsMk X x)).range.comap
        (actionHom G X) := by
  ext g
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  exact (mem_range_stabilizerInclusion_iff (𝟭 (Type u)) ((𝟭 (Type u)).elementsMk X x)
    (actionHom G X g)).symm

/-- The set `Mˣ` of the element calculus is the underlying set of the group `(−)ˣ(M)`. -/
theorem units_underlying (M : Type) [Monoid M] :
    (forget GrpCat).obj (MonCat.units.obj (MonCat.of M)) = Algebra.Units.units (MonCat.of M) :=
  rfl

/-- The `⁻¹` of the element calculus on `Mˣ` is the inversion of the group `(−)ˣ(M)`. -/
theorem units_inverse (M : Type) [Monoid M] (u : MonCat.units.obj (MonCat.of M)) :
    ConcreteCategory.hom (C := Type) (Algebra.Units.inverse (MonCat.of M)) u = u⁻¹ :=
  rfl

/-! Separating examples: a stabilizer is a proper subgroup in general, and contains `1`. -/

/-- The transposition of `Fin 2` does not fix `0`: `Stab(0) ≠ Aut(Fin 2)`. -/
example : (Equiv.swap (0 : Fin 2) 1).toIso ∉
    (stabilizerInclusion (𝟭 Type) ((𝟭 Type).elementsMk (Fin 2) (0 : Fin 2))).range := by
  refine (mem_range_stabilizerInclusion_iff _ _ _).not.mpr ?_
  change Equiv.swap (0 : Fin 2) 1 0 ≠ 0
  decide

/-- The identity fixes every point. -/
example : (Iso.refl (Fin 2) : Aut (Fin 2)) ∈
    (stabilizerInclusion (𝟭 Type) ((𝟭 Type).elementsMk (Fin 2) (0 : Fin 2))).range := by
  exact (mem_range_stabilizerInclusion_iff _ _ _).mpr rfl

/-- Automorphisms in the selected category, applied directly rather than through
an inherited method on the underlying set. -/
def automorphismsConstruction (C : Cat.{v, u}) : Core C ⥤ GrpCat.{v} :=
  automorphisms C

/-- The stabilizer of the selected functor and pointed object, with its inclusion
into the automorphism group in the selected category. -/
def stabilizersConstruction (C : Cat.{v, u}) (U : C ⥤ Type v) :
    Core U.Elements ⥤ (LeanCategories.isMonoArrow GrpCat.{v}).FullSubcategory :=
  stabilizers U

end CasCatalogue.Algebra.Automorphisms

namespace CasCatalogue

namespace CategoryId
def coreGroups : CategoryId := ⟨"cat.core_groups"⟩
def pointedSets : CategoryId := ⟨"cat.pointed_sets"⟩
def corePointedSets : CategoryId := ⟨"cat.core_pointed_sets"⟩
end CategoryId

namespace FunctorId
def coreSetsAutomorphisms : FunctorId := ⟨"fun.core_sets.automorphisms"⟩
def coreSetsEndomorphisms : FunctorId := ⟨"fun.core_sets.endomorphisms"⟩
def coreGroupsAutomorphisms : FunctorId := ⟨"fun.core_groups.automorphisms"⟩
def coreGroupsEndomorphisms : FunctorId := ⟨"fun.core_groups.endomorphisms"⟩
def coreModulesAutomorphisms : FunctorId := ⟨"fun.core_modules_r.automorphisms"⟩
def coreModulesEndomorphisms : FunctorId := ⟨"fun.core_modules_r.endomorphisms"⟩
def pointedSetsProjection : FunctorId := ⟨"fun.pointed_sets.projection"⟩
def corePointedSetsStabilizer : FunctorId := ⟨"fun.core_pointed_sets.stabilizer"⟩
def arrowsGroupsCodomain : FunctorId := ⟨"fun.arrows_groups.codomain"⟩
end FunctorId

namespace Algebra.Automorphisms.Registration

open Algebra.Catalogue.Magmas Algebra.CatalogueRegistration Algebra.Subgroups
open Catalogue.ConstructorRegistration

universe u

def CoreGroups : CategoryExpr := .construct ConstructorId.core #[.category Groups]
def PointedSets : CategoryExpr :=
  .construct ConstructorId.elements #[.category Foundation.Sets, .functor FunctorId.setsIdentity]
def CorePointedSets : CategoryExpr := .construct ConstructorId.core #[.category PointedSets]

def CoreSetsAutExpr : FunctorExpr Constructed.CoreSets Groups :=
  .atomic FunctorId.coreSetsAutomorphisms
def CoreSetsEndExpr : FunctorExpr Constructed.CoreSets Monoids :=
  .atomic FunctorId.coreSetsEndomorphisms
def CoreGroupsAutExpr : FunctorExpr CoreGroups Groups := .atomic FunctorId.coreGroupsAutomorphisms
def CoreGroupsEndExpr : FunctorExpr CoreGroups Monoids := .atomic FunctorId.coreGroupsEndomorphisms
def CoreModulesAutExpr : FunctorExpr Modules.Rank.CoreModules Groups :=
  .atomic FunctorId.coreModulesAutomorphisms
def CoreModulesEndExpr : FunctorExpr Modules.Rank.CoreModules Monoids :=
  .atomic FunctorId.coreModulesEndomorphisms
def PointedSetsProjectionExpr : FunctorExpr PointedSets Foundation.Sets :=
  .atomic FunctorId.pointedSetsProjection
def StabilizerExpr : FunctorExpr CorePointedSets SubobjectsGroups :=
  .atomic FunctorId.corePointedSetsStabilizer
def ArrowsGroupsCodomainExpr : FunctorExpr ArrowsGroups Groups :=
  .atomic FunctorId.arrowsGroupsCodomain

noncomputable section

def coreGroupsCategory := Constructors.core Algebra.Groups.{u}
def coreGroupsRealization : CategoryRealization CoreGroups coreGroupsCategory.{u} := {}

/-- `Sets_* = Elements(𝟭 Sets)`: a set with a point. -/
def pointedSetsCategory :=
  Constructors.elements Foundation.Mathlib.Sets.{u}
    Foundation.CatalogueRegistration.setsIdentity.toFunctor
def pointedSetsRealization : CategoryRealization PointedSets pointedSetsCategory.{u} := {}
def corePointedSetsCategory := Constructors.core pointedSetsCategory.{u}
def corePointedSetsRealization :
    CategoryRealization CorePointedSets corePointedSetsCategory.{u} := {}

/-- `Aut : Core(Sets) ⥤ Grp`, the symmetric groups. -/
def coreSetsAutDeclaration : coreSetsCategory.{u} ⥤ Algebra.Groups.{u} :=
  automorphisms (Type u)
def coreSetsAutRealization :
    FunctorRealization CoreSetsAutExpr coreSetsCategory.{u} Algebra.Groups.{u}
      coreSetsAutDeclaration :=
  { sourceRealization := coreSetsRealization, targetRealization := groupsRealization }
/-- `End : Core(Sets) ⥤ Mon`. -/
def coreSetsEndDeclaration : coreSetsCategory.{u} ⥤ Algebra.Monoids.{u} :=
  endomorphisms (Type u)
def coreSetsEndRealization :
    FunctorRealization CoreSetsEndExpr coreSetsCategory.{u} Algebra.Monoids.{u}
      coreSetsEndDeclaration :=
  { sourceRealization := coreSetsRealization, targetRealization := monoidsRealization }
/-- `Aut(X) = End(X)ˣ` for sets. -/
def coreSetsAutUnits :
    coreSetsAutDeclaration.{u} ≅ coreSetsEndDeclaration.{u} ⋙ Algebra.Units.unitsDeclaration.{u} :=
  automorphismsIsoUnits (Type u)

/-- `Aut : Core(Grp) ⥤ Grp`. -/
def coreGroupsAutDeclaration : coreGroupsCategory.{u} ⥤ Algebra.Groups.{u} :=
  automorphisms GrpCat.{u}
def coreGroupsAutRealization :
    FunctorRealization CoreGroupsAutExpr coreGroupsCategory.{u} Algebra.Groups.{u}
      coreGroupsAutDeclaration :=
  { sourceRealization := coreGroupsRealization, targetRealization := groupsRealization }
/-- `End : Core(Grp) ⥤ Mon`. -/
def coreGroupsEndDeclaration : coreGroupsCategory.{u} ⥤ Algebra.Monoids.{u} :=
  endomorphisms GrpCat.{u}
def coreGroupsEndRealization :
    FunctorRealization CoreGroupsEndExpr coreGroupsCategory.{u} Algebra.Monoids.{u}
      coreGroupsEndDeclaration :=
  { sourceRealization := coreGroupsRealization, targetRealization := monoidsRealization }
/-- `Aut(G) = End(G)ˣ` for groups. -/
def coreGroupsAutUnits :
    coreGroupsAutDeclaration.{u} ≅ coreGroupsEndDeclaration.{u} ⋙ Algebra.Units.unitsDeclaration.{u} :=
  automorphismsIsoUnits GrpCat.{u}

/-- `Aut : Core(Mod_R) ⥤ Grp`, `M ↦ GL(M)`. -/
def coreModulesAutDeclaration (R : RingCat.{u}) :
    Modules.Rank.coreModulesCategory R ⥤ Algebra.Groups.{u} :=
  automorphisms (ModuleCat.{u} R)
def coreModulesAutRealization (R : RingCat.{u}) :
    FunctorRealization CoreModulesAutExpr (Modules.Rank.coreModulesCategory R) Algebra.Groups.{u}
      (coreModulesAutDeclaration R) :=
  { sourceRealization := Modules.Rank.coreModulesRealization R
    targetRealization := groupsRealization }
/-- `End : Core(Mod_R) ⥤ Mon`. -/
def coreModulesEndDeclaration (R : RingCat.{u}) :
    Modules.Rank.coreModulesCategory R ⥤ Algebra.Monoids.{u} :=
  endomorphisms (ModuleCat.{u} R)
def coreModulesEndRealization (R : RingCat.{u}) :
    FunctorRealization CoreModulesEndExpr (Modules.Rank.coreModulesCategory R)
      Algebra.Monoids.{u} (coreModulesEndDeclaration R) :=
  { sourceRealization := Modules.Rank.coreModulesRealization R
    targetRealization := monoidsRealization }
/-- `GL(M) = End_R(M)ˣ`. -/
def coreModulesAutUnits (R : RingCat.{u}) :
    coreModulesAutDeclaration R ≅ coreModulesEndDeclaration R ⋙ Algebra.Units.unitsDeclaration.{u} :=
  automorphismsIsoUnits (ModuleCat.{u} R)

/-- `π : Sets_* ⥤ Sets`, forgetting the point. -/
def pointedSetsProjectionDeclaration : pointedSetsCategory.{u} ⥤ Foundation.Mathlib.Sets.{u} :=
  CategoryOfElements.π _
def pointedSetsProjectionRealization :
    FunctorRealization PointedSetsProjectionExpr pointedSetsCategory.{u}
      Foundation.Mathlib.Sets.{u} pointedSetsProjectionDeclaration :=
  { sourceRealization := pointedSetsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

/-- `Stab : Core(Sets_*) ⥤ Subobjects(Grp)`, `(X, x) ↦ (Stab(x) ↪ Aut(X))`. -/
def stabilizerDeclaration : corePointedSetsCategory.{u} ⥤ subobjectsGroupsCategory.{u} :=
  stabilizers Foundation.CatalogueRegistration.setsIdentity.toFunctor
def stabilizerRealization :
    FunctorRealization StabilizerExpr corePointedSetsCategory.{u} subobjectsGroupsCategory.{u}
      stabilizerDeclaration :=
  { sourceRealization := corePointedSetsRealization
    targetRealization := subobjectsGroupsRealization }

/-- The codomain of an arrow of groups. -/
def arrowsGroupsCodomainDeclaration : arrowsGroupsCategory.{u} ⥤ Algebra.Groups.{u} :=
  Arrow.rightFunc
def arrowsGroupsCodomainRealization :
    FunctorRealization ArrowsGroupsCodomainExpr arrowsGroupsCategory.{u} Algebra.Groups.{u}
      arrowsGroupsCodomainDeclaration :=
  { sourceRealization := arrowsGroupsRealization, targetRealization := groupsRealization }

/-- The ambient group of the stabilizer of `x ∈ X` is `Aut(X)`. -/
def stabilizerAmbient :
    stabilizerDeclaration.{u} ⋙ inclusionDeclaration.{u} ⋙ arrowsGroupsCodomainDeclaration.{u} ≅
      Constructors.coreMap pointedSetsProjectionDeclaration.{u} ⋙ coreSetsAutDeclaration.{u} :=
  stabilizersCodomainIso Foundation.CatalogueRegistration.setsIdentity.toFunctor

end

end Algebra.Automorphisms.Registration

open Algebra.Automorphisms.Registration Algebra.Catalogue.Magmas

normalized_registry .method
  { id := ⟨"meth.units"⟩, name := "units", owner := Monoids
    functor := FunctorId.monoidsUnits, shape := .object }

normalized_registry .category
  { id := CategoryId.coreGroups
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreGroupsCategory
    expression := CoreGroups
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.coreGroupsRealization }
normalized_registry .category
  { id := CategoryId.pointedSets
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.pointedSetsCategory
    expression := PointedSets
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.pointedSetsRealization }
normalized_registry .category
  { id := CategoryId.corePointedSets
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.corePointedSetsCategory
    expression := CorePointedSets
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.corePointedSetsRealization }

normalized_registry .functor
  { id := FunctorId.coreSetsAutomorphisms, source := Constructed.CoreSets, target := Groups
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreSetsAutDeclaration
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.coreSetsAutRealization
    expression := CoreSetsAutExpr }
normalized_registry .functor
  { id := FunctorId.coreSetsEndomorphisms, source := Constructed.CoreSets, target := Monoids
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreSetsEndDeclaration
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.coreSetsEndRealization
    expression := CoreSetsEndExpr }
normalized_registry .cell
  { id := ⟨"cell.core_sets.automorphisms_units"⟩, source := Constructed.CoreSets, target := Groups
    left := #[.functor FunctorId.coreSetsAutomorphisms]
    right := #[.functor FunctorId.coreSetsEndomorphisms, .functor FunctorId.monoidsUnits]
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreSetsAutUnits
    invertible := true }

normalized_registry .functor
  { id := FunctorId.coreGroupsAutomorphisms, source := CoreGroups, target := Groups
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreGroupsAutDeclaration
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.coreGroupsAutRealization
    expression := CoreGroupsAutExpr }
normalized_registry .functor
  { id := FunctorId.coreGroupsEndomorphisms, source := CoreGroups, target := Monoids
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreGroupsEndDeclaration
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.coreGroupsEndRealization
    expression := CoreGroupsEndExpr }
normalized_registry .cell
  { id := ⟨"cell.core_groups.automorphisms_units"⟩, source := CoreGroups, target := Groups
    left := #[.functor FunctorId.coreGroupsAutomorphisms]
    right := #[.functor FunctorId.coreGroupsEndomorphisms, .functor FunctorId.monoidsUnits]
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreGroupsAutUnits
    invertible := true }

normalized_registry .functor
  { id := FunctorId.coreModulesAutomorphisms, source := Modules.Rank.CoreModules, target := Groups
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreModulesAutDeclaration
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.coreModulesAutRealization
    expression := CoreModulesAutExpr }
normalized_registry .functor
  { id := FunctorId.coreModulesEndomorphisms, source := Modules.Rank.CoreModules
    target := Monoids
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreModulesEndDeclaration
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.coreModulesEndRealization
    expression := CoreModulesEndExpr }
normalized_registry .cell
  { id := ⟨"cell.core_modules_r.automorphisms_units"⟩, source := Modules.Rank.CoreModules
    target := Groups
    left := #[.functor FunctorId.coreModulesAutomorphisms]
    right := #[.functor FunctorId.coreModulesEndomorphisms, .functor FunctorId.monoidsUnits]
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.coreModulesAutUnits
    invertible := true }

normalized_registry .functor
  { id := FunctorId.pointedSetsProjection, source := PointedSets, target := Foundation.Sets
    declaration :=
      `CasCatalogue.Algebra.Automorphisms.Registration.pointedSetsProjectionDeclaration
    realization :=
      `CasCatalogue.Algebra.Automorphisms.Registration.pointedSetsProjectionRealization
    expression := PointedSetsProjectionExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.corePointedSetsStabilizer, source := CorePointedSets
    target := Algebra.Subgroups.SubobjectsGroups
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.stabilizerDeclaration
    realization := `CasCatalogue.Algebra.Automorphisms.Registration.stabilizerRealization
    expression := StabilizerExpr }
normalized_registry .functor
  { id := FunctorId.arrowsGroupsCodomain, source := Algebra.Subgroups.ArrowsGroups
    target := Groups
    declaration :=
      `CasCatalogue.Algebra.Automorphisms.Registration.arrowsGroupsCodomainDeclaration
    realization :=
      `CasCatalogue.Algebra.Automorphisms.Registration.arrowsGroupsCodomainRealization
    expression := ArrowsGroupsCodomainExpr }
normalized_registry .cell
  { id := ⟨"cell.core_pointed_sets.stabilizer_ambient"⟩, source := CorePointedSets
    target := Groups
    left := #[.functor FunctorId.corePointedSetsStabilizer,
      .functor FunctorId.subobjectsGroupsInclusion, .functor FunctorId.arrowsGroupsCodomain]
    right := #[.constructMap ConstructorId.core (.functor FunctorId.pointedSetsProjection),
      .functor FunctorId.coreSetsAutomorphisms]
    declaration := `CasCatalogue.Algebra.Automorphisms.Registration.stabilizerAmbient
    invertible := true }

end CasCatalogue

namespace CasCatalogue

normalized_registry .construction
  { id := ⟨"con.automorphisms"⟩, name := "Aut"
    declaration := `CasCatalogue.Algebra.Automorphisms.automorphismsConstruction
    target := Algebra.Catalogue.Magmas.Groups }

normalized_registry .construction
  { id := ⟨"con.stabilizers"⟩, name := "Stab"
    declaration := `CasCatalogue.Algebra.Automorphisms.stabilizersConstruction
    target := Algebra.Subgroups.SubobjectsGroups }

end CasCatalogue
