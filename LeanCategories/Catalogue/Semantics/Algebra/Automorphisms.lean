/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Subgroups
public import LeanCategories.Catalogue.Semantics.Algebra.Ports
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Conj
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

/-!
# Group-valued constructions: automorphisms, units, stabilizers (draft)
-/

open CategoryTheory

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
    simp only [Iso.refl_hom, Category.id_comp]
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

end CasCatalogue.Algebra.Automorphisms
