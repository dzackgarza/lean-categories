/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.Cofibered
public import LeanCategories.ForMathlib.GrothendieckCocartesian

@[expose] public section

/-!
# Fibred fibrations over a Grothendieck construction

FOUNDATIONS Proposition 31.2b. Let `α : F ⟶ G` be a strong transformation of pseudofunctors
`LocallyDiscrete 𝒮 ⥤ᵖ Cat`, and `P = Pseudofunctor.Grothendieck.map α : ∫ F ⥤ ∫ G`.

* `isStronglyCocartesian_map_mk`: a morphism `⟨f, ψ⟩ : ⟨c, a⟩ ⟶ ⟨c', b⟩` of `∫ F` is strongly
  `P`-cocartesian as soon as every transport `F h ψ` (`h : c' ⟶ c''`) is strongly
  `α_{c''}`-cocartesian.
* `isCofibered_map`: if every component `α_c` is a cocartesian fibration and every transport
  `F h` preserves strongly `α`-cocartesian morphisms, then `P` is a cocartesian fibration
  (Hermida,
  *Some properties of Fib as a fibred 2-category*, JPAA 134 (1999), §1; the dual of the
  statement for cartesian fibrations).

No indexed Lean source states either result (formalization-corpus searches
`Grothendieck.map cocartesian`, `fibred fibration Grothendieck`,
`IsCocartesianFibration Grothendieck map`, `strong transformation Grothendieck map fibration`,
`IsStronglyCocartesian map pseudonatural`, `fibration of fibrations`,
`Grothendieck map preserves cartesian`; the nearest hits, UniMath's displayed-bicategory
Grothendieck construction and `sinhp/LeanFibredCategories`, state neither). Recorded in
COMPLAINTS.md (LC-11) as an upstream candidate. The projection `forget F` is itself a
cocartesian fibration (`isCofibered_forget`), from the canonical lifts of
`GrothendieckCocartesian.lean`.
-/

namespace CategoryTheory.Pseudofunctor.Grothendieck

open CategoryTheory.Functor Category Bicategory StrongTrans

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F G : LocallyDiscrete 𝒮 ⥤ᵖ Cat.{v₂, u₂}}
  (α : F ⟶ G)

set_option backward.isDefEq.respectTransparency false in
/-- The component form of `StrongTrans.naturality_comp_inv` used below: the transport of a
fibre morphism of `∫ G` along `h`, after `(α.naturality f).inv`, matches
`(α.naturality (f ≫ h)).inv`. -/
lemma naturality_comp_inv_app_eq {c c' c'' : 𝒮} (f : c ⟶ c') (h : c' ⟶ c'')
    (a : F.obj ⟨c⟩) :
    (α.naturality (f.toLoc ≫ h.toLoc)).inv.toNatTrans.app a =
      (G.mapComp f.toLoc h.toLoc).hom.toNatTrans.app ((α.app ⟨c⟩).toFunctor.obj a) ≫
        (G.map h.toLoc).toFunctor.map ((α.naturality f.toLoc).inv.toNatTrans.app a) ≫
        (α.naturality h.toLoc).inv.toNatTrans.app ((F.map f.toLoc).toFunctor.obj a) ≫
        (α.app ⟨c''⟩).toFunctor.map ((F.mapComp f.toLoc h.toLoc).inv.toNatTrans.app a) := by
  rw [StrongTrans.naturality_comp_inv_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism `φ` of `∫ F` whose fibre part stays strongly `α`-cocartesian under every
transport `F h` is strongly cocartesian for `Grothendieck.map α`. -/
lemma isStronglyCocartesian_map {x y : ∫ F} (φ : x ⟶ y)
    (hφ : ∀ {c'' : 𝒮} (h : y.base ⟶ c''), IsStronglyCocartesian (α.app ⟨c''⟩).toFunctor
      ((α.app ⟨c''⟩).toFunctor.map ((F.map h.toLoc).toFunctor.map φ.fiber))
      ((F.map h.toLoc).toFunctor.map φ.fiber)) :
    IsStronglyCocartesian (map α) ((map α).map φ) φ where
  universal_property' {b'} g φ' _ := by
    have hφ' := (IsHomLift.eq_of_isHomLift (map α) ((map α).map φ ≫ g) φ').symm
    rcases x with ⟨c, a⟩
    rcases y with ⟨c', b⟩
    rcases b' with ⟨c'', b'⟩
    rcases φ with ⟨f, ψ⟩
    rcases g with ⟨h, γ⟩
    rcases φ' with ⟨k, θ⟩
    obtain ⟨hk, hθ⟩ := (Hom.ext_iff _ _).1 hφ'
    simp only [map_map_base, categoryStruct_comp_base] at hk
    subst hk
    simp at hθ
    rw [naturality_comp_inv_app_eq, assoc, assoc] at hθ
    have hθ' := (cancel_epi _).1 hθ
    simp only [assoc] at hθ'
    have hθ'' := (cancel_epi _).1 hθ'
    have hnat := (α.naturality h.toLoc).inv.toNatTrans.naturality ψ
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.comp_obj] at hnat
    have hlift : (α.app ⟨c''⟩).toFunctor.map
        ((F.mapComp f.toLoc h.toLoc).inv.toNatTrans.app a ≫ θ) =
        (α.app ⟨c''⟩).toFunctor.map ((F.map h.toLoc).toFunctor.map ψ) ≫
          ((α.naturality h.toLoc).hom.toNatTrans.app b ≫ γ) := by
      rw [Functor.map_comp, ← cancel_epi ((α.naturality h.toLoc).inv.toNatTrans.app
        ((F.map f.toLoc).toFunctor.obj a)), hθ'']
      erw [← reassoc_of% hnat]
      simp
    have := hφ h
    have : IsHomLift (α.app ⟨c''⟩).toFunctor
        ((α.app ⟨c''⟩).toFunctor.map ((F.map h.toLoc).toFunctor.map ψ) ≫
          ((α.naturality h.toLoc).hom.toNatTrans.app b ≫ γ))
        ((F.mapComp f.toLoc h.toLoc).inv.toNatTrans.app a ≫ θ) := by
      rw [← hlift]
      infer_instance
    obtain ⟨κ, ⟨hκlift, hκfac⟩, hκuniq⟩ := IsStronglyCocartesian.universal_property'
      (p := (α.app ⟨c''⟩).toFunctor) (f := (α.app ⟨c''⟩).toFunctor.map
        ((F.map h.toLoc).toFunctor.map ψ)) (φ := (F.map h.toLoc).toFunctor.map ψ)
      ((α.naturality h.toLoc).hom.toNatTrans.app b ≫ γ)
      ((F.mapComp f.toLoc h.toLoc).inv.toNatTrans.app a ≫ θ)
    have hακ := (IsHomLift.eq_of_isHomLift (α.app ⟨c''⟩).toFunctor
      ((α.naturality h.toLoc).hom.toNatTrans.app b ≫ γ) κ).symm
    have hmap : (map α).map (show (⟨c', b⟩ : ∫ F) ⟶ ⟨c'', b'⟩ from ⟨h, κ⟩) = ⟨h, γ⟩ := by
      ext
      · rfl
      · simp [hακ]
    refine ⟨⟨h, κ⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [← hmap]
      infer_instance
    · ext
      · rfl
      · simp [hκfac]
    · rintro ⟨h', κ'⟩ ⟨hl, hfac⟩
      have hl' := IsHomLift.eq_of_isHomLift (map α)
        (show (map α).obj ⟨c', b⟩ ⟶ (map α).obj ⟨c'', b'⟩ from ⟨h, γ⟩)
        (show (⟨c', b⟩ : ∫ F) ⟶ ⟨c'', b'⟩ from ⟨h', κ'⟩)
      obtain ⟨hh, hκ'⟩ := (Hom.ext_iff _ _).1 hl'
      simp only [map_map_base] at hh
      subst hh
      simp at hκ'
      have hακ' : (α.app ⟨c''⟩).toFunctor.map κ' =
          (α.naturality h.toLoc).hom.toNatTrans.app b ≫ γ := by
        simp [hκ']
      obtain ⟨_, hfac'⟩ := (Hom.ext_iff _ _).1 hfac
      simp only [categoryStruct_comp_fiber, eqToHom_refl, id_comp] at hfac'
      have : IsHomLift (α.app ⟨c''⟩).toFunctor
          ((α.naturality h.toLoc).hom.toNatTrans.app b ≫ γ) κ' := by
        rw [← hακ']
        infer_instance
      rw [hκuniq κ' ⟨this, by simp [← hfac']⟩]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If every component `α_c` is a cocartesian fibration and every transport `F h` preserves
strongly `α`-cocartesian morphisms, then every morphism out of the image of an object under
`Grothendieck.map α` has a strongly cocartesian lift. -/
theorem exists_isStronglyCocartesian_map
    [∀ c : 𝒮, (α.app ⟨c⟩).toFunctor.IsCofibered]
    (hpres : ∀ {c c' : 𝒮} (h : c ⟶ c') {a b : F.obj ⟨c⟩} (ψ : a ⟶ b),
      IsStronglyCocartesian (α.app ⟨c⟩).toFunctor ((α.app ⟨c⟩).toFunctor.map ψ) ψ →
      IsStronglyCocartesian (α.app ⟨c'⟩).toFunctor
        ((α.app ⟨c'⟩).toFunctor.map ((F.map h.toLoc).toFunctor.map ψ))
        ((F.map h.toLoc).toFunctor.map ψ))
    {x : ∫ F} {y : ∫ G} (u : (map α).obj x ⟶ y) :
    ∃ (z : ∫ F) (φ : x ⟶ z), IsStronglyCocartesian (map α) u φ := by
  rcases x with ⟨c, a⟩
  rcases y with ⟨c', w⟩
  rcases u with ⟨f, β⟩
  obtain ⟨b, ψ, hψ⟩ := IsCofibered.exists_isStronglyCocartesian (α.app ⟨c'⟩).toFunctor
    ((α.naturality f.toLoc).hom.toNatTrans.app a ≫ β)
  have hobj : (α.app ⟨c'⟩).toFunctor.obj b = w :=
    IsHomLift.codomain_eq (α.app ⟨c'⟩).toFunctor
      ((α.naturality f.toLoc).hom.toNatTrans.app a ≫ β) ψ
  subst hobj
  have hβ := (IsHomLift.eq_of_isHomLift (α.app ⟨c'⟩).toFunctor
    ((α.naturality f.toLoc).hom.toNatTrans.app a ≫ β) ψ).symm
  have hψ' : IsStronglyCocartesian (α.app ⟨c'⟩).toFunctor
      ((α.app ⟨c'⟩).toFunctor.map ψ) ψ := by
    rw [hβ]
    exact hψ
  refine ⟨⟨c', b⟩, ⟨f, ψ⟩, ?_⟩
  have hmap : (map α).map (show (⟨c, a⟩ : ∫ F) ⟶ ⟨c', b⟩ from ⟨f, ψ⟩) = ⟨f, β⟩ := by
    ext
    · rfl
    · simp [hβ]
  rw [← hmap]
  exact isStronglyCocartesian_map α _ fun h ↦ hpres h ψ hψ'

/-- FOUNDATIONS Proposition 31.2b: `Grothendieck.map α` is a cocartesian fibration when every
component `α_c` is one and every transport `F h` preserves strongly `α`-cocartesian
morphisms. -/
theorem isCofibered_map [∀ c : 𝒮, (α.app ⟨c⟩).toFunctor.IsCofibered]
    (hpres : ∀ {c c' : 𝒮} (h : c ⟶ c') {a b : F.obj ⟨c⟩} (ψ : a ⟶ b),
      IsStronglyCocartesian (α.app ⟨c⟩).toFunctor ((α.app ⟨c⟩).toFunctor.map ψ) ψ →
      IsStronglyCocartesian (α.app ⟨c'⟩).toFunctor
        ((α.app ⟨c'⟩).toFunctor.map ((F.map h.toLoc).toFunctor.map ψ))
        ((F.map h.toLoc).toFunctor.map ψ)) :
    (map α).IsCofibered :=
  IsCofibered.of_exists_isStronglyCocartesian fun _ _ u ↦
    exists_isStronglyCocartesian_map α hpres u

end CategoryTheory.Pseudofunctor.Grothendieck
