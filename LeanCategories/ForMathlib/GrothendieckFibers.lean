/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.HasFibers
public import Mathlib.CategoryTheory.Grothendieck

@[expose] public section

/-!
# Fibres of the covariant Grothendieck construction

The dual of the fibre part of `Mathlib.CategoryTheory.FiberedCategory.Grothendieck`: for a
pseudofunctor `F : LocallyDiscrete 𝒮 ⥤ᵖ Cat`, the fibre of `forget F : ∫ F ⥤ 𝒮` over `S` is
equivalent to `F S`, through the inclusion `ι F S`. Mathlib states this only for the
contravariant `CoGrothendieck` (formalization-corpus searches
`Grothendieck fiber equivalence HasFibers`, `Fiber inducedFunctor IsEquivalence Grothendieck`,
`fiber of Grothendieck construction equivalence`); the proofs below follow Mathlib's
line by line with `mapId.hom` in place of `mapId.inv`. Upstream candidate.
-/

namespace CategoryTheory.Pseudofunctor.Grothendieck

open CategoryTheory.Functor Bicategory Fiber

variable {𝒮 : Type*} [Category* 𝒮] (F : LocallyDiscrete 𝒮 ⥤ᵖ Cat) (S : 𝒮)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The inclusion of `F(S)` into `∫ F`, over `S`. -/
@[simps]
def ι : F.obj ⟨S⟩ ⥤ ∫ F where
  obj a := { base := S, fiber := a }
  map {a b} φ := { base := 𝟙 S, fiber := (F.mapId ⟨S⟩).hom.toNatTrans.app a ≫ φ }
  map_id a := by
    ext
    · simp
    · simp
  map_comp {a b c} φ ψ := by
    ext
    · simp
    · simp [F.mapComp_id_right_hom, Strict.rightUnitor_eqToIso, ← Cat.Hom₂.comp_app]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism encoding `comp_const`. -/
@[simps!]
def compIso : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨S⟩)).obj S :=
  NatIso.ofComponents (fun _ => eqToIso rfl)

lemma comp_const : (ι F S) ⋙ forget F = (const (F.obj ⟨S⟩)).obj S :=
  Functor.ext_of_iso (compIso F S) (fun _ ↦ rfl) (fun _ => rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).Full where
  map_surjective {X Y} f := by
    have hf : (fiberInclusion.map f).base = 𝟙 S := by
      simpa using (IsHomLift.fac (forget F) (𝟙 S) (fiberInclusion.map f)).symm
    use (F.mapId ⟨S⟩).inv.toNatTrans.app X ≫ eqToHom (by simp [hf]) ≫
      (fiberInclusion.map f).fiber
    ext <;> simp [hf, ← Cat.Hom₂.comp_app]

set_option backward.isDefEq.respectTransparency false in
instance : (Fiber.inducedFunctor (comp_const F S)).Faithful where
  map_injective {a b} := by
    intro f g heq
    replace heq := fiberInclusion.congr_map heq
    simpa [cancel_epi, ← Cat.Hom.toNatIso_hom,
      ← Cat.Hom.toNatIso_inv] using ((Hom.ext_iff _ _).mp heq).2

set_option backward.defeqAttrib.useBackward true in
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).EssSurj := by
  apply essSurj_of_surj
  intro Y
  have hYS : (fiberInclusion.obj Y).base = S := by simpa using! Y.2
  use hYS ▸ (fiberInclusion.obj Y).fiber
  apply fiberInclusion_obj_inj
  ext <;> simp [hYS]

noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).IsEquivalence where

/-- `HasFibers` instance for `∫ F`, where the fibre over `S` is `F.obj ⟨S⟩`. -/
noncomputable instance hasFibersForget : HasFibers (forget F) where
  Fib S := F.obj ⟨S⟩
  ι := ι F
  comp_const := comp_const F

end CategoryTheory.Pseudofunctor.Grothendieck

namespace CategoryTheory.Pseudofunctor.Grothendieck

open CategoryTheory.Functor Bicategory StrongTrans Fiber

variable {𝒮 : Type*} [Category* 𝒮] {F G : LocallyDiscrete 𝒮 ⥤ᵖ Cat} (α : F ⟶ G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The fibre inclusions commute with `Grothendieck.map α` on the nose: the component
`α_c : F(c) ⥤ G(c)` is the restriction of `map α` to the fibre over `c`. -/
theorem ι_comp_map (c : 𝒮) : ι F c ⋙ map α = (α.app ⟨c⟩).toFunctor ⋙ ι G c := by
  refine Functor.ext (fun _ ↦ rfl) fun x x' ψ ↦ ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  ext
  · rfl
  · simp [StrongTrans.naturality_id_inv_app, ← Functor.map_comp]

variable (c : 𝒮) (y : G.obj ⟨c⟩)

lemma base_eqToHom {H : LocallyDiscrete 𝒮 ⥤ᵖ Cat} {X Y : ∫ H} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Grothendieck.base h) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Each fibre inclusion is faithful. -/
instance faithful_ι (H : LocallyDiscrete 𝒮 ⥤ᵖ Cat) (c : 𝒮) : (ι H c).Faithful where
  map_injective {a b} ψ ψ' h := by
    have := Hom.congr h
    simpa [cancel_epi] using this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma fiberInclusion_ι_comp_map :
    (fiberInclusion ⋙ ι F c) ⋙ map α =
      (const (Fiber (α.app ⟨c⟩).toFunctor y)).obj (⟨c, y⟩ : ∫ G) := by
  rw [Functor.assoc, ι_comp_map, ← Functor.assoc, Fiber.fiberInclusion_comp_eq_const]
  exact Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by simp

/-- The fibre of `α_c` over `y` included in the fibre of `Grothendieck.map α` over `(c, y)`. -/
noncomputable def fibreFunctor :
    Fiber (α.app ⟨c⟩).toFunctor y ⥤ Fiber (map α) (⟨c, y⟩ : ∫ G) :=
  Fiber.inducedFunctor (fiberInclusion_ι_comp_map α c y)

instance : (fibreFunctor α c y).Faithful :=
  Functor.Faithful.of_comp_eq (Fiber.inducedFunctor_comp (fiberInclusion_ι_comp_map α c y))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (fibreFunctor α c y).EssSurj := by
  apply essSurj_of_surj
  rintro ⟨⟨c', x⟩, h⟩
  have hc : c' = c := congrArg Grothendieck.base h
  subst hc
  have hx : (α.app ⟨c'⟩).toFunctor.obj x = y := by
    exact eq_of_heq (Grothendieck.ext_iff.1 h).2
  exact ⟨⟨x, hx⟩, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (fibreFunctor α c y).Full where
  map_surjective {X Y} f := by
    have hfac := IsHomLift.fac (map α) (𝟙 (⟨c, y⟩ : ∫ G)) (fiberInclusion.map f)
    have hb : (fiberInclusion.map f).base = 𝟙 c := by
      have := congrArg Hom.base hfac
      simpa [base_eqToHom] using this.symm
    let ψ : X.1 ⟶ Y.1 := (F.mapId ⟨c⟩).inv.toNatTrans.app X.1 ≫ eqToHom (by rw [hb]; rfl) ≫
      (fiberInclusion.map f).fiber
    have hψ : (ι F c).map ψ = fiberInclusion.map f := by
      refine Hom.ext _ _ hb.symm ?_
      simp [ψ]
    have hαψ : IsHomLift (α.app ⟨c⟩).toFunctor (𝟙 y) ψ := by
      apply IsHomLift.of_fac _ _ _ X.2 Y.2
      apply (ι G c).map_injective
      have e := Functor.congr_hom (ι_comp_map α c) ψ
      simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] at e
      simp only [Functor.map_comp, eqToHom_map]
      rw [← e, hψ, Functor.map_id]
      exact hfac
    exact ⟨⟨ψ, hαψ⟩, by ext1; exact hψ⟩

noncomputable instance : (fibreFunctor α c y).IsEquivalence where

/-- FOUNDATIONS Proposition 31.2b, fibres: the fibre of `Grothendieck.map α` over `(c, y)` is
the fibre of `α_c` over `y`. -/
noncomputable def fibreEquivalence :
    Fiber (α.app ⟨c⟩).toFunctor y ≌ Fiber (map α) (⟨c, y⟩ : ∫ G) :=
  (fibreFunctor α c y).asEquivalence

end CategoryTheory.Pseudofunctor.Grothendieck

namespace CategoryTheory.Grothendieck

open CategoryTheory.Functor Fiber

variable {C : Type*} [Category* C] (F : C ⥤ Cat) (c : C)

lemma ι_comp_forget : ι F c ⋙ forget F = (const (F.obj c)).obj c :=
  Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦
    (by simp : (𝟙 c : c ⟶ c) = 𝟙 c ≫ 𝟙 c ≫ 𝟙 c)

/-- The fibre `F(c)` included in the fibre of the strict Grothendieck projection over `c`. -/
noncomputable def fibreFunctor : F.obj c ⥤ Fiber (forget F) c :=
  Fiber.inducedFunctor (ι_comp_forget F c)

instance : (fibreFunctor F c).Faithful :=
  Functor.Faithful.of_comp_eq (Fiber.inducedFunctor_comp (ι_comp_forget F c))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (fibreFunctor F c).Full where
  map_surjective {X Y} f := by
    obtain ⟨⟨b, φ⟩, hf⟩ := f
    have hb : b = 𝟙 c := by
      simpa [forget] using (IsHomLift.fac (forget F) (𝟙 c) (⟨b, φ⟩ : Hom _ _)).symm
    subst hb
    refine ⟨eqToHom (show X = (F.map (𝟙 c)).toFunctor.obj X by simp) ≫ φ, ?_⟩
    ext1
    exact Grothendieck.ext _ _ rfl (by simp [fibreFunctor]; rfl)

set_option backward.defeqAttrib.useBackward true in
noncomputable instance : (fibreFunctor F c).EssSurj := by
  apply essSurj_of_surj
  rintro ⟨⟨c', x⟩, h⟩
  have hc : c' = c := h
  subst hc
  exact ⟨x, rfl⟩

noncomputable instance : (fibreFunctor F c).IsEquivalence where

/-- The fibre of a strict Grothendieck projection over `c` is `F(c)`. -/
noncomputable def fibreEquivalence : F.obj c ≌ Fiber (forget F) c :=
  (fibreFunctor F c).asEquivalence

end CategoryTheory.Grothendieck
