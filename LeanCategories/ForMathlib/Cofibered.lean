/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# Cocartesian fibrations

The dual of `Mathlib.CategoryTheory.FiberedCategory.Fibered`: a functor `p : 𝒳 ⥤ 𝒮` is
*precofibered* if every morphism `p a ⟶ S` has a cocartesian lift with domain `a`, and
*cofibered* (a cocartesian fibration, SGA 1 VI.10) if moreover cocartesian morphisms are closed
under composition. As for fibered categories, cocartesian morphisms of a cofibered functor are
strongly cocartesian, and existence of strongly cocartesian lifts characterizes cofibered
functors (`IsCofibered.of_exists_isStronglyCocartesian`).

Mathlib states only the cartesian side (`Functor.IsPreFibered`, `Functor.IsFibered`); no indexed
Lean source states the cocartesian predicate against Mathlib's `IsCocartesian` API
(formalization-corpus searches `IsCofibered`, `IsPreCofibered`,
`cocartesian fibration class Functor`; the hits in UniMath, 1lab and `sinhp/HoTTLean` use
their own displayed-category encodings). The declarations and proofs below are the duals of
Mathlib's, line by line. Upstream candidate; recorded in COMPLAINTS.md (LC-11).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Functor Category IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

namespace Functor.IsCocartesian

variable (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCocartesian p f φ]

instance codomainUniqueUpToIso_hom_isHomLift {b' : 𝒳} (φ' : a ⟶ b')
    [IsCocartesian p f φ'] : IsHomLift p (𝟙 S) (codomainUniqueUpToIso p f φ φ').hom :=
  IsCocartesian.map_isHomLift p f φ φ'

instance codomainUniqueUpToIso_inv_isHomLift {b' : 𝒳} (φ' : a ⟶ b')
    [IsCocartesian p f φ'] : IsHomLift p (𝟙 S) (codomainUniqueUpToIso p f φ φ').inv :=
  IsCocartesian.map_isHomLift p f φ' φ

end Functor.IsCocartesian

/-- A functor is precofibered if every morphism out of the image of an object has a cocartesian
lift. Dual of `Functor.IsPreFibered`. -/
class Functor.IsPreCofibered (p : 𝒳 ⥤ 𝒮) : Prop where
  exists_isCocartesian' {a : 𝒳} {S : 𝒮} (f : p.obj a ⟶ S) :
    ∃ (b : 𝒳) (φ : a ⟶ b), IsCocartesian p f φ

protected lemma IsPreCofibered.exists_isCocartesian (p : 𝒳 ⥤ 𝒮) [p.IsPreCofibered] {a : 𝒳}
    {R S : 𝒮} (ha : p.obj a = R) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : a ⟶ b), IsCocartesian p f φ := by
  subst ha; exact IsPreCofibered.exists_isCocartesian' f

/-- A cocartesian fibration: a precofibered functor whose cocartesian morphisms are closed under
composition. Dual of `Functor.IsFibered`. -/
class Functor.IsCofibered (p : 𝒳 ⥤ 𝒮) : Prop extends IsPreCofibered p where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCocartesian p f φ] [IsCocartesian p g ψ] : IsCocartesian p (f ≫ g) (φ ≫ ψ)

instance (p : 𝒳 ⥤ 𝒮) [p.IsCofibered] {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳}
    (φ : a ⟶ b) (ψ : b ⟶ c) [IsCocartesian p f φ] [IsCocartesian p g ψ] :
    IsCocartesian p (f ≫ g) (φ ≫ ψ) :=
  IsCofibered.comp f g φ ψ

namespace Functor.IsPreCofibered

variable {p : 𝒳 ⥤ 𝒮} [IsPreCofibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = R) (f : R ⟶ S)

/-- The codomain of a chosen cocartesian lift of `f` with domain `a`. -/
noncomputable def pushforwardObj : 𝒳 :=
  Classical.choose (IsPreCofibered.exists_isCocartesian p ha f)

/-- A chosen cocartesian lift of `f` with domain `a`. -/
noncomputable def pushforwardMap : a ⟶ pushforwardObj ha f :=
  Classical.choose (Classical.choose_spec (IsPreCofibered.exists_isCocartesian p ha f))

instance pushforwardMap.IsCocartesian : IsCocartesian p f (pushforwardMap ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreCofibered.exists_isCocartesian p ha f))

lemma pushforwardObj_proj : p.obj (pushforwardObj ha f) = S :=
  codomain_eq p f (pushforwardMap ha f)

end Functor.IsPreCofibered

namespace Functor.IsCofibered

open IsCocartesian Functor.IsPreCofibered

/-- In a cocartesian fibration, any cocartesian morphism is strongly cocartesian. -/
instance isStronglyCocartesian_of_isCocartesian (p : 𝒳 ⥤ 𝒮) [p.IsCofibered] {R S : 𝒮}
    (f : R ⟶ S) {a b : 𝒳} (φ : a ⟶ b) [p.IsCocartesian f φ] : p.IsStronglyCocartesian f φ where
  universal_property' g φ' hφ' := by
    let ψ := pushforwardMap (codomain_eq p f φ) g
    let τ := IsCocartesian.map p (f ≫ g) (φ ≫ ψ) φ'
    use ψ ≫ τ
    refine ⟨⟨inferInstance, by simp only [← assoc, IsCocartesian.fac, τ]⟩, ?_⟩
    intro π ⟨hπ, hπ_comp⟩
    rw [← fac p g ψ π]
    congr 1
    apply map_uniq
    rwa [assoc, IsCocartesian.fac]

/-- If every morphism out of the image of an object has a strongly cocartesian lift, then every
cocartesian morphism is strongly cocartesian. -/
lemma isStronglyCocartesian_of_exists_isCocartesian (p : 𝒳 ⥤ 𝒮) (h : ∀ (a : 𝒳) (S : 𝒮)
    (f : p.obj a ⟶ S), ∃ (b : 𝒳) (φ : a ⟶ b), IsStronglyCocartesian p f φ) {R S : 𝒮}
    (f : R ⟶ S) {a b : 𝒳} (φ : a ⟶ b) [p.IsCocartesian f φ] : p.IsStronglyCocartesian f φ := by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  obtain ⟨b', ψ, hψ⟩ := h _ _ (p.map φ)
  let τ' := IsStronglyCocartesian.map p (p.map φ) ψ (f' := p.map φ ≫ g) rfl φ'
  let Φ := codomainUniqueUpToIso p (p.map φ) φ ψ
  use Φ.hom ≫ τ'
  refine ⟨⟨by simp only [Φ]; infer_instance, ?_⟩, ?_⟩
  · simp [τ', Φ, codomainUniqueUpToIso]
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.inv_comp_eq]
  apply IsStronglyCocartesian.map_uniq p (p.map φ) ψ rfl φ'
  simp [hπ_comp, Φ, codomainUniqueUpToIso]

/-- A functor with strongly cocartesian lifts of every morphism out of the image of an object is
a cocartesian fibration. Dual of `Functor.IsFibered.of_exists_isStronglyCartesian`. -/
lemma of_exists_isStronglyCocartesian {p : 𝒳 ⥤ 𝒮}
    (h : ∀ (a : 𝒳) (S : 𝒮) (f : p.obj a ⟶ S),
      ∃ (b : 𝒳) (φ : a ⟶ b), IsStronglyCocartesian p f φ) :
    IsCofibered p where
  exists_isCocartesian' := by
    intro a S f
    obtain ⟨b, φ, hφ⟩ := h a S f
    refine ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCocartesian f φ := isStronglyCocartesian_of_exists_isCocartesian p h _ _
    have : p.IsStronglyCocartesian g ψ := isStronglyCocartesian_of_exists_isCocartesian p h _ _
    inferInstance

/-- In a cocartesian fibration, every morphism out of the image of an object has a strongly
cocartesian lift. -/
lemma exists_isStronglyCocartesian (p : 𝒳 ⥤ 𝒮) [p.IsCofibered] {a : 𝒳} {S : 𝒮}
    (f : p.obj a ⟶ S) : ∃ (b : 𝒳) (φ : a ⟶ b), IsStronglyCocartesian p f φ := by
  obtain ⟨b, φ, _⟩ := IsPreCofibered.exists_isCocartesian' (p := p) f
  exact ⟨b, φ, inferInstance⟩

end Functor.IsCofibered

section Transfer

universe v₃ v₄ u₃ u₄

variable {𝒮' : Type u₃} {𝒳' : Type u₄} [Category.{v₃} 𝒮'] [Category.{v₄} 𝒳']
  (p : 𝒳 ⥤ 𝒮) (p' : 𝒳' ⥤ 𝒮') (Φ : 𝒳 ⥤ 𝒳') (Ψ : 𝒮 ⥤ 𝒮') (e : Φ ⋙ p' = p ⋙ Ψ)

include e in
/-- A functor over `Ψ` sends lifts of `f` to lifts of `Ψ f`. Generalizes Mathlib's
`BasedFunctor.preserves_isHomLift`, which is the case `Ψ = 𝟭 𝒮`. -/
lemma Functor.IsHomLift.map_of_comm {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p f φ] :
    IsHomLift p' (Ψ.map f) (Φ.map φ) := by
  subst_hom_lift p f φ
  exact IsHomLift.of_fac p' _ _ (Functor.congr_obj e _) (Functor.congr_obj e _)
    (by rw [← Functor.comp_map Φ p', Functor.congr_hom e φ]; simp)

include e in
/-- Transfer of strongly cocartesian morphisms: if a functor `Φ` over `Ψ` sends one strongly
cocartesian lift of every morphism to a strongly cocartesian morphism, then it sends every
strongly cocartesian morphism to a strongly cocartesian morphism. Every strongly cocartesian lift
differs from the chosen one by a vertical isomorphism (`codomainUniqueUpToIso`), which `Φ` keeps
vertical and invertible. -/
lemma Functor.IsStronglyCocartesian.map_of_exists
    (hlift : ∀ (a : 𝒳) (S : 𝒮) (f : p.obj a ⟶ S), ∃ (b : 𝒳) (φ : a ⟶ b),
      IsStronglyCocartesian p f φ ∧ IsStronglyCocartesian p' (Ψ.map f) (Φ.map φ))
    {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳} (φ : a ⟶ b) [IsStronglyCocartesian p f φ] :
    IsStronglyCocartesian p' (Ψ.map f) (Φ.map φ) := by
  obtain rfl := IsHomLift.domain_eq p f φ
  obtain ⟨b₀, φ₀, h₀, h₀'⟩ := hlift a S f
  let ι := IsCocartesian.codomainUniqueUpToIso p f φ₀ φ
  have hfac : φ₀ ≫ ι.hom = φ := IsCocartesian.fac p f φ₀ φ
  have : IsHomLift p' (Ψ.map (𝟙 S)) (Φ.map ι.hom) :=
    IsHomLift.map_of_comm p p' Φ Ψ e (𝟙 S) ι.hom
  have : IsStronglyCocartesian p' (Ψ.map (𝟙 S)) (Φ.map ι.hom) :=
    IsStronglyCocartesian.of_isIso p' _ (Φ.map ι.hom)
  have : IsStronglyCocartesian p' (Ψ.map f ≫ Ψ.map (𝟙 S)) (Φ.map φ₀ ≫ Φ.map ι.hom) :=
    inferInstance
  rw [← hfac, Φ.map_comp]
  simpa using this

end Transfer

end CategoryTheory
