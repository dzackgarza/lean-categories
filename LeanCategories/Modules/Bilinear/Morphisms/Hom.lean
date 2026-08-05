module

public import LeanCategories.Modules.Bilinear.Objects.Basic

@[expose] public section

namespace LeanCategories.Modules.Bilinear

open CategoryTheory

universe u v

/-- Form-preserving linear maps B_N(fx, fy) = B_M(x, y). -/
structure Hom {R : Type u} [CommRing R] (L M : SymmBilinModuleCat.{u, v} R) where
  toLinearMap : L.carrier →ₗ[R] M.carrier
  map_form : ∀ x y, M.form (toLinearMap x) (toLinearMap y) = L.form x y

/-- Identity morphism in SymmBilinModuleCat R. -/
def Hom.id {R : Type u} [CommRing R] (L : SymmBilinModuleCat.{u, v} R) : Hom L L where
  toLinearMap := LinearMap.id
  map_form _ _ := rfl

/-- Composition of morphisms in SymmBilinModuleCat R. -/
def Hom.comp {R : Type u} [CommRing R] {L M N : SymmBilinModuleCat.{u, v} R} (g : Hom M N) (f : Hom L M) : Hom L N where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_form x y := by
    dsimp [LinearMap.comp_apply]
    rw [g.map_form, f.map_form]

/-- CategoryTheory instance for SymmBilinModuleCat R. -/
instance (R : Type u) [CommRing R] : Category (SymmBilinModuleCat.{u, v} R) where
  Hom L M := Hom L M
  id L := Hom.id L
  comp f g := Hom.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end LeanCategories.Modules.Bilinear
