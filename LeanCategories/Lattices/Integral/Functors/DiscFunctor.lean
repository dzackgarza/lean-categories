module

public import LeanCategories.Lattices.Discriminant.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

open CategoryTheory
open LeanCategories.Lattices.Discriminant

/-- Isometries between even lattices. -/
structure EvenIsometry (L M : EvenLattice) where
  equiv : L.carrier ≃ₗ[ℤ] M.carrier
  map_form : ∀ x y, M.form (equiv x) (equiv y) = L.form x y

def EvenIsometry.id (L : EvenLattice) : EvenIsometry L L where
  equiv := LinearEquiv.refl ℤ L.carrier
  map_form _ _ := rfl

def EvenIsometry.comp {L M N : EvenLattice} (g : EvenIsometry M N)
    (f : EvenIsometry L M) : EvenIsometry L N where
  equiv := f.equiv.trans g.equiv
  map_form x y := by
    change N.form (g.equiv (f.equiv x)) (g.equiv (f.equiv y)) = L.form x y
    rw [g.map_form, f.map_form]

instance : Category EvenLattice where
  Hom := EvenIsometry
  id := EvenIsometry.id
  comp f g := EvenIsometry.comp g f
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- Isometries of finite quadratic modules. -/
structure QuadraticIsometry (A B : FiniteQuadraticModule) where
  equiv : A.carrier ≃+ B.carrier
  map_quad : ∀ x, B.quadForm (equiv x) = A.quadForm x

def QuadraticIsometry.id (A : FiniteQuadraticModule) : QuadraticIsometry A A where
  equiv := AddEquiv.refl A.carrier
  map_quad _ := rfl

def QuadraticIsometry.comp {A B C : FiniteQuadraticModule} (g : QuadraticIsometry B C)
    (f : QuadraticIsometry A B) : QuadraticIsometry A C where
  equiv := f.equiv.trans g.equiv
  map_quad x := by
    change C.quadForm (g.equiv (f.equiv x)) = A.quadForm x
    rw [g.map_quad, f.map_quad]

instance : Category FiniteQuadraticModule where
  Hom := QuadraticIsometry
  id := QuadraticIsometry.id
  comp f g := QuadraticIsometry.comp g f
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- The discriminant quadratic module of an even lattice. -/
axiom discriminantModule (L : EvenLattice) : FiniteQuadraticModule

/-- Isometries descend to discriminant-form isometries. -/
axiom discriminantMap {L M : EvenLattice} (f : L ⟶ M) :
    discriminantModule L ⟶ discriminantModule M

axiom discriminantMap_id (L : EvenLattice) : discriminantMap (𝟙 L) = 𝟙 _

axiom discriminantMap_comp {L M N : EvenLattice} (f : L ⟶ M) (g : M ⟶ N) :
    discriminantMap (f ≫ g) = discriminantMap f ≫ discriminantMap g

/-- Discriminant forms as an actual functor on the isometry categories. -/
noncomputable def discriminantFunctor : EvenLattice ⥤ FiniteQuadraticModule where
  obj := discriminantModule
  map := discriminantMap
  map_id := discriminantMap_id
  map_comp := discriminantMap_comp

end LeanCategories.Lattices.Integral
