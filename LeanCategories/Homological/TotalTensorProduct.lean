/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.NoncommutativeTensor
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# The total tensor-product functor on complexes

Weibel, *An Introduction to Homological Algebra* (1994), §10.6,
pp. 394--397 (FC05-C10-U068).

For a fixed bounded-above complex `A` of right `R`-modules, Weibel first
forms the ordinary functor

`B ↦ Tot^⊕(A ⊗_R B)`

on bounded-above complexes of left `R`-modules.  Its total left derived
functor is introduced only in Definition 10.6.1; this file records the
underived total-tensor functor itself.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u


variable (R : Type u) [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- Relative tensor product as a bifunctor from right and left `R`-modules to
abelian groups. -/
def relativeTensorBifunctor :
    ModuleCat Rᵐᵒᵖ ⥤ ModuleCat R ⥤ ModuleCat ℤ where
  obj A := tensorLeftFunctor R A
  map {A A'} f :=
    { app := fun B => relativeTensorMap R f (𝟙 B)
      naturality := by
        intro B B' g
        change relativeTensorMap R (𝟙 A) g ≫ relativeTensorMap R f (𝟙 B') =
          relativeTensorMap R f (𝟙 B) ≫ relativeTensorMap R (𝟙 A') g
        calc
          _ = relativeTensorMap R f g := by
            simpa using (relativeTensorMap_comp R (𝟙 A) f g (𝟙 B')).symm
          _ = _ := by
            simpa using relativeTensorMap_comp R f (𝟙 A') (𝟙 B) g }
  map_id A := by
    refine NatTrans.ext <| funext fun B => ?_
    change relativeTensorMap R (𝟙 A) (𝟙 B) = 𝟙 _
    exact relativeTensorMap_id R A B
  map_comp f g := by
    refine NatTrans.ext <| funext fun B => ?_
    change relativeTensorMap R (f ≫ g) (𝟙 B) =
      relativeTensorMap R f (𝟙 B) ≫ relativeTensorMap R g (𝟙 B)
    simpa using relativeTensorMap_comp R f g (𝟙 B) (𝟙 B)

set_option backward.isDefEq.respectTransparency false in
instance relativeTensorBifunctor_additive :
    (relativeTensorBifunctor R).Additive where
  map_add := by
    intro A A' f g
    refine NatTrans.ext <| funext fun B => ?_
    change relativeTensorMap R (f + g) (𝟙 B) =
      relativeTensorMap R f (𝟙 B) + relativeTensorMap R g (𝟙 B)
    exact relativeTensorMap_add_left (R := R) (B := B) f g

set_option backward.isDefEq.respectTransparency false in
instance relativeTensorBifunctor_obj_preservesZeroMorphisms
    (A : ModuleCat Rᵐᵒᵖ) :
    ((relativeTensorBifunctor R).obj A).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (tensorLeftFunctor R A)

/-- The direct-sum total tensor complex `Tot^⊕(A ⊗_R B)`. -/
def totalTensorComplex
    (A : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
    (B : CochainComplex (ModuleCat R) ℤ)
    [HomologicalComplex.HasMapBifunctor A B (relativeTensorBifunctor R)
      (ComplexShape.up ℤ)] :
    CochainComplex (ModuleCat ℤ) ℤ :=
  HomologicalComplex.mapBifunctor A B (relativeTensorBifunctor R)
    (ComplexShape.up ℤ)

/-- The total-tensor bifunctor on cochain complexes. -/
def totalTensorBifunctor
    [∀ (A : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
      (B : CochainComplex (ModuleCat R) ℤ),
      HomologicalComplex.HasMapBifunctor A B (relativeTensorBifunctor R)
        (ComplexShape.up ℤ)] :
    CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ ⥤
      CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat ℤ) ℤ :=
  (relativeTensorBifunctor R).map₂CochainComplex

/-- For fixed `A`, Weibel's underived total-tensor functor
`B ↦ Tot^⊕(A ⊗_R B)`.

The source later restricts this functor to bounded-above complexes before
deriving it.  Boundedness is a domain restriction, not part of the total
tensor construction itself.

Source: Weibel, §10.6, pp. 394--397 (FC05-C10-U068). -/
def totalTensorFunctor
    (A : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
    [∀ (A' : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
      (B : CochainComplex (ModuleCat R) ℤ),
      HomologicalComplex.HasMapBifunctor A' B (relativeTensorBifunctor R)
        (ComplexShape.up ℤ)] :
    CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat ℤ) ℤ :=
  (totalTensorBifunctor R).obj A

end LeanCategories.Homological
