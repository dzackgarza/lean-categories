/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Basic

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/-- The restriction of a finite symmetric form to a submodule. -/
noncomputable def restrictForm (L : FiniteFormCat K K) (W : Submodule K L.obj.carrier) :
    FiniteFormCat K K :=
  have : Module.Finite K L.obj.carrier := L.property.1
  ⟨L.obj.restrict W, inferInstanceAs (Module.Finite K W), fun x y ↦ L.property.2 x.1 y.1⟩

/-- The restricted form pairs vectors of the submodule by the ambient form. -/
@[simp]
theorem pairing_restrictForm (L : FiniteFormCat K K) (W : Submodule K L.obj.carrier)
    (x y : W) : (restrictForm L W).obj.pairing x y = L.obj.pairing (x : L.obj.carrier) y :=
  rfl

end LeanCategories.Lattices.Valued
