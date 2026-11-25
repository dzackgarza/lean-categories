/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Morphisms out of the tensor product with a free module

## Provenance (lean-categories#22)

Ported from `TauCeti/Algebra/Category/ModuleCat/Monoidal/Free.lean` (The Tau Ceti contributors, Apache 2.0), commit
`ca32605ff53921fa0689dd312618b7cfaafa7e43`, namespaces renamed `TauCeti` →
`LeanCategories`. The unit's provenance and search record is in
`LeanCategories/AlgebraicGeometry/RelativeSpec/Basic.lean`.


A morphism out of the tensor product `M₁ ⊗ (ModuleCat.free S).obj X` of a module with a free
module is determined by its values on the pure tensors `m ⊗ₜ ModuleCat.freeMk x` of an element of
`M₁` with a basis element: `LeanCategories.ModuleCat.tensor_free_hom_ext` combines Mathlib's
extensionality lemmas `ModuleCat.MonoidalCategory.tensor_ext` for tensor products and
`ModuleCat.free_hom_ext` for free modules.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace LeanCategories.ModuleCat

variable {S : Type u} [CommRing S] {M₁ M₂ : ModuleCat.{u} S} {X : Type u}

/-- Two morphisms out of the tensor product of a module with a free module agree once they agree
on pure tensors with basis elements. -/
theorem tensor_free_hom_ext {f g : M₁ ⊗ (ModuleCat.free S).obj X ⟶ M₂}
    (h : ∀ (m : M₁) (x : X), f (m ⊗ₜ ModuleCat.freeMk x) = g (m ⊗ₜ ModuleCat.freeMk x)) :
    f = g := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun m s ↦ ?_
  have := ModuleCat.free_hom_ext
    (f := ModuleCat.ofHom (f.hom ∘ₗ TensorProduct.mk S M₁ ((ModuleCat.free S).obj X) m))
    (g := ModuleCat.ofHom (g.hom ∘ₗ TensorProduct.mk S M₁ ((ModuleCat.free S).obj X) m))
    (fun x ↦ h m x)
  exact ConcreteCategory.congr_hom this s

end LeanCategories.ModuleCat
