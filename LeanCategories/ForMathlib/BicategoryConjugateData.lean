/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# Construction data for the conjugate of a bicategory

Definition-level realization of Kerodon FC17-KER-U00286 (tag 008D).

For a bicategory `B`, its conjugate keeps the same objects and the same
directions of 1-cells, while replacing each hom-category by its opposite.
Consequently only 2-cells are reversed.  This file records the induced
identity/composition, whiskering, associator, and unitor data.

Mathlib's `Bicategory` class also requires the whiskering laws and the
pentagon/triangle equations.  Certifying those laws is proof work, so the
actual `Bicategory` instance is deliberately deferred beyond Sweep III.
-/

@[expose] public section

namespace LeanCategories.Bicategory.Conjugate

open CategoryTheory Opposite
open CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [CategoryTheory.Bicategory.{w, v} B]

/-- The hom-category of the conjugate bicategory: the opposite of the
original hom-category.  Its objects are the original 1-cells and its arrows
are the original 2-cells with direction reversed. -/
abbrev Hom (a b : B) := (a ⟶ b)ᵒᵖ

/-- Regard an original 1-cell as a 1-cell of the conjugate construction. -/
def hom {a b : B} (f : a ⟶ b) : Hom a b :=
  Opposite.op f

/-- The identity 1-cell in the conjugate construction. -/
def id (a : B) : Hom a a :=
  hom (𝟙 a)

/-- Composition of conjugate 1-cells keeps the original 1-cell direction. -/
def comp {a b c : B} (f : Hom a b) (g : Hom b c) : Hom a c :=
  hom (f.unop ≫ g.unop)

/-- Left whiskering in the conjugate construction reverses the supplied
2-cell, whisks it in `B`, and reverses it back. -/
def whiskerLeft {a b c : B} (f : Hom a b) {g h : Hom b c}
    (η : g ⟶ h) : comp f g ⟶ comp f h :=
  (f.unop ◁ η.unop).op

/-- Right whiskering in the conjugate construction. -/
def whiskerRight {a b c : B} {f g : Hom a b} (η : f ⟶ g)
    (h : Hom b c) : comp f h ⟶ comp g h :=
  (η.unop ▷ h.unop).op

/-- The conjugate associator is the opposite of the inverse original
associator. -/
def associator {a b c d : B} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    comp (comp f g) h ≅ comp f (comp g h) :=
  Iso.op (α_ f.unop g.unop h.unop).symm

/-- The conjugate left unitor is the opposite of the inverse original left
unitor. -/
def leftUnitor {a b : B} (f : Hom a b) : comp (id a) f ≅ f :=
  Iso.op (λ_ f.unop).symm

/-- The conjugate right unitor is the opposite of the inverse original right
unitor. -/
def rightUnitor {a b : B} (f : Hom a b) : comp f (id b) ≅ f :=
  Iso.op (ρ_ f.unop).symm

end LeanCategories.Bicategory.Conjugate
