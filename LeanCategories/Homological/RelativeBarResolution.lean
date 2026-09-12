/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CotripleResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The relative bar cotriple

Weibel, *An Introduction to Homological Algebra*, Construction 8.6.12,
pp. 278--285 (FC05-C08-U069).

For a homomorphism of commutative rings `k → R`, extension of scalars
`R ⊗ₖ -` is left adjoint to restriction of scalars.  The induced comonad on
`R`-modules is Weibel's relative bar cotriple.  Applying the canonical cotriple
construction in each degree gives the underlying degree, face, degeneracy, and
augmentation data of the relative bar resolution.

That these data assemble to an augmented simplicial object and that its
underlying restricted simplicial object is contractible/aspherical are
result-level assertions and are not included here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

universe u v w

variable {k : Type u} {R : Type v} [CommRing k] [CommRing R]

/-- The comonad on `R`-modules induced by extension/restriction of scalars
along `f : k →+* R`.  This is Weibel's relative bar cotriple.

Source: Weibel, Construction 8.6.12 (FC05-C08-U069). -/
noncomputable def relativeBarComonad (f : k →+* R) :
    Comonad (ModuleCat.{max w v} R) :=
  (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad

/-- Degree `n` of the canonical relative bar construction on an `R`-module
`M`, namely the `(n+1)`-fold iterate of the bar cotriple. -/
abbrev relativeBarDegree (f : k →+* R) (M : ModuleCat.{max w v} R) (n : ℕ) :
    ModuleCat.{max w v} R :=
  (relativeBarComonad f).simplicialDegree M n

/-- The `i`th face of the canonical relative bar construction. -/
def relativeBarFace (f : k →+* R) (M : ModuleCat.{max w v} R)
    (n : ℕ) (i : Fin (n + 1)) :
    relativeBarDegree f M n ⟶
      (relativeBarComonad f).iterObj M n :=
  (relativeBarComonad f).face M n i

/-- The `i`th degeneracy of the canonical relative bar construction. -/
def relativeBarDegeneracy (f : k →+* R) (M : ModuleCat.{max w v} R)
    (n : ℕ) (i : Fin (n + 1)) :
    relativeBarDegree f M n ⟶
      (relativeBarComonad f).iterObj M (n + 2) :=
  (relativeBarComonad f).degeneracy M n i

/-- The canonical augmentation from bar degree zero to `M`. -/
def relativeBarAugmentation (f : k →+* R) (M : ModuleCat.{max w v} R) :
    relativeBarDegree f M 0 ⟶ M :=
  (relativeBarComonad f).augmentation M

end LeanCategories.Homological
