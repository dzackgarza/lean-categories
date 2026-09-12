/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CyclicOperators
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Cyclic coinvariant quotient complex

Weibel, *An Introduction to Homological Algebra* (1994), Corollary 9.6.9,
pp. 330--337 (FC05-C09-U090).

For a cyclic module `A`, quotient degree `n` by the image of `1-t_n`.  The
Hochschild differential descends to these quotients, giving the complex
`A_*/(1-t)`.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe u v

variable (R : Type u) [Ring R]

/-- The image of `1-t_n` in degree `n`. -/
def cyclicDifferenceSubmodule
    (A : CyclicObject (C := ModuleCat.{v} R)) (n : ℕ) :
    Submodule R (A.obj.obj (op ⦋n⦌)) :=
  LinearMap.range ((𝟙 _ - (A.t n).hom).hom)

/-- Degree `n` of the cyclic coinvariant quotient. -/
abbrev cyclicCoinvariantDegree
    (A : CyclicObject (C := ModuleCat.{v} R)) (n : ℕ) : ModuleCat.{v} R :=
  ModuleCat.of R ((A.obj.obj (op ⦋n⦌)) ⧸ cyclicDifferenceSubmodule R A n)

/-- The canonical quotient map `A_n → A_n/(1-t_n)`. -/
noncomputable def cyclicCoinvariantQuotient
    (A : CyclicObject (C := ModuleCat.{v} R)) (n : ℕ) :
    A.obj.obj (op ⦋n⦌) ⟶ cyclicCoinvariantDegree R A n :=
  ModuleCat.ofHom (Submodule.mkQ (cyclicDifferenceSubmodule R A n))

/-- Definition-layer realization of the quotient Hochschild complex
`A_*/(1-t)`.  The displayed square says the differential is induced from the
ordinary Hochschild differential. -/
structure CyclicCoinvariantComplexRealization
    (A : CyclicObject (C := ModuleCat.{v} R)) where
  /-- The quotient chain complex. -/
  complex : ChainComplex (ModuleCat.{v} R) ℕ
  /-- Identification of degree `n` with `A_n/(1-t_n)`. -/
  degreeIso : ∀ n : ℕ, complex.X n ≅ cyclicCoinvariantDegree R A n
  /-- The quotient map followed by the chosen degree identification. -/
  differential : ∀ n : ℕ,
    cyclicCoinvariantQuotient R A (n + 1) ≫ (degreeIso (n + 1)).inv ≫
        complex.d (n + 1) n =
      (cyclicHochschildComplex A).d (n + 1) n ≫
        cyclicCoinvariantQuotient R A n ≫ (degreeIso n).inv

end LeanCategories.Homological
