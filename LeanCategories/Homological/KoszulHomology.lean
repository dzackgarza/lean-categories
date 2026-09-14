/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KoszulComplex
public import LeanCategories.Homological.NoncommutativeTensor
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Koszul homology and cohomology

Weibel, *An Introduction to Homological Algebra* (1994), Notation 4.5.1,
pp. 111--114 (FC05-C04-U069).

For a realized Koszul complex `K(x)`, homology with a right `R`-module `A`
is the homology of `A ⊗_R K(x)`.  Cohomology with a left `R`-module `B` is
the cohomology of `Hom_R(K(x),B)`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite

universe u

variable (R : Type u) [Ring R]
variable {n : ℕ} (x : Fin n → R) (hx : IsCentralSequence R x)

/-- The coefficient chain complex `A ⊗_R K` for a chosen realization `K` of the Koszul
complex.  This realization-parametrized form is useful for comparison maps; Weibel's canonical
coefficient complex is `koszulTensorComplex` below. -/
noncomputable def koszulTensorComplexOf
    (K : KoszulComplexRealization R x hx) (A : ModuleCat Rᵐᵒᵖ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((tensorLeftFunctor R A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K.complex

/-- The homology of a chosen Koszul realization with coefficients in a right `R`-module. -/
noncomputable def koszulHomologyOf
    (K : KoszulComplexRealization R x hx) (A : ModuleCat Rᵐᵒᵖ) (q : ℕ) :
    ModuleCat ℤ :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) q).obj
    (koszulTensorComplexOf R x hx K A)

/-- The cochain complex `Hom_R(K,B)` for a chosen realization `K` of the Koszul complex. -/
noncomputable def koszulHomCochainComplexOf
    (K : KoszulComplexRealization R x hx) (B : ModuleCat R) :
    CochainComplex AddCommGrpCat ℕ :=
  ((preadditiveYoneda.obj B).mapHomologicalComplex (ComplexShape.up ℕ)).obj K.complex.op

/-- The cohomology of a chosen Koszul realization with coefficients in a left `R`-module. -/
noncomputable def koszulCohomologyOf
    (K : KoszulComplexRealization R x hx) (B : ModuleCat R) (q : ℕ) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).obj
    (koszulHomCochainComplexOf R x hx K B)

/-- Weibel's canonical coefficient chain complex `A ⊗_R K(x)`. -/
noncomputable def koszulTensorComplex (A : ModuleCat Rᵐᵒᵖ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  koszulTensorComplexOf R x hx (canonicalKoszulComplexRealization R x hx) A

/-- Weibel's Koszul homology `H_q(x,A) = H_q(A ⊗_R K(x))`. -/
noncomputable def koszulHomology (A : ModuleCat Rᵐᵒᵖ) (q : ℕ) : ModuleCat ℤ :=
  koszulHomologyOf R x hx (canonicalKoszulComplexRealization R x hx) A q

/-- Weibel's canonical cochain complex `Hom_R(K(x),B)`. -/
noncomputable def koszulHomCochainComplex (B : ModuleCat R) :
    CochainComplex AddCommGrpCat ℕ :=
  koszulHomCochainComplexOf R x hx (canonicalKoszulComplexRealization R x hx) B

/-- Weibel's Koszul cohomology `H^q(x,B) = H^q(Hom_R(K(x),B))`. -/
noncomputable def koszulCohomology (B : ModuleCat R) (q : ℕ) : AddCommGrpCat :=
  koszulCohomologyOf R x hx (canonicalKoszulComplexRealization R x hx) B q

end LeanCategories.Homological
