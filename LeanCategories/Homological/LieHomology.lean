/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.LieModuleCategory
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Lie algebra homology and cohomology

Weibel, *An Introduction to Homological Algebra* (1994), Definition 7.2.2,
§7.2, pp. 219--222, FC05-C07-U017.

For a fixed Lie algebra `L` over a commutative ring `R`, Lie homology is computed by applying
coinvariants to a projective resolution and taking homology; Lie cohomology is computed by applying
invariants to an injective resolution and taking cohomology.  This file records those chosen-
resolution models, which are the definition-level data available before proving that the category
of Lie modules is abelian and proving independence of the chosen resolutions.  Those assertions,
the degree-zero identifications, and subsequent computational statements are result-level
obligations and are intentionally not proved here.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Lie homology `H_n^{Lie}(L,M)` computed from a chosen projective resolution of `M`:
apply Lie coinvariants degreewise and take degree-`n` homology.

Source: Weibel, Definition 7.2.2, pp. 219--222 (FC05-C07-U017). -/
noncomputable def lieHomology
    [HasZeroObject (LieModuleCat.{u, v, w} R L)]
    (M : LieModuleCat.{u, v, w} R L) (P : ProjectiveResolution M) (n : ℕ) :
    ModuleCat.{w} R :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.down ℕ) n).obj
    (((LieModuleCat.coinvariantsFunctor R L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      P.complex)

/-- Lie cohomology `H^n_{Lie}(L,M)` computed from a chosen injective resolution of `M`:
apply Lie invariants degreewise and take degree-`n` cohomology.

Source: Weibel, Definition 7.2.2, pp. 219--222 (FC05-C07-U017). -/
noncomputable def lieCohomology
    [HasZeroObject (LieModuleCat.{u, v, w} R L)]
    (M : LieModuleCat.{u, v, w} R L) (I : InjectiveResolution M) (n : ℕ) :
    ModuleCat.{w} R :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℕ) n).obj
    (((LieModuleCat.invariantsFunctor R L).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex)

end LeanCategories.Homological
