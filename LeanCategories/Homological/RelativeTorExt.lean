/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.RelativeBarResolution
public import LeanCategories.Homological.TripleCohomology
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Relative Tor and Ext

Weibel, *An Introduction to Homological Algebra* (1994), Definition 8.7.5,
pp. 286--293 (FC05-C08-U081).

For a homomorphism `k → R`, relative Tor and Ext are the cotriple homology and
cohomology of the relative bar cotriple.  A simplicial realization of the
canonical bar formulas is supplied explicitly, keeping the existence and
comparison results at theorem level.
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory

namespace LeanCategories.Homological

universe u v

variable {k : Type u} {R : Type v} [CommRing k] [CommRing R]

/-- Relative Tor for `k → R`, defined as cotriple homology of the relative
bar cotriple with coefficient functor `- ⊗_R N`.

Source: Weibel, Definition 8.7.5 (FC05-C08-U081). -/
noncomputable def relativeTor (f : k →+* R) (M N : ModuleCat.{v} R)
    (S : (relativeBarComonad f).SimplicialResolution M) (n : ℕ) :
    ModuleCat.{v} R :=
  cotripleHomology (relativeBarComonad f) M S (tensorRight N) n

/-- Relative Ext for `k → R`, defined as cotriple cohomology of the relative
bar cotriple with coefficient functor `Hom_R(-,N)`.

Source: Weibel, Definition 8.7.5 (FC05-C08-U081). -/
noncomputable def relativeExt (f : k →+* R) (M N : ModuleCat.{v} R)
    (S : (relativeBarComonad f).SimplicialResolution M) (n : ℕ) :
    AddCommGrpCat.{v} :=
  cotripleCohomology (relativeBarComonad f) M S
    (preadditiveYoneda.obj N) n

end LeanCategories.Homological
