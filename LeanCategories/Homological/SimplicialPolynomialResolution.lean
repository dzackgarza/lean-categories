/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.AndreQuillen
public import LeanCategories.Homological.AugmentedSimplicialObjects
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Simplicial polynomial resolutions

Weibel, *An Introduction to Homological Algebra* (1994), §8.8,
pp. 294--299 (FC05-C08-U099).

A simplicial polynomial resolution of a commutative `k`-algebra `R` is an
augmented simplicial commutative `k`-algebra whose terms are polynomial
`k`-algebras and whose underlying simplicial abelian group is aspherical.
For simplicial commutative algebras this is the additive-group form of the
source's underlying-simplicial-set asphericity condition.

The comparison with the canonical cotriple resolution and the invariance of
André--Quillen (co)homology and the cotangent complex are theorem-level
statements and are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial

namespace LeanCategories.Homological

universe u

/-- Forget a commutative `k`-algebra to its underlying additive commutative
group. -/
def commAlgUnderlyingAddCommGrp (k : Type u) [CommRing k] :
    CommAlgCat.{u} k ⥤ AddCommGrpCat.{u} where
  obj A := AddCommGrpCat.of A
  map f := AddCommGrpCat.ofHom f.hom.toRingHom.toAddMonoidHom
  map_id A := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The augmented simplicial additive group underlying an augmented
simplicial commutative `k`-algebra. -/
def underlyingAdditiveAugmented (k : Type u) [CommRing k]
    (P : SimplicialObject.Augmented (CommAlgCat k)) :
    SimplicialObject.Augmented AddCommGrpCat :=
  (SimplicialObject.Augmented.whiskeringObj _ _
    (commAlgUnderlyingAddCommGrp k)).obj P

/-- A simplicial polynomial resolution in the sense used in Weibel §8.8.
Every degree is a polynomial `k`-algebra and the underlying augmented
simplicial additive group is aspherical.

Source: Weibel, §8.8, pp. 294--299 (FC05-C08-U099). -/
structure SimplicialPolynomialResolution (k : Type u) [CommRing k]
    (P : SimplicialObject.Augmented (CommAlgCat k)) where
  /-- A set of polynomial generators in each simplicial degree. -/
  generators : ℕ → Type u
  /-- Identification of every degree with a polynomial algebra over `k`. -/
  degreeIso : ∀ n : ℕ,
    CommAlgCat.of k (MvPolynomial (generators n) k) ≅ P.left.obj (op ⦋n⦌)
  /-- Asphericity of the underlying augmented simplicial object. -/
  aspherical : IsAspherical (underlyingAdditiveAugmented k P)

end LeanCategories.Homological
