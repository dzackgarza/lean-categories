/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import Mathlib.CategoryTheory.Core
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [LinearOrder K]

/-- The quadratic form associated to a finite symmetric bilinear form. -/
def finiteFormQuadraticForm (L : FiniteFormCat K K) :
    QuadraticForm K L.obj.carrier :=
  LinearMap.BilinMap.toQuadraticMap L.obj.bilinMap

/-- The underlying finite-dimensional module of a finite symmetric form. -/
def finiteFormForget : FiniteFormCat K K ⥤ ModuleCat K :=
  ObjectProperty.ι (isFiniteForm K K) ⋙
    LeanCategories.Modules.Bilinear.Valued.forget K K

/-- An isomorphism of finite symmetric forms gives an isometry of their quadratic forms. -/
def finiteFormQuadraticIsometryEquiv {L M : FiniteFormCat K K}
    (e : L ≅ M) :
    (finiteFormQuadraticForm K L).IsometryEquiv
      (finiteFormQuadraticForm K M) where
  __ := ((finiteFormForget K).mapIso e).toLinearEquiv
  map_app' x := BilinModuleCat.map_pairing e.hom.hom x x

/-- The total Sylvester signature `(positive, negative, nullity)`. -/
noncomputable def signature (L : FiniteFormCat K K) : ℕ × ℕ × ℕ :=
  let Q := finiteFormQuadraticForm K L
  (sigPos Q, sigNeg Q, Module.finrank K Q.radical)

/-- Signature is invariant under isomorphisms of finite symmetric forms. -/
theorem signature_eq_of_iso {L M : FiniteFormCat K K} (e : L ≅ M) :
    signature K L = signature K M := by
  let h : QuadraticMap.Equivalent
      (finiteFormQuadraticForm K L) (finiteFormQuadraticForm K M) :=
    ⟨finiteFormQuadraticIsometryEquiv K e⟩
  simp only [signature]
  rw [h.sigPos_eq, h.sigNeg_eq, h.rank_radical_eq]

/-- Positive, negative, and null ranks sum to the carrier rank. -/
theorem signature_sum [IsStrictOrderedRing K] (L : FiniteFormCat K K) :
    (signature K L).1 + (signature K L).2.1 + (signature K L).2.2 =
      Module.finrank K L.obj.carrier := by
  letI : Module.Finite K L.obj.carrier := L.property.1
  exact QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := finiteFormQuadraticForm K L)

/-- Total signature as a functor on the isomorphism core. -/
noncomputable def signatureFunctor :
    Core (FiniteFormCat K K) ⥤ Discrete (ℕ × ℕ × ℕ) where
  obj L := Discrete.mk (signature K L.of)
  map f := Discrete.eqToHom (signature_eq_of_iso K f.iso)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- A signature value is positive definite when it has no negative or null part. -/
def IsPositiveDefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (_, n, z) => n = 0 ∧ z = 0

/-- A signature value is negative definite when it has no positive or null part. -/
def IsNegativeDefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (p, _, z) => p = 0 ∧ z = 0

/-- A signature value is indefinite when both signed parts are nonzero. -/
def IsIndefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (p, n, _) => 0 < p ∧ 0 < n

/-- A nondegenerate signature is Lorentzian when its smaller signed rank is one. -/
def IsLorentzianSignature : ℕ × ℕ × ℕ → Prop
  | (p, n, z) => min p n = 1 ∧ z = 0

end LeanCategories.Lattices.Valued
