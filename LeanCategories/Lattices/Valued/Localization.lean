/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]

/-- Localization at a prime ideal preserves exact linear sequences. -/
theorem localizeAtPrime_exact
    (P : Ideal R) [P.IsPrime]
    {M N O : Type u}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    [Module R M] [Module R N] [Module R O]
    (f : M →ₗ[R] N) (g : N →ₗ[R] O)
    (h : Function.Exact f g) :
    Function.Exact
      (LinearMap.baseChange (Localization.AtPrime P) f)
      (LinearMap.baseChange (Localization.AtPrime P) g) :=
  baseChange_exact R (Localization.AtPrime P) f g h

/-- Integral lattices localized at a prime ideal. -/
noncomputable def localizeIntegralAtPrime
    (P : Ideal R) [P.IsPrime] :
    IntegralLatticeCat R ⥤ IntegralLatticeCat (Localization.AtPrime P) :=
  baseChangeIntegral R (Localization.AtPrime P)

/-- Finite projective integral lattices localized at a prime ideal. -/
noncomputable def localizeFiniteIntegralAtPrime
    (P : Ideal R) [P.IsPrime] :
    FiniteProjectiveLatticeCat R R ⥤
      FiniteProjectiveLatticeCat (Localization.AtPrime P)
        (Localization.AtPrime P) :=
  baseChangeFiniteIntegral R (Localization.AtPrime P)

@[simp]
theorem localizeIntegralAtPrime_pairing_tmul
    (P : Ideal R) [P.IsPrime] (L : IntegralLatticeCat R)
    (a b : Localization.AtPrime P) (x y : L.obj.carrier) :
    ((localizeIntegralAtPrime R P).obj L).obj.pairing
        (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R (Localization.AtPrime P)
        (L.obj.pairing x y) :=
  baseChangeIntegral_pairing_tmul R (Localization.AtPrime P) L a b x y

/-- Two integral lattices are isometric after localization at a prime ideal. -/
noncomputable def IsIsometricAfterLocalizationAtPrime
    (P : Ideal R) [P.IsPrime]
    (L M : IntegralLatticeCat R) : Prop :=
  Nonempty
    (((localizeIntegralAtPrime R P).obj L) ≅
      ((localizeIntegralAtPrime R P).obj M))

/-- A global isometry gives an isometry after every prime localization. -/
theorem isIsometricAfterLocalizationAtPrime_of_iso
    (P : Ideal R) [P.IsPrime] {L M : IntegralLatticeCat R}
    (e : L ≅ M) : IsIsometricAfterLocalizationAtPrime R P L M :=
  ⟨(localizeIntegralAtPrime R P).mapIso e⟩

end LeanCategories.Lattices.Valued
