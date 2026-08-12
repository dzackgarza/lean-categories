/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Adele
public import LeanCategories.Lattices.Valued.RingEquiv
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

open CategoryTheory
open NumberField
open scoped NumberField

namespace LeanCategories.Lattices.Valued

/-- Two finite integral lattices are globally isometric. -/
def IsGloballyIsometric
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  Nonempty (L ≅ M)

/-- Two integral lattices are isometric after extension to the real numbers. -/
noncomputable def IsRealIsometric
    (L M : IntegralLatticeCat ℤ) : Prop :=
  Nonempty
    (((baseChangeIntegral ℤ ℝ).obj L) ≅
      ((baseChangeIntegral ℤ ℝ).obj M))

/-- Two integral lattices are isometric over the `p`-adic integers. -/
noncomputable def IsPadicallyIsometricAt (p : ℕ) (hp : p.Prime)
    (L M : IntegralLatticeCat ℤ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  Nonempty
    (((completeIntegralAtPrime p).obj L) ≅
      ((completeIntegralAtPrime p).obj M))

/-- The classical real and `p`-adic local isometry condition. -/
noncomputable def IsClassicallyLocallyIsometric
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsRealIsometric L.obj M.obj ∧
    ∀ p (hp : p.Prime), IsPadicallyIsometricAt p hp L.obj M.obj

/-- Transport a finite projective `ℤ`-lattice to the ring of integers of `ℚ`. -/
noncomputable def rationalIntegerLatticeTransport :
    FiniteProjectiveLatticeCat ℤ ℤ ⥤
      FiniteProjectiveLatticeCat (𝓞 ℚ) (𝓞 ℚ) :=
  transportFiniteProjectiveLattice (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm

/-- Two finite integral lattices have the same genus when their ring-adelic scalar
extensions are isometric. -/
noncomputable def SameGenus
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  SameAdeleGenus ℚ
    (rationalIntegerLatticeTransport.obj L)
    (rationalIntegerLatticeTransport.obj M)

/-- The integral `ℤ`-lattice genus is the ring-adelic genus after transport across
`𝓞 ℚ ≃ ℤ`. -/
theorem sameGenus_iff_sameAdeleGenus
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) :
    SameGenus L M ↔
      SameAdeleGenus ℚ
        (rationalIntegerLatticeTransport.obj L)
        (rationalIntegerLatticeTransport.obj M) :=
  Iff.rfl

theorem isGloballyIsometric_refl (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    IsGloballyIsometric L L :=
  ⟨Iso.refl L⟩

theorem isGloballyIsometric_symm {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : IsGloballyIsometric L M) : IsGloballyIsometric M L := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem isGloballyIsometric_trans {L M N : FiniteProjectiveLatticeCat ℤ ℤ}
    (hLM : IsGloballyIsometric L M) (hMN : IsGloballyIsometric M N) :
    IsGloballyIsometric L N := by
  obtain ⟨e⟩ := hLM
  obtain ⟨f⟩ := hMN
  exact ⟨e ≪≫ f⟩

theorem sameGenus_refl (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    SameGenus L L :=
  sameAdeleGenus_refl ℚ _

theorem sameGenus_symm {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : SameGenus L M) : SameGenus M L :=
  sameAdeleGenus_symm ℚ h

theorem sameGenus_trans {L M N : FiniteProjectiveLatticeCat ℤ ℤ}
    (hLM : SameGenus L M) (hMN : SameGenus M N) : SameGenus L N :=
  sameAdeleGenus_trans ℚ hLM hMN

/-- A global isometry induces every real and p-adic local isometry. -/
theorem sameGenus_of_isGloballyIsometric
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : IsGloballyIsometric L M) : SameGenus L M := by
  obtain ⟨e⟩ := h
  exact ⟨(finiteRingAdeleBaseChange ℚ).mapIso
    (rationalIntegerLatticeTransport.mapIso e)⟩

/-- Global isometry as an equivalence relation on finite integral lattices. -/
def globalIsometrySetoid : Setoid (FiniteProjectiveLatticeCat ℤ ℤ) where
  r := IsGloballyIsometric
  iseqv := ⟨isGloballyIsometric_refl, isGloballyIsometric_symm,
    isGloballyIsometric_trans⟩

/-- Genus as an equivalence relation on finite integral lattices. -/
noncomputable def genusSetoid : Setoid (FiniteProjectiveLatticeCat ℤ ℤ) where
  r := SameGenus
  iseqv := ⟨sameGenus_refl, sameGenus_symm, sameGenus_trans⟩

/-- Global isometry classes of finite integral lattices. -/
abbrev IntegralLatticeIsometryClass := Quotient globalIsometrySetoid

/-- Genera of finite integral lattices. -/
noncomputable abbrev IntegralLatticeGenus := Quotient genusSetoid

/-- The local-global map from global isometry classes to genera. -/
noncomputable def isometryClassToGenus :
    IntegralLatticeIsometryClass → IntegralLatticeGenus :=
  Quotient.map id fun _ _ h ↦ sameGenus_of_isGloballyIsometric h

/-- Every genus contains a global isometry class. -/
theorem isometryClassToGenus_surjective :
    Function.Surjective isometryClassToGenus := by
  intro g
  refine Quotient.inductionOn g ?_
  intro L
  exact ⟨Quotient.mk _ L, rfl⟩

/-- The full category of finite integral lattices in the genus of `L`. -/
def genusProperty (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    ObjectProperty (FiniteProjectiveLatticeCat ℤ ℤ) :=
  SameGenus L

/-- Finite integral lattices in a fixed genus. -/
abbrev GenusCat (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (genusProperty L).FullSubcategory

end LeanCategories.Lattices.Valued
