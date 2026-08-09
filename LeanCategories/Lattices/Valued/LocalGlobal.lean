/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.BaseChange
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

open CategoryTheory

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
    (((baseChangeIntegral ℤ ℤ_[p]).obj L) ≅
      ((baseChangeIntegral ℤ ℤ_[p]).obj M))

/-- Two finite integral lattices have the same genus. -/
noncomputable def SameGenus
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsRealIsometric L.obj M.obj ∧
    ∀ p (hp : p.Prime), IsPadicallyIsometricAt p hp L.obj M.obj

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
    SameGenus L L := by
  constructor
  · exact ⟨Iso.refl _⟩
  · intro p hp
    exact ⟨Iso.refl _⟩

theorem sameGenus_symm {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : SameGenus L M) : SameGenus M L := by
  constructor
  · obtain ⟨e⟩ := h.1
    exact ⟨e.symm⟩
  · intro p hp
    obtain ⟨e⟩ := h.2 p hp
    exact ⟨e.symm⟩

theorem sameGenus_trans {L M N : FiniteProjectiveLatticeCat ℤ ℤ}
    (hLM : SameGenus L M) (hMN : SameGenus M N) : SameGenus L N := by
  constructor
  · obtain ⟨e⟩ := hLM.1
    obtain ⟨f⟩ := hMN.1
    exact ⟨e ≪≫ f⟩
  · intro p hp
    obtain ⟨e⟩ := hLM.2 p hp
    obtain ⟨f⟩ := hMN.2 p hp
    exact ⟨e ≪≫ f⟩

/-- A global isometry induces every real and p-adic local isometry. -/
theorem sameGenus_of_isGloballyIsometric
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : IsGloballyIsometric L M) : SameGenus L M := by
  obtain ⟨e⟩ := h
  let latticeIso : L.obj ≅ M.obj :=
    (ObjectProperty.ι (isFiniteProjectiveLattice ℤ ℤ)).mapIso e
  constructor
  · exact ⟨(baseChangeIntegral ℤ ℝ).mapIso latticeIso⟩
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    exact ⟨(baseChangeIntegral ℤ ℤ_[p]).mapIso latticeIso⟩

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
