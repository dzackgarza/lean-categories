/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalGlobal
public import LeanCategories.Lattices.Valued.Spinor

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

/-- The rational scalar extension of a finite integral lattice. -/
noncomputable abbrev RationalLattice
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (baseChangeFiniteIntegral ℤ ℚ).obj L

/-- The direct scalar extension of a finite integral lattice to `ℚ_[p]`. -/
noncomputable abbrev PadicFieldLattice (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (extendFiniteIntegralToPadicField p).obj L

/-- The completion of a finite integral lattice over `ℤ_[p]`. -/
noncomputable abbrev PadicIntegralLattice (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (completeFiniteIntegralAtPrime p).obj L

/-- The finite symmetric form under a direct `p`-adic field extension. -/
noncomputable abbrev PadicFieldForm (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).obj
    (PadicFieldLattice p L)

/-- A direct `p`-adic isometry is the scalar extension of a rational isometry. -/
noncomputable def IsPadicScalarExtensionOf (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (e : RationalLattice L ≅ RationalLattice M)
    (eₚ : PadicFieldLattice p L ≅ PadicFieldLattice p M) : Prop :=
  ∀ x : L.obj.obj.carrier,
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso eₚ).toLinearEquiv
        (1 ⊗ₜ[ℤ] x) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange
        ℤ ℚ ℚ_[p] ℚ_[p] M.obj.obj.carrier
        (1 ⊗ₜ[ℚ]
          ((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv
            (1 ⊗ₜ[ℤ] x))

/-- A direct `p`-adic field isometry extends an isometry of completed lattices. -/
noncomputable def IsPadicCompletionExtensionOf (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (e : PadicIntegralLattice p L ≅ PadicIntegralLattice p M)
    (eₚ : PadicFieldLattice p L ≅ PadicFieldLattice p M) : Prop :=
  ∀ x : L.obj.obj.carrier,
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso eₚ).toLinearEquiv
        (1 ⊗ₜ[ℤ] x) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange
        ℤ ℤ_[p] ℚ_[p] ℚ_[p] M.obj.obj.carrier
        (1 ⊗ₜ[ℤ_[p]]
          ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv
            (1 ⊗ₜ[ℤ] x))

/-- The local data which compares a rational isometry with an integral one. -/
structure PadicSpinorGenusWitness
    (L M : FiniteProjectiveLatticeCat ℤ ℤ)
    (rational : RationalLattice L ≅ RationalLattice M)
    (p : ℕ) [Fact p.Prime] where
  integral : PadicIntegralLattice p L ≅ PadicIntegralLattice p M
  reference : PadicFieldLattice p L ≅ PadicFieldLattice p M
  current : PadicFieldLattice p L ≅ PadicFieldLattice p M
  reference_isScalarExtension :
    IsPadicScalarExtensionOf p rational reference
  current_isCompletionExtension :
    IsPadicCompletionExtensionOf p integral current
  spinorNorm : SpinorNorm (PadicFieldForm p L)
  sameSpinorClass :
    IsSpinorEquivalentRelative spinorNorm
      ((finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).mapIso reference)
      ((finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).mapIso current)

/-- Rational and local integral isometries whose differences have trivial spinor class. -/
structure SpinorGenusWitness
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) where
  real : IsRealIsometric L.obj M.obj
  rational : RationalLattice L ≅ RationalLattice M
  atPrime : ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    PadicSpinorGenusWitness L M rational p

/-- Two finite integral lattices lie in the same spinor genus. -/
noncomputable def SameSpinorGenus
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  Nonempty (SpinorGenusWitness L M)

/-- A common spinor genus is contained in one genus. -/
theorem sameGenus_of_sameSpinorGenus
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : SameSpinorGenus L M) : SameGenus L M := by
  obtain ⟨w⟩ := h
  refine ⟨w.real, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨(ObjectProperty.ι
    (isFiniteProjectiveLattice ℤ_[p] ℤ_[p])).mapIso
      (w.atPrime p hp).integral⟩

/-- Lattices in the spinor genus of `L`. -/
noncomputable def spinorGenusProperty
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    ObjectProperty (FiniteProjectiveLatticeCat ℤ ℤ) :=
  SameSpinorGenus L

/-- The full category of finite integral lattices in one spinor genus. -/
noncomputable abbrev SpinorGenusCat
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (spinorGenusProperty L).FullSubcategory

end LeanCategories.Lattices.Valued
