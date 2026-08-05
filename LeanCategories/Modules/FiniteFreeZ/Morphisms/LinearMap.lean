module

public import LeanCategories.Modules.FiniteFreeZ.Objects.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Int

@[expose] public section

namespace LeanCategories.Modules.FiniteFreeZ

open CategoryTheory

/-- A submodule M of a free Z-module L is saturated if L/M is torsion-free. -/
def IsSaturated (L : ZLat) (M : Submodule ℤ L.carrier) : Prop :=
  Module.IsTorsionFree ℤ (L.carrier ⧸ M)

/-- Saturation of a submodule: the smallest saturated submodule containing M.
    Equivalently, M_sat = { x ∈ L | ∃ n > 0, n • x ∈ M }. -/
def Saturation (L : ZLat) (M : Submodule ℤ L.carrier) : Submodule ℤ L.carrier :=
  Submodule.span ℤ {x | ∃ (n : ℤ), n ≠ 0 ∧ n • x ∈ M}

/-- The saturation contains the original submodule. -/
theorem le_saturation (L : ZLat) (M : Submodule ℤ L.carrier) : M ≤ Saturation L M := by
  intro x hx
  apply Submodule.subset_span
  exact ⟨1, one_ne_zero, by rwa [one_smul]⟩

/-- Index of a sublattice M in L, when finite. -/
noncomputable def sublatticeIndex (L : ZLat) (M : Submodule ℤ L.carrier) [Fintype (L.carrier ⧸ M)] : ℕ :=
  Fintype.card (L.carrier ⧸ M)

/-- Rank of a ZLat. -/
noncomputable def rank (L : ZLat) : ℕ :=
  Module.finrank ℤ L.carrier

/-- Smith normal form data supplied by Mathlib for a sublattice and a chosen basis. -/
noncomputable def smithNormalForm {ι : Type*} [Finite ι] (L : ZLat)
    (b : Module.Basis ι ℤ L.carrier) (M : Submodule ℤ L.carrier) :=
  M.smithNormalForm b

/-- Saturation preserves the ambient rank. -/
axiom saturation_rank (L : ZLat) (M : Submodule ℤ L.carrier) :
    Module.finrank ℤ (Saturation L M) = Module.finrank ℤ M

end LeanCategories.Modules.FiniteFreeZ
