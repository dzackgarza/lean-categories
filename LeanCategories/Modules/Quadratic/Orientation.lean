/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-! # Peters--Sterk FC11-C16-U007: coherent definite-subspace orientations -/
@[expose] public section
namespace LeanCategories.Modules.Quadratic
universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- An orientation on each maximal positive-definite subspace. -/
def PositiveOrientationFamily [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) : Type u :=
  (P : Submodule ℝ V) → Module.finrank ℝ P = sigPos Q →
    (Q.restrict P).PosDef → Orientation ℝ P (Fin (sigPos Q))

variable [FiniteDimensional ℝ V]

/-- Coherence is preservation of orientation by orthogonal projection.
The comparison equivalences are characterized by their orthogonality equation,
not supplied as an arbitrary transport system. Their existence is a result. -/
def IsCoherentPositiveOrientation (Q : QuadraticForm ℝ V)
    (o : PositiveOrientationFamily Q) : Prop :=
  ∀ (P₁ P₂ : Submodule ℝ V)
    (h₁ : Module.finrank ℝ P₁ = sigPos Q)
    (h₂ : Module.finrank ℝ P₂ = sigPos Q)
    (hp₁ : (Q.restrict P₁).PosDef) (hp₂ : (Q.restrict P₂).PosDef)
    (e : P₁ ≃ₗ[ℝ] P₂),
    (∀ (x : P₁) (y : P₂), Q.IsOrtho ((x : V) - (e x : V)) (y : V)) →
      Orientation.map (Fin (sigPos Q)) e (o P₁ h₁ hp₁) = o P₂ h₂ hp₂

/-- A positive orientation is a coherent family on maximal positive subspaces. -/
def PositiveOrientation (Q : QuadraticForm ℝ V) : Type u :=
  {o : PositiveOrientationFamily Q // IsCoherentPositiveOrientation Q o}

/-- A negative orientation is a positive orientation for the negative form. -/
def NegativeOrientation (Q : QuadraticForm ℝ V) : Type u :=
  PositiveOrientation (-Q)

end LeanCategories.Modules.Quadratic
