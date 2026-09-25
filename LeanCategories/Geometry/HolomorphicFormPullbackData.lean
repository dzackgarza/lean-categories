/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Geometry.HolomorphicFormSheafData
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Pullback data for global holomorphic forms

Definition-level support for Peters--Sterk FC11-C20-U001.

For a complex-manifold diffeomorphism f, the pullback of a global
holomorphic p-form has the pointwise formula

    (f^* omega)_x = omega_(f x) composed with (df_x)^p.

Rather than proving that this pointwise formula is again a holomorphic global
section, this file records its exact graph on the already-realized
holomorphic-form sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Manifold ContDiff Topology

namespace LeanCategories.Geometry

universe u

variable {E H X : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [TopologicalSpace H]
variable (I : ModelWithCorners ℂ E H) [I.Boundaryless]
variable [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]

/-- Global holomorphic p-forms: sections of Omega_X^p over the top open. -/
abbrev GlobalHolomorphicPFormData (p : ℕ) :=
  (holomorphicPFormSheafData (X := X) I p).presheaf.obj
    (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of X)))

/-- Exact pointwise graph for pullback of a global holomorphic p-form by a
complex-manifold diffeomorphism. -/
def IsGlobalHolomorphicPFormPullbackData
    (p : ℕ) (f : X ≃ₘ⟮I, I⟯ X)
    (s r : GlobalHolomorphicPFormData (X := X) I p) : Prop :=
  ∀ x : X,
    holomorphicPFormSectionValueData (X := X) I p _ r
        ⟨x, Set.mem_univ x⟩ =
      (holomorphicPFormSectionValueData (X := X) I p _ s
        ⟨f x, Set.mem_univ (f x)⟩).compContinuousLinearMap
          (mfderiv I I f x)

/-- A global holomorphic form is nonzero when one of its fibre values is
nonzero. -/
def IsNonzeroGlobalHolomorphicPFormData
    (p : ℕ) (s : GlobalHolomorphicPFormData (X := X) I p) : Prop :=
  ∃ x : X,
    holomorphicPFormSectionValueData (X := X) I p _ s
      ⟨x, Set.mem_univ x⟩ ≠ 0

/-- A complex-manifold diffeomorphism is symplectic in the K3 sense when it
fixes a nonzero global holomorphic two-form. -/
def IsSymplecticComplexDiffeomorphData
    (f : X ≃ₘ⟮I, I⟯ X) : Prop :=
  ∃ s : GlobalHolomorphicPFormData (X := X) I 2,
    IsNonzeroGlobalHolomorphicPFormData (X := X) I 2 s ∧
      IsGlobalHolomorphicPFormPullbackData (X := X) I 2 f s s

/-- Definition-layer Nikulin involution: a symplectic complex
diffeomorphism of order two. -/
def IsNikulinInvolutionData
    (f : X ≃ₘ⟮I, I⟯ X) : Prop :=
  IsSymplecticComplexDiffeomorphData (X := X) I f ∧
    ∀ x : X, f (f x) = x

end LeanCategories.Geometry
