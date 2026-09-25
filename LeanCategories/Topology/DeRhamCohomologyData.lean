/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.Real.Basic

/-!
# de Rham cohomology quotient data

Definition-level realization of Lee FC08-C17-U002.

For a graded family of real vector spaces of smooth forms and supplied linear
exterior derivatives, Lee defines closed forms as kernels, exact forms as
images, and de Rham cohomology as closed forms modulo exact differences.

The result `d ∘ d = 0` is what proves every exact form is closed.  Sweep III
does not prove or package that result as a constructor prerequisite.  Instead,
following the repository's local-coefficient (co)homology pattern, this file
records the quotient presentation by a candidate carrier and class map whose
equality relation is exactly difference by an exact form.  Existence of a
candidate satisfying that specification is result-layer content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

variable
  (Form : ℕ → Type u)
  [∀ p, AddCommGroup (Form p)]
  [∀ p, Module ℝ (Form p)]
  (d : ∀ p, Form p →ₗ[ℝ] Form (p + 1))

/-- Lee's closed p-forms `Z^p`: the kernel of the degree-p exterior
derivative. -/
def deRhamClosedForms (p : ℕ) : Submodule ℝ (Form p) :=
  LinearMap.ker (d p)

/-- Lee's exact p-forms `B^p`: zero in degree zero and the image of the
preceding exterior derivative in positive degree. -/
def deRhamExactForms : (p : ℕ) → Submodule ℝ (Form p)
  | 0 => ⊥
  | p + 1 => LinearMap.range (d p)

/-- Candidate vector-space carrier for the quotient `Z^p / B^p`, together
with the quotient-class map from closed p-forms. -/
structure DeRhamCohomologyCandidateData (p : ℕ) where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module ℝ carrier]
  classOf : deRhamClosedForms Form d p →ₗ[ℝ] carrier

attribute [instance]
  DeRhamCohomologyCandidateData.instAddCommGroup
  DeRhamCohomologyCandidateData.instModule

instance (p : ℕ) : Nonempty (DeRhamCohomologyCandidateData Form d p) :=
  ⟨{ carrier := ULift.{u} ℝ
     classOf := 0 }⟩

/-- Exact quotient specification for Lee's `H_dR^p = Z^p/B^p`.

Two closed forms represent the same class exactly when their difference is an
exact p-form, and every quotient class has a closed representative.  No proof
that exact forms are closed, or that this specification is inhabited, is
provided in Sweep III. -/
def IsDeRhamCohomologyData
    (p : ℕ) (H : DeRhamCohomologyCandidateData Form d p) : Prop :=
  Function.Surjective H.classOf ∧
    ∀ x y : deRhamClosedForms Form d p,
      H.classOf x = H.classOf y ↔
        x.1 - y.1 ∈ deRhamExactForms Form d p

/-- Lee's source-facing de Rham cohomology presentation, selected from the
exact quotient specification.  The square-zero theorem is the later result
that supplies the intended realization of this specification. -/
def deRhamCohomologyCandidateData (p : ℕ) :
    DeRhamCohomologyCandidateData Form d p :=
  Classical.epsilon (IsDeRhamCohomologyData Form d p)

/-- The carrier of Lee's p-th de Rham cohomology vector space. -/
abbrev DeRhamCohomologyData (p : ℕ) : Type u :=
  (deRhamCohomologyCandidateData Form d p).carrier

end LeanCategories.Topology
