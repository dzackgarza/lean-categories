/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective and quasi-projective varieties

This file ports the definition layer from
`facebookresearch/atlas-lean`,
`Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean`,
commit `34ffed396f376454c1a9b297f3fd74c5c801fb50`.

Mathlib supplies the graded polynomial ring, `Proj`, and the closed- and
open-immersion predicates.  These definitions combine those existing objects.
No projectivity theorem or variety-specific proxy is introduced here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

universe u

/-! ### Projective space -/

/-- The standard total-degree grading on `k[x₀, ..., xₙ]`. -/
noncomputable abbrev projectiveSpaceGrading (k : Type u) [CommRing k] (n : ℕ) :
    ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard graded polynomial algebra used to construct projective space. -/
noncomputable instance projectiveSpaceGradedRing (k : Type u) [CommRing k] (n : ℕ) :
    GradedRing (projectiveSpaceGrading k n) :=
  MvPolynomial.gradedAlgebra

/-- Projective `n`-space over `k`, defined as the `Proj` of the graded polynomial ring. -/
noncomputable def ProjectiveSpace (k : Type u) [CommRing k] (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (projectiveSpaceGrading k n)

/-- The structure morphism of projective space to the spectrum of its degree-zero ring. -/
noncomputable def ProjectiveSpace.structureMorphism (k : Type u) [CommRing k] (n : ℕ) :
    ProjectiveSpace k n ⟶
      Spec (.of (projectiveSpaceGrading k n 0)) :=
  AlgebraicGeometry.Proj.toSpecZero (projectiveSpaceGrading k n)

/-! ### Variety predicates -/

/-- A scheme is projective when it admits a closed immersion into projective space. -/
def IsProjectiveVariety (k : Type u) [CommRing k] (X : Scheme.{u}) : Prop :=
  ∃ (n : ℕ) (ι : X ⟶ ProjectiveSpace k n), IsClosedImmersion ι

/-- A scheme is quasi-projective when it is open in a projective variety. -/
def IsQuasiProjectiveVariety (k : Type u) [CommRing k] (X : Scheme.{u}) : Prop :=
  ∃ (n : ℕ) (Y : Scheme.{u}) (ι : Y ⟶ ProjectiveSpace k n),
    IsClosedImmersion ι ∧ ∃ (j : X ⟶ Y), IsOpenImmersion j

end LeanCategories.Schemes
