/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.Real.Basic

/-!
# de Rham cohomology data

Definition-level realization of Lee FC08-C17-U002 and FC08-C17-U004.

Once the exterior derivative has been assembled as a cochain complex of real
vector spaces, its square-zero law is part of that Lean object. Lee's closed
forms, exact forms, de Rham cohomology, and cohomology classes are therefore
the native cycles, boundaries, homology, and homology projection. No quotient
carrier or class map is supplied by a caller.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open CategoryTheory

universe u

/-- Lee's closed `p`-forms `Z^p`: the cycles of the de Rham cochain
complex. -/
abbrev deRhamClosedForms
    (K : CochainComplex (ModuleCat.{u} ℝ) ℕ) (p : ℕ) : ModuleCat.{u} ℝ :=
  K.cycles p

/-- Lee's exact `p`-forms `B^p`: the boundaries of the de Rham cochain
complex. -/
abbrev deRhamExactForms
    (K : CochainComplex (ModuleCat.{u} ℝ) ℕ) (p : ℕ) : ModuleCat.{u} ℝ :=
  Abelian.image (K.sc p).f

/-- Lee's de Rham cohomology `H_dR^p = Z^p/B^p`, constructed by the native
homology object of the de Rham cochain complex. -/
abbrev DeRhamCohomologyData
    (K : CochainComplex (ModuleCat.{u} ℝ) ℕ) (p : ℕ) : ModuleCat.{u} ℝ :=
  K.homology p

/-- The canonical cohomology-class map from closed forms to de Rham
cohomology. -/
def deRhamCohomologyClassMap
    (K : CochainComplex (ModuleCat.{u} ℝ) ℕ) (p : ℕ) :
    deRhamClosedForms K p ⟶ DeRhamCohomologyData K p :=
  K.homologyπ p

/-- Lee's cohomology class `[ω]` of a closed `p`-form. -/
def deRhamCohomologyClass
    (K : CochainComplex (ModuleCat.{u} ℝ) ℕ) (p : ℕ)
    (ω : deRhamClosedForms K p) :
    DeRhamCohomologyData K p :=
  (deRhamCohomologyClassMap K p).hom ω

/-- Two closed forms are cohomologous exactly when their canonical homology
classes agree. -/
def AreDeRhamCohomologous
    (K : CochainComplex (ModuleCat.{u} ℝ) ℕ) (p : ℕ)
    (ω η : deRhamClosedForms K p) : Prop :=
  deRhamCohomologyClass K p ω = deRhamCohomologyClass K p η

end LeanCategories.Topology
