/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.ProfiniteIntegerData
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Quasi-finite Frobenius generator data

Definition-level realization of Serre FC10-C13-U043.

A quasi-finite structure includes a chosen topological group equivalence from
Serre's profinite integers to the relevant absolute Galois group. The free
generator denoted by Serre is simply the image of the canonical additive
generator `1 ∈ Z-hat` under that supplied equivalence.

Constructing such an equivalence for a particular residue field is result
content. This file records only the convention once the quasi-finite
equivalence has been supplied.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The canonical additive generator `1 ∈ Z-hat` on the local
multiplicative profinite-completion carrier. -/
def quasiFiniteProfiniteIntegerGeneratorData :
    serreProfiniteIntegerData :=
  ProfiniteGrp.ProfiniteCompletion.etaFn
    (GrpCat.of (Multiplicative ℤ))
    (Multiplicative.ofAdd (1 : ℤ))

/-- Serre's distinguished Frobenius/free generator attached to a supplied
quasi-finite `Z-hat` equivalence. -/
def quasiFiniteFrobeniusGeneratorData
    (e : serreProfiniteIntegerData ≃ₜ* G) : G :=
  e quasiFiniteProfiniteIntegerGeneratorData

end LeanCategories.Algebra
