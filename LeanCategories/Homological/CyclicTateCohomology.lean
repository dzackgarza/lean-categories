/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.FiniteCyclic

/-!
# Tate cohomology of a cyclic group

Weibel, *An Introduction to Homological Algebra*, Definition 6.2.4, pp. 167--170
(FC05-C06-U021).

For a finite cyclic group `G = ⟨σ⟩` and a `G`-module `A`, Weibel defines Tate cohomology in every
integer degree by the two-periodic formulas

* `Ĥ^(2i)(G; A) = A^G / N A`, and
* `Ĥ^(2i+1)(G; A) = ker N / (σ - 1) A`.

Mathlib's `Rep.FiniteCyclicGroup.normHomCompSub` and `subCompNormHom` already own exactly the two
short complexes whose homology objects are these quotients.  The definition below packages those
existing owners with the source's integer parity convention.  Comparison with Mathlib's general
Tate complex is a theorem and is deliberately not part of this definition unit.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

variable {G : Type} [CommGroup G] [Fintype G]

/-- Weibel's cyclic Tate cohomology object in degree `n`.

The generator hypothesis records the source condition `G = ⟨σ⟩`.  In even degrees the owner is
the homology of `A --N--> A --(σ-1)--> A`, hence `A^G / N A`; in odd degrees it is the homology
of `A --(σ-1)--> A --N--> A`, hence `ker N / (σ-1)A`.

Source: Weibel, Definition 6.2.4, pp. 167--170 (FC05-C06-U021). -/
noncomputable def cyclicTateCohomology
    (A : Rep ℤ G) (σ : G) (_hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) (n : ℤ) : ModuleCat ℤ :=
  if Even n then
    (Rep.FiniteCyclicGroup.normHomCompSub A σ).homology
  else
    (Rep.FiniteCyclicGroup.subCompNormHom A σ).homology

end LeanCategories.Homological
