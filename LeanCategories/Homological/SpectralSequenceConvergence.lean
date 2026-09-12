/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject

/-!
# Bounded spectral sequences and convergence

Weibel, *An Introduction to Homological Algebra*, Definition 5.2.5 (FC05-C05-U006).

Mathlib owns the page-by-page spectral-sequence structure.  This file adds the missing
boundedness and bounded-convergence layer: degreewise finite support, eventual page values, finite
filtrations of the abutment, and the identification of the stable page with the associated graded
pieces.  The cohomological version uses the dual decreasing filtration.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable (C : Type u) [Category C] [Abelian C]

/-- A homological spectral sequence has differential of bidegree `(-r,r-1)` on page `r`. -/
abbrev HomologicalSpectralSequence (r₀ : ℤ) :=
  SpectralSequence C (fun r => ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) r₀

variable {C} {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}

/-- Weibel's degree-boundedness condition: on the initial page, only finitely many nonzero
bidegrees occur on each line of fixed total degree. -/
def IsDegreeBounded (E : SpectralSequence C c r₀) : Prop :=
  ∀ n : ℤ,
    Set.Finite {pq : ℤ × ℤ |
      pq.1 + pq.2 = n ∧ ¬ IsZero ((E.page r₀ (by rfl)).X pq)}

/-- An object realizing the eventual value of one bidegree of a spectral sequence. -/
structure StableValueAt (E : SpectralSequence C c r₀) (pq : ℤ × ℤ) where
  /-- The eventual object. -/
  object : C
  /-- A page from which this bidegree has stabilized. -/
  stage : ℤ
  stage_ge : r₀ ≤ stage
  /-- Every later page is isomorphic to the eventual object. -/
  iso (r : ℤ) (hr : stage ≤ r) : (E.page r (stage_ge.trans hr)).X pq ≅ object

/-- A finite increasing filtration of an object, indexed by `ℤ` and eventually equal to `0`
and the whole object. -/
structure FiniteIncreasingFiltration (X : C) where
  obj : ℤ → Subobject X
  monotone : Monotone obj
  boundedBelow : ∃ a : ℤ, ∀ p ≤ a, obj p = ⊥
  boundedAbove : ∃ b : ℤ, ∀ p, b ≤ p → obj p = ⊤

namespace FiniteIncreasingFiltration

variable {X : C}

/-- The `p`th associated graded piece `F_p/F_{p-1}`. -/
noncomputable def gradedPiece (F : FiniteIncreasingFiltration X) (p : ℤ) : C :=
  cokernel (Subobject.ofLE (F.obj (p - 1)) (F.obj p) (F.monotone (by omega)))

end FiniteIncreasingFiltration

/-- A finite decreasing filtration of an object, indexed by `ℤ` and eventually equal to the
whole object on the left and `0` on the right. -/
structure FiniteDecreasingFiltration (X : C) where
  obj : ℤ → Subobject X
  antitone : Antitone obj
  boundedBelow : ∃ a : ℤ, ∀ p ≤ a, obj p = ⊤
  boundedAbove : ∃ b : ℤ, ∀ p, b ≤ p → obj p = ⊥

namespace FiniteDecreasingFiltration

variable {X : C}

/-- The `p`th associated graded piece `F^p/F^{p+1}`. -/
noncomputable def gradedPiece (F : FiniteDecreasingFiltration X) (p : ℤ) : C :=
  cokernel (Subobject.ofLE (F.obj (p + 1)) (F.obj p) (F.antitone (by omega)))

end FiniteDecreasingFiltration

/-- Bounded homological convergence to a graded target `H`: every bidegree has an eventual
value and, in total degree `p+q`, that value is the associated graded piece
`F_p H_{p+q}/F_{p-1} H_{p+q}` of a finite filtration. -/
structure HomologicalBoundedConvergence {r₀ : ℤ}
    (E : HomologicalSpectralSequence C r₀) (H : ℤ → C) where
  bounded : IsDegreeBounded E
  stable (pq : ℤ × ℤ) : StableValueAt E pq
  filtration (n : ℤ) : FiniteIncreasingFiltration (H n)
  gradedIso (p q : ℤ) :
    (stable (p, q)).object ≅ (filtration (p + q)).gradedPiece p

/-- Bounded cohomological convergence to a graded target `H`: the stable value in bidegree
`(p,q)` is `F^p H^{p+q}/F^{p+1} H^{p+q}` for a finite decreasing filtration. -/
structure CohomologicalBoundedConvergence {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (H : ℤ → C) where
  bounded : IsDegreeBounded E
  stable (pq : ℤ × ℤ) : StableValueAt E pq
  filtration (n : ℤ) : FiniteDecreasingFiltration (H n)
  gradedIso (p q : ℤ) :
    (stable (p, q)).object ≅ (filtration (p + q)).gradedPiece p

end LeanCategories.Homological
