/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic

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

/-- On page `r`, exactly one row is nonzero: all terms off row `q₀` vanish, and at least one
term on row `q₀` is nonzero. -/
def HasSingleNonzeroRowAt {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) : Prop :=
  ∃ q₀ : ℤ,
    (∃ p : ℤ, ¬ IsZero ((E.page r hr).X (p, q₀))) ∧
      ∀ p q : ℤ, q ≠ q₀ → IsZero ((E.page r hr).X (p, q))

/-- On page `r`, exactly one column is nonzero. -/
def HasSingleNonzeroColumnAt {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) : Prop :=
  ∃ p₀ : ℤ,
    (∃ q : ℤ, ¬ IsZero ((E.page r hr).X (p₀, q))) ∧
      ∀ p q : ℤ, p ≠ p₀ → IsZero ((E.page r hr).X (p, q))

/-- Weibel's collapse condition (Definition 5.2.7): page `E^r` has exactly one nonzero row or
exactly one nonzero column. -/
def CollapsesAt {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) : Prop :=
  HasSingleNonzeroRowAt E r hr ∨ HasSingleNonzeroColumnAt E r hr

/-- Weibel's homological bounded-below condition (Definition 5.2.9): in each total degree,
the initial page vanishes sufficiently far to the left. -/
def IsHomologicallyBoundedBelow {r₀ : ℤ} (E : HomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
    IsZero ((E.page r₀ (by rfl)).X (p, n - p))

/-- The cohomological dual of Weibel's bounded-below condition: in each total degree, the
initial page vanishes sufficiently far to the right. -/
def IsCohomologicallyBoundedBelow {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
    IsZero ((E.page r₀ (by rfl)).X (p, n - p))

/-- Degree-boundedness is stronger than the homological bounded-below condition. -/
theorem isHomologicallyBoundedBelow_of_degreeBounded {r₀ : ℤ}
    (E : HomologicalSpectralSequence C r₀) (hE : IsDegreeBounded E) :
    IsHomologicallyBoundedBelow E := by
  intro n
  let s : Set (ℤ × ℤ) :=
    {pq | pq.1 + pq.2 = n ∧ ¬ IsZero ((E.page r₀ (by rfl)).X pq)}
  have hs : s.Finite := hE n
  let t : Set ℤ := Prod.fst '' s
  have ht : t.Finite := hs.image Prod.fst
  by_cases htn : t.Nonempty
  · let m : ℤ := ht.toFinset.min' (by simpa using htn)
    refine ⟨m - 1, fun p hp => ?_⟩
    by_contra hz
    have hp_mem_s : (p, n - p) ∈ s := by
      exact ⟨by omega, hz⟩
    have hp_mem_t : p ∈ t := ⟨(p, n - p), hp_mem_s, rfl⟩
    have hm_le : m ≤ p := by
      exact ht.toFinset.min'_le _ (by simpa using hp_mem_t)
    omega
  · refine ⟨0, fun p hp => ?_⟩
    by_contra hz
    apply htn
    exact ⟨p, ⟨(p, n - p), ⟨by omega, hz⟩, rfl⟩⟩

/-- Degree-boundedness is also stronger than the cohomological bounded-below condition. -/
theorem isCohomologicallyBoundedBelow_of_degreeBounded {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (hE : IsDegreeBounded E) :
    IsCohomologicallyBoundedBelow E := by
  intro n
  let s : Set (ℤ × ℤ) :=
    {pq | pq.1 + pq.2 = n ∧ ¬ IsZero ((E.page r₀ (by rfl)).X pq)}
  have hs : s.Finite := hE n
  let t : Set ℤ := Prod.fst '' s
  have ht : t.Finite := hs.image Prod.fst
  by_cases htn : t.Nonempty
  · let m : ℤ := ht.toFinset.max' (by simpa using htn)
    refine ⟨m + 1, fun p hp => ?_⟩
    by_contra hz
    have hp_mem_s : (p, n - p) ∈ s := by
      exact ⟨by omega, hz⟩
    have hp_mem_t : p ∈ t := ⟨(p, n - p), hp_mem_s, rfl⟩
    have hp_le : p ≤ m := by
      exact ht.toFinset.le_max' _ (by simpa using hp_mem_t)
    omega
  · refine ⟨0, fun p hp => ?_⟩
    by_contra hz
    apply htn
    exact ⟨p, ⟨(p, n - p), ⟨by omega, hz⟩, rfl⟩⟩

/-- Weibel's regularity condition (Definition 5.2.10): at every fixed bidegree, the outgoing
differential is zero on every sufficiently late page. -/
def IsRegularSpectralSequence {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E : SpectralSequence C c r₀) : Prop :=
  ∀ pq : ℤ × ℤ, ∃ r : ℤ, ∃ hr : r₀ ≤ r, ∀ s : ℤ, ∀ hrs : r ≤ s,
    (E.page s (hr.trans hrs)).d pq ((c s).next pq) = 0

/-- A spectral sequence whose outgoing differentials vanish on every page is regular. -/
theorem isRegularSpectralSequence_of_differential_zero {r₀ : ℤ}
    {c : ℤ → ComplexShape (ℤ × ℤ)} (E : SpectralSequence C c r₀)
    (hE : ∀ (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ),
      (E.page r hr).d pq ((c r).next pq) = 0) :
    IsRegularSpectralSequence E := by
  rw [IsRegularSpectralSequence]
  intro pq
  exact ⟨r₀, le_rfl, fun s hs => hE s hs pq⟩

/-- A bidegree supporting nonzero outgoing differentials arbitrarily late prevents regularity. -/
theorem not_isRegularSpectralSequence_of_cofinally_nonzero {r₀ : ℤ}
    {c : ℤ → ComplexShape (ℤ × ℤ)} (E : SpectralSequence C c r₀)
    (pq : ℤ × ℤ)
    (hE : ∀ (r : ℤ) (hr : r₀ ≤ r), ∃ s : ℤ, ∃ hrs : r ≤ s,
      (E.page s (hr.trans hrs)).d pq ((c s).next pq) ≠ 0) :
    ¬ IsRegularSpectralSequence E := by
  intro hreg
  rw [IsRegularSpectralSequence] at hreg
  obtain ⟨r, hr₀, hr⟩ := hreg pq
  obtain ⟨s, hrs, hs⟩ := hE r hr₀
  exact hs (hr s hrs)

end LeanCategories.Homological
