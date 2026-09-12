/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import LeanCategories.Homological.SpectralSequenceInfinity
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

/-- An increasing filtration `… ⊆ F_{p-1}X ⊆ F_pX ⊆ F_{p+1}X ⊆ …`.
This is the filtration data used in Weibel, *An Introduction to Homological Algebra*,
Definition 5.2.11, p. 126. -/
structure IncreasingFiltration (X : C) where
  obj : ℤ → Subobject X
  monotone : Monotone obj

namespace IncreasingFiltration

variable {X : C}

/-- The associated graded piece `F_pX/F_{p-1}X` from Weibel Definition 5.2.11, p. 126. -/
noncomputable def gradedPiece (F : IncreasingFiltration X) (p : ℤ) : C :=
  cokernel (Subobject.ofLE (F.obj (p - 1)) (F.obj p) (F.monotone (by omega)))

/-- The quotient `X/F_pX` occurring in the inverse-limit clause of Weibel
Definition 5.2.11, p. 126. -/
noncomputable def quotient (F : IncreasingFiltration X) (p : ℤ) : C :=
  cokernel (F.obj p).arrow

/-- For `p ≤ q`, the canonical quotient map `X/F_pX ⟶ X/F_qX`. -/
noncomputable def quotientMap (F : IncreasingFiltration X) {p q : ℤ} (h : p ≤ q) :
    F.quotient p ⟶ F.quotient q :=
  cokernel.map (F.obj p).arrow (F.obj q).arrow
    (Subobject.ofLE (F.obj p) (F.obj q) (F.monotone h)) (𝟙 X) (by simp)

/-- The inverse-limit diagram `p ↦ X/F_pX` of Weibel Definition 5.2.11, p. 126. -/
noncomputable def quotientFunctor (F : IncreasingFiltration X) : ℤ ⥤ C where
  obj p := F.quotient p
  map f := F.quotientMap (leOfHom f)
  map_id p := by
    simp [quotientMap, quotient]
  map_comp := by
    intro p q s f g
    dsimp [quotientMap, quotient]
    rw [← cancel_epi (cokernel.π (F.obj p).arrow)]
    simp

/-- The canonical cone from `X` to the quotients `X/F_pX`.  Weibel's completeness
clause `X ≅ lim_p X/F_pX` says precisely that this cone is limiting. -/
noncomputable def completionCone (F : IncreasingFiltration X) : Cone F.quotientFunctor :=
  Cone.mk X
    { app := fun p => cokernel.π (F.obj p).arrow
      naturality := by
        intro p q f
        simp [quotientFunctor, quotientMap, quotient] }

/-- Exhaustiveness `X = ⋃_p F_pX` in Weibel Definition 5.2.11, p. 126. -/
def IsExhaustive (F : IncreasingFiltration X) : Prop :=
  IsLUB (Set.range F.obj) ⊤

/-- Hausdorffness `⋂_p F_pX = 0` in Weibel Definition 5.2.11, p. 126. -/
def IsHausdorff (F : IncreasingFiltration X) : Prop :=
  IsGLB (Set.range F.obj) ⊥

end IncreasingFiltration

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

/-- A spectral sequence is regular when, at each fixed bidegree, every sufficiently late
outgoing differential vanishes.  Source: Weibel, *An Introduction to Homological Algebra*,
Definition 5.2.10, p. 126. -/
def IsRegularSpectralSequence {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E : SpectralSequence C c r₀) : Prop :=
  ∀ pq : ℤ × ℤ, ∃ r : ℤ, ∃ hr : r₀ ≤ r, ∀ s : ℤ, ∀ hrs : r ≤ s,
    (E.page s (hr.trans hrs)).d pq ((c s).next pq) = 0

/-- Weak convergence of a spectral sequence to a graded object: the infinity page is the
associated graded object of an increasing filtration.  Source: Weibel, *An Introduction to
Homological Algebra*, Definition 5.2.11, p. 126.  The `presentation` and `infinityBounds` fields
are exactly the existence data for `E^∞` from Construction 5.2.8. -/
structure SpectralSequenceWeakConvergence {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E : SpectralSequence C c r₀) (H : ℤ → C) where
  presentation (pq : ℤ × ℤ) : CycleBoundaryPresentation E pq
  infinityBounds (pq : ℤ × ℤ) : (presentation pq).InfinityBounds
  filtration (n : ℤ) : IncreasingFiltration (H n)
  gradedIso (p q : ℤ) :
    (presentation (p, q)).infinityPage (infinityBounds (p, q)) ≅
      (filtration (p + q)).gradedPiece p

namespace SpectralSequenceWeakConvergence

variable {E : SpectralSequence C c r₀} {H : ℤ → C}

/-- A weakly convergent spectral sequence approaches, or abuts to, `H` when every target
filtration is exhaustive and Hausdorff.  Source: Weibel Definition 5.2.11, p. 126. -/
def Approaches (W : SpectralSequenceWeakConvergence E H) : Prop :=
  ∀ n : ℤ, (W.filtration n).IsExhaustive ∧ (W.filtration n).IsHausdorff

/-- `AbutsTo` is Weibel's synonymous terminology for `Approaches` in Definition 5.2.11. -/
abbrev AbutsTo (W : SpectralSequenceWeakConvergence E H) : Prop := W.Approaches

/-- Full convergence requires abutment, regularity, and completeness of each target filtration:
the canonical cone `H_n ⟶ H_n/F_pH_n` is a limit cone.  Source: Weibel, *An Introduction to
Homological Algebra*, Definition 5.2.11, p. 126. -/
def Converges (W : SpectralSequenceWeakConvergence E H) : Prop :=
  W.Approaches ∧ IsRegularSpectralSequence E ∧
    ∀ n : ℤ, Nonempty (IsLimit (W.filtration n).completionCone)

end SpectralSequenceWeakConvergence

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
