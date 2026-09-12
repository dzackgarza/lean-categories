/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject

/-!
# The infinity page of a spectral sequence

Weibel, *An Introduction to Homological Algebra*, Construction 5.2.8 (FC05-C05-U009).

For a fixed bidegree, Weibel presents every page as `Z^r / B^r` inside the initial page, with

`B^r ≤ B^{r+1} ≤ Z^{r+1} ≤ Z^r`.

When the union of the boundaries and intersection of the cycles exist, the infinity page is
`Z^∞ / B^∞`.  The structures below record exactly this subquotient presentation and the stated
existence condition for the two limiting subobjects; the infinity object itself is then their
cokernel quotient.  Identification with a stable page in the bounded case is a later result, not
part of the construction.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe u

variable {C : Type u} [Category C] [Abelian C]
  {r₀ : ℤ} {c : ℤ → ComplexShape (ℤ × ℤ)}

/-- A realization of the pages at one bidegree as nested subquotients of the initial page.
This is Weibel's `B^r,Z^r` presentation. -/
structure CycleBoundaryPresentation (E : SpectralSequence C c r₀) (pq : ℤ × ℤ) where
  /-- `B^r`, regarded as a subobject of the initial page. -/
  boundary (r : ℤ) : Subobject ((E.page r₀ (by rfl)).X pq)
  /-- `Z^r`, regarded as a subobject of the initial page. -/
  cycle (r : ℤ) : Subobject ((E.page r₀ (by rfl)).X pq)
  boundary_le_cycle (r : ℤ) (hr : r₀ ≤ r) : boundary r ≤ cycle r
  boundary_monotone {r s : ℤ} (hr : r₀ ≤ r) (hrs : r ≤ s) : boundary r ≤ boundary s
  cycle_antitone {r s : ℤ} (hr : r₀ ≤ r) (hrs : r ≤ s) : cycle s ≤ cycle r
  initial_boundary : boundary r₀ = ⊥
  initial_cycle : cycle r₀ = ⊤
  /-- The page is the quotient `Z^r/B^r`. -/
  pageIso (r : ℤ) (hr : r₀ ≤ r) :
    cokernel (Subobject.ofLE (boundary r) (cycle r) (boundary_le_cycle r hr)) ≅
      (E.page r hr).X pq

namespace CycleBoundaryPresentation

variable {E : SpectralSequence C c r₀} {pq : ℤ × ℤ}

/-- The source's four nested subobjects on consecutive pages. -/
theorem nested (P : CycleBoundaryPresentation E pq) (r : ℤ) (hr : r₀ ≤ r) :
    P.boundary r ≤ P.boundary (r + 1) ∧
      P.boundary (r + 1) ≤ P.cycle (r + 1) ∧
      P.cycle (r + 1) ≤ P.cycle r := by
  exact ⟨P.boundary_monotone hr (by omega),
    P.boundary_le_cycle (r + 1) (by omega), P.cycle_antitone hr (by omega)⟩

/-- The set of boundary subobjects occurring from the initial page onward. -/
def boundarySet (P : CycleBoundaryPresentation E pq) :
    Set (Subobject ((E.page r₀ (by rfl)).X pq)) :=
  Set.range fun r : {r : ℤ // r₀ ≤ r} => P.boundary r.1

/-- The set of cycle subobjects occurring from the initial page onward. -/
def cycleSet (P : CycleBoundaryPresentation E pq) :
    Set (Subobject ((E.page r₀ (by rfl)).X pq)) :=
  Set.range fun r : {r : ℤ // r₀ ≤ r} => P.cycle r.1

/-- The existence data required by Weibel's `B^∞ = ⋃ B^r` and `Z^∞ = ⋂ Z^r` construction. -/
structure InfinityBounds (P : CycleBoundaryPresentation E pq) where
  boundaryInfinity : Subobject ((E.page r₀ (by rfl)).X pq)
  boundary_isLUB : IsLUB P.boundarySet boundaryInfinity
  cycleInfinity : Subobject ((E.page r₀ (by rfl)).X pq)
  cycle_isGLB : IsGLB P.cycleSet cycleInfinity

namespace InfinityBounds

variable {P : CycleBoundaryPresentation E pq}

/-- The union of the boundaries lies in the intersection of the cycles. -/
theorem boundary_le_cycle (h : InfinityBounds P) :
    h.boundaryInfinity ≤ h.cycleInfinity := by
  apply h.boundary_isLUB.2
  intro B hB
  rcases hB with ⟨r, rfl⟩
  apply h.cycle_isGLB.2
  intro Z hZ
  rcases hZ with ⟨s, rfl⟩
  rcases le_total r.1 s.1 with hrs | hsr
  · exact (P.boundary_monotone r.2 hrs).trans
      (P.boundary_le_cycle s.1 s.2)
  · exact (P.boundary_le_cycle r.1 r.2).trans
      (P.cycle_antitone s.2 hsr)

end InfinityBounds

/-- Weibel's infinity page `E^∞ = Z^∞/B^∞` at the chosen bidegree. -/
noncomputable def infinityPage (P : CycleBoundaryPresentation E pq) (h : InfinityBounds P) : C :=
  cokernel (Subobject.ofLE h.boundaryInfinity h.cycleInfinity h.boundary_le_cycle)

end CycleBoundaryPresentation

end LeanCategories.Homological
