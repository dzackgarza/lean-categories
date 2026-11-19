/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootsAreFolds

/-!
# The converse predicate at the lattice carrier, where the chamber theorem consumes it (`#116`)

`FoldingRootsAreFolds.RootsAreFoldsOfWalls` states AEGS Lemma 3.4's converse (**printed p. 12**)
relative to a wall set, over elementary the invariant lattice's subtype. The chamber theorem
consumes
its consequence at the *lattice carrier* — `isChamberWithWalls_invariant_of_sign_cover` takes
`∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice g), …` — so this file states the same
predicate
directly there and derives the covering without a conversion step.

The one formal point that makes the carrier version writable: the fold must be taken *in the
subtype*. `foldedVector g α` is a vector of the ambient lattice, and coercing it back to the lattice
carrier needs its membership in `M^σ` — which is `foldedVector_mem_fixed` and therefore needs the
involution law. That is why the predicate below takes `hg : g * g = 1`, and why the subtype form of
the previous file takes no such hypothesis.

* `RootsAreFoldsOfWallsCarrier`;
* `signCover_of_rootsAreFoldsOfWallsCarrier` — it implies the covering, at the carrier;
* `hcomplete_of_rootsAreFoldsOfWallsCarrier` — hence `hcomplete`, at the carrier.

## LC-09 record

`rg "RootsAreFoldsOfWalls"` gives the subtype form and its consequences only; no carrier-level form
existed. The coercion `L.carrier → ↥(involutionFixedSubmodule g)` is a *membership*, not a
subtyping, which is what the previous file's docstring records as the "third face" of the carrier
problem — the fix is to carry the membership as data (`foldedVector_mem_fixed`), and that is what
this file does. Nothing ported.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8: Lemma 3.4 and its
  converse (**printed p. 12**), Definition 3.7 (**printed p. 12**), Lemma 3.8 (**printed p. 12**).
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **AEGS Lemma 3.4's converse at the lattice carrier, relative to a wall set**: every negative
reflective root of `M^σ` is a folded wall root or its negative. The fold is taken in `M^σ`, which is
what the involution law is needed for. -/
def RootsAreFoldsOfWallsCarrier (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (hg : g * g = 1)
    (R : Set L.obj.obj.carrier) : Prop :=
  ∀ ρ : (invariantFixedLattice (L := L) g).obj.obj.carrier,
    ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g) →
      ∃ α ∈ R,
        ρ = (⟨foldedVector g α, foldedVector_mem_fixed g hg α⟩ :
              involutionFixedSubmodule g) ∨
        ρ = -(⟨foldedVector g α, foldedVector_mem_fixed g hg α⟩ :
              involutionFixedSubmodule g)

/-- **The carrier form implies the subtype form.** The coercion `↥M^σ → L.carrier` is a genuine
subtyping, so the two statements agree once the fold is read on both sides. -/
theorem rootsAreFoldsOfWalls_of_carrier (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (hg : g * g = 1)
    (R : Set L.obj.obj.carrier)
    (h : RootsAreFoldsOfWallsCarrier (L := L) g hg R) :
    RootsAreFoldsOfWalls (L := L) g R := by
  intro v hv
  obtain ⟨α, hα, hfold | hfold⟩ := h (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) hv
  · refine ⟨α, hα, Or.inl ?_⟩
    have h2 := congrArg (fun w : involutionFixedSubmodule g =>
      (w : L.obj.obj.carrier)) hfold
    exact h2
  · refine ⟨α, hα, Or.inr ?_⟩
    have h2 := congrArg (fun w : involutionFixedSubmodule g =>
      (w : L.obj.obj.carrier)) hfold
    exact h2

/-- **The covering, at the carrier.** -/
theorem signCover_of_rootsAreFoldsOfWallsCarrier (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (hg : g * g = 1)
    (R : Set L.obj.obj.carrier)
    (h : RootsAreFoldsOfWallsCarrier (L := L) g hg R) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ρ ∈ foldedRootSet (L := L) g R ∨ -ρ ∈ foldedRootSet (L := L) g R :=
  signCover_of_rootsAreFoldsOfWalls (L := L) g R
    (rootsAreFoldsOfWalls_of_carrier (L := L) g hg R h)

/-- **Hence `hcomplete`, at the carrier.** -/
theorem hcomplete_of_rootsAreFoldsOfWallsCarrier (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (hg : g * g = 1)
    (R : Set L.obj.obj.carrier)
    (h : RootsAreFoldsOfWallsCarrier (L := L) g hg R) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ∃ v ∈ foldedRootSet (L := L) g R, ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v :=
  hcomplete_of_sign_cover (L := L) g R
    (signCover_of_rootsAreFoldsOfWallsCarrier (L := L) g hg R h)

end LeanCategories.Lattices.Valued
