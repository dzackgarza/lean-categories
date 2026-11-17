/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FibreRefinement
public import LeanCategories.Lattices.Valued.Semifan

/-!
# Controls for the refinement step of Lemma 6.6 (#168)

The refinement step of Looijenga, Lemma 6.6, p. 30, is carried by `FibreRefinement.lean`: refinement
of one locally rational decomposition by another (`Refines`, `RefinesLocus`), the least containing
coarse member with its uniqueness (`IsLeastMem`, `exists_least_mem_of_le`), and the support-space
inclusion `V_σ ⊆ V_{σ'}` (`vSigma_le_of_refines`). These are the compile-level controls of that
module: each declaration here consumes the new API, so each fails to elaborate against the tree
before it, and none of them assumes a least member, a support inclusion or a support-index
domination.

* Refinement is a preorder, so the refinement hypothesis composes.
* The least member of the facial decomposition `Σ(bb)` containing a member of any locally rational
  decomposition exists and is unique — the source's "in particular `Σ' = Σ(bb)`", with the
  refinement `refines_facialDecomposition` doing the work.
* At the source's principal instance — an arbitrary family `S` refining the Baily-Borel
  decomposition fibre by fibre (Example 6.2, p. 29, condition (i) of Definition 6.1 in `Semifan`) —
  the support space of a member of a conical fibre is contained in that of its least Baily-Borel
  member.
-/

@[expose] public section

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued.FibreRefinementTests

variable {V : Type} [AddCommGroup V] [Module ℚ V]

/-- Refinement is reflexive. -/
example (S : Set (PointedCone ℝ (realified V))) : Refines S S := Refines.refl S

/-- Refinement is transitive, so refinement hypotheses compose. -/
example {S T U : Set (PointedCone ℝ (realified V))} (h₁ : Refines S T) (h₂ : Refines T U) :
    Refines S U := h₁.trans h₂

/-- **The least face of `C₊` containing a member of a locally rational decomposition exists and is
unique** (Looijenga, Lemma 6.6, p. 30, text line 823, the case `Σ' = Σ(bb)`): the coarse family is
the facial decomposition, which `refines_facialDecomposition` shows is refined by any locally
rational decomposition of `C₊`, and `IsLeastMem.eq` makes the member a function of `σ`. -/
example [Module.Finite ℚ V] {C : PointedCone ℝ (realified V)}
    (hsal : ((rationalClosure C : PointedCone ℝ (realified V)) :
      ConvexCone ℝ (realified V)).Salient)
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ S) :
    ∃ F : PointedCone ℝ (realified V),
      IsLeastMem (facialDecomposition (rationalClosure C)) σ F ∧
        ∀ G : PointedCone ℝ (realified V),
          IsLeastMem (facialDecomposition (rationalClosure C)) σ G → F = G := by
  obtain ⟨F, hF⟩ := exists_least_mem_facialDecomposition hsal hS hσ
  exact ⟨F, hF, fun G hG => IsLeastMem.eq hF hG⟩

/-- **`V_σ ⊆ V_{σ'}` in a conical fibre, for an arbitrary fine family refining Baily-Borel**
(Looijenga, Lemma 6.6, p. 30; Example 6.2, p. 29): the coarse family is `Σ(bb)`, the facial
decomposition of each fibre, which `Semifan.bailyBorel_condition_i` certifies as a locally rational
decomposition, and the refinement is `refines_facialDecomposition`, fibre by fibre. The hypotheses
on the signature of the fibre are those of Example 6.2 (`sigPos` and nondegeneracy of `fibreForm`,
§1B, p. 11), carried for every fibre as in `Semifan`. -/
example [Module.Finite ℚ V] {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    (hpos : ∀ F' : ConicalLine BQ Q, sigPos (fibreForm Q F'.space) = 1)
    (hnd : ∀ F' : ConicalLine BQ Q, (fibreForm Q F'.space).Nondegenerate)
    {S : ∀ F' : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F'.space))}
    (hfine : ∀ F' : ConicalLine BQ Q, IsLocallyRationalDecomposition F'.closure (S F'))
    (F : ConicalLine BQ Q) {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ S F) :
    ∃ σ' : PointedCone ℝ (realified ↥F.space),
      IsLeastMem (facialDecomposition F.closure) σ σ' ∧ vSigma F σ ≤ vSigma F σ' :=
  vSigma_le_of_refines (fun F' => bailyBorel_condition_i F' (hpos F') (hnd F'))
    (fun F' => refines_facialDecomposition (hfine F')) F hσ

end LeanCategories.Lattices.Valued.FibreRefinementTests
