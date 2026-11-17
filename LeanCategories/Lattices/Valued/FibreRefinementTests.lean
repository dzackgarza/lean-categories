/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FibreRefinement
public import LeanCategories.Lattices.Valued.Semifan
public import LeanCategories.Lattices.Valued.SemifanArrangement

/-!
# Controls for the refinement step of Lemma 6.6 (#168)

The refinement step of Looijenga, Lemma 6.6, p. 30, is carried by `FibreRefinement.lean`: refinement
of one locally rational decomposition by another (`Refines`, `RefinesLocus`), the least containing
coarse member with its uniqueness (`IsLeastMem`, `exists_least_mem_of_le`), and the span inclusion
`vSigma F σ ≤ vSigma F σ'` at the least coarse member (`vSigma_le_of_refines`), which is the
source's `V_σ ⊆ V_{σ'}` for the members that Definition 6.1 (i) covers. These are the compile-level
controls of that module: each declaration here consumes the new API, so each fails to elaborate
against the tree before it, and none of them assumes a least member, a support inclusion or a
support-index domination.

* Refinement is a preorder, so the refinement hypothesis composes.
* The least member of the facial decomposition `Σ(bb)` containing a member of any locally rational
  decomposition exists and is unique — the source's "in particular `Σ' = Σ(bb)`", with the
  refinement `refines_facialDecomposition` doing the work.
* At the source's principal instance — an arbitrary family `S` refining the Baily-Borel
  decomposition fibre by fibre (Example 6.2, p. 29, condition (i) of Definition 6.1 in `Semifan`) —
  the span inclusion `vSigma F σ ≤ vSigma F σ'` holds at the least Baily-Borel member above a member
  of a conical fibre, which is the source's `V_σ ⊆ V_{σ'}` for the members of case (i).
* In `realified (ℚ × ℚ)`, the least member of `{⊥, rightHalfPlane}` above the ray through `(1, 1)`
  is the half-plane, read off the family, and the covering family `{rightHalfPlane, leftHalfPlane}`
  is rejected by `Refines`: a cover is not a refinement.

The last item is the positive/separating control: a least member known independently of
`exists_least_mem_of_le`, paired with a family that covers and still refines nothing. No conical
fibre is constructed here: `vSigma_le_of_refines_of_not_isotropicHalfLine` needs a `ConicalLine` —
a `ℚ`-isotropic line, a hyperbolic partner and a positive sheet, over a concrete quadratic form on a
realified space — so the non-ray hypothesis is not instantiated in this file rather than being
assumed true for an empty one.
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

/-! ## Two plane-sized controls: a least member read off a family, and a cover that does not refine

The two smallest semantic examples these predicates admit, both in `realified (ℚ × ℚ)` and both from
cone constructors the repository already has — `halfspaceCone` for the half-planes,
`PointedCone.hull` for a ray, `⊥` and `⊤`.

Neither is a specialization of a theorem of `FibreRefinement`: the first writes down a least member
and checks the three fields of `IsLeastMem` against it, and `IsLeastMem.eq` then says nothing else
is one; the second exhibits a covering family that `Refines` rejects.

The pair is the point. `Refines` asks for a *member* of the coarse family above each member of the
fine one, while the covering clause of Definition 4.2 is about the union alone, so a family can
cover the whole plane and still refine nothing.
-/

/-- The first coordinate on `realified (ℚ × ℚ)`, as a real linear form. -/
noncomputable def planeFst : realified (ℚ × ℚ) →ₗ[ℝ] ℝ := realifiedForm (LinearMap.fst ℚ ℚ ℚ)

@[simp] theorem planeFst_rationalPoint (a b : ℚ) :
    planeFst (rationalPoint (a, b)) = (a : ℝ) := by
  rw [planeFst, realifiedForm_rationalPoint]
  rfl

/-- The closed right half-plane `{x | 0 ≤ x₁}`. -/
noncomputable def rightHalfPlane : PointedCone ℝ (realified (ℚ × ℚ)) := halfspaceCone planeFst

/-- The closed left half-plane `{x | x₁ ≤ 0}`. -/
noncomputable def leftHalfPlane : PointedCone ℝ (realified (ℚ × ℚ)) := halfspaceCone (-planeFst)

theorem mem_rightHalfPlane {x : realified (ℚ × ℚ)} : x ∈ rightHalfPlane ↔ 0 ≤ planeFst x :=
  Iff.rfl

theorem mem_leftHalfPlane {x : realified (ℚ × ℚ)} : x ∈ leftHalfPlane ↔ planeFst x ≤ 0 := by
  rw [leftHalfPlane, mem_halfspaceCone, LinearMap.neg_apply, neg_nonneg]

/-- The ray through `(1, 1)`. -/
noncomputable def diagonalRay : PointedCone ℝ (realified (ℚ × ℚ)) :=
  PointedCone.hull ℝ {rationalPoint ((1 : ℚ), (1 : ℚ))}

/-- **The least member of a two-member family, read off the family** (Looijenga, Lemma 6.6, p. 30,
"the smallest member of `Σ'` that contains `σ`"): the ray through `(1, 1)` lies in the right
half-plane, and the only other member of `{⊥, rightHalfPlane}` is `⊥`, which cannot hold the ray
because the ray holds the nonzero vector `(1, 1)`. So the half-plane is the least member above the
ray, known by inspection and not by minimizing a rank, and `IsLeastMem.eq` says it is the only
one. -/
example :
    IsLeastMem ({⊥, rightHalfPlane} : Set (PointedCone ℝ (realified (ℚ × ℚ)))) diagonalRay
        rightHalfPlane ∧
      ∀ σ' : PointedCone ℝ (realified (ℚ × ℚ)),
        IsLeastMem ({⊥, rightHalfPlane} : Set (PointedCone ℝ (realified (ℚ × ℚ)))) diagonalRay σ' →
          σ' = rightHalfPlane := by
  have hleast : IsLeastMem ({⊥, rightHalfPlane} : Set (PointedCone ℝ (realified (ℚ × ℚ))))
      diagonalRay rightHalfPlane := by
    refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      obtain ⟨c, hc0, rfl⟩ := PointedCone.mem_hull_singleton.1 hx
      rw [mem_rightHalfPlane, map_smul, smul_eq_mul, planeFst_rationalPoint]
      simpa using hc0
    · intro τ hτ hle
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
      rcases hτ with rfl | rfl
      · have hzero : rationalPoint ((1 : ℚ), (1 : ℚ)) ∈
            (⊥ : PointedCone ℝ (realified (ℚ × ℚ))) :=
          hle (PointedCone.subset_hull (Set.mem_singleton _))
        rw [Submodule.mem_bot] at hzero
        exact absurd hzero (rationalPoint_ne_zero (by decide))
      · exact le_rfl
  exact ⟨hleast, fun σ' h' => IsLeastMem.eq h' hleast⟩

/-- The two half-planes cover the plane. -/
example : ((rightHalfPlane : Set (realified (ℚ × ℚ))) ∪ leftHalfPlane) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  change x ∈ rightHalfPlane ∨ x ∈ leftHalfPlane
  rw [mem_rightHalfPlane, mem_leftHalfPlane]
  rcases le_total 0 (planeFst x) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **A cover is not a refinement**: `{rightHalfPlane, leftHalfPlane}` covers the whole plane, yet
`Refines {⊤} {rightHalfPlane, leftHalfPlane}` is false, because `⊤` lies in neither member —
`(-1, 0)` is outside the right half-plane and `(1, 0)` outside the left one. This is the separation
`Refines` has to make: Definition 4.2's covering clause is about the union, and Lemma 6.6's
"smallest member containing `σ`" is about members. -/
example : ¬ Refines ({⊤} : Set (PointedCone ℝ (realified (ℚ × ℚ))))
    {rightHalfPlane, leftHalfPlane} := by
  intro h
  obtain ⟨τ, hτ, htop⟩ := h ⊤ (Set.mem_singleton ⊤)
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl
  · have hmem : rationalPoint ((-1 : ℚ), (0 : ℚ)) ∈ rightHalfPlane := htop Submodule.mem_top
    rw [mem_rightHalfPlane, planeFst_rationalPoint] at hmem
    norm_num at hmem
  · have hmem : rationalPoint ((1 : ℚ), (0 : ℚ)) ∈ leftHalfPlane := htop Submodule.mem_top
    rw [mem_leftHalfPlane, planeFst_rationalPoint] at hmem
    norm_num at hmem

end LeanCategories.Lattices.Valued.FibreRefinementTests
