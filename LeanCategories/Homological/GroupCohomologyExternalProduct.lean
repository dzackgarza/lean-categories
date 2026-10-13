/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.GroupCohomologyCupProduct

/-!
# External and diagonal cup products in ordinary group cohomology

Weibel, *An Introduction to Homological Algebra* (1994), Construction 6.1.14,
pp. 160--166 (FC05-C06-U016), and §6.7.1, p. 192 (FC05-C06-U090).

The all-degree cup product on ordinary integral group cohomology is ported from the checked FLT
reference in `GroupCohomologyCupProduct`.  The external product is the standard one supplied by
that reference: pull the two classes back along the projections `G × H → G` and `G × H → H`,
then cup them on `G × H`.

For FC05-C06-U090, Weibel defines the same-group cup product by composing this
external product with restriction along the diagonal `G → G × G`. The final
definitions below record that presentation literally, using Mathlib's ordinary
group-cohomology functoriality for the diagonal restriction.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

variable (G : Type) [Group G]
variable (H : Type) [Group H]

/-- Restriction of a trivial integral representation along a group homomorphism maps canonically
to the trivial representation of the source group. -/
def groupCohomologyTrivialRestrictionHom {K L : Type} [Group K] [Group L]
    (f : K →* L) :
    Rep.res f (groupCohomologyTrivialIntRep L) ⟶ groupCohomologyTrivialIntRep K :=
  Rep.ofHom ⟨LinearMap.id, fun _ ↦ by
    show LinearMap.id ∘ₗ LinearMap.id = LinearMap.id ∘ₗ LinearMap.id
    rfl⟩

/-- First projection `G × H → G`. -/
def groupCohomologyFstHom : G × H →* G where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Second projection `G × H → H`. -/
def groupCohomologySndHom : G × H →* H where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Pullback in ordinary group cohomology along the first projection. -/
noncomputable def groupCohomologyFstPullback (n : ℕ) :
    groupCohomology (groupCohomologyTrivialIntRep G) n ⟶
      groupCohomology (groupCohomologyTrivialIntRep (G × H)) n :=
  groupCohomology.map (groupCohomologyFstHom G H)
    (groupCohomologyTrivialRestrictionHom (groupCohomologyFstHom G H)) n

/-- Pullback in ordinary group cohomology along the second projection. -/
noncomputable def groupCohomologySndPullback (n : ℕ) :
    groupCohomology (groupCohomologyTrivialIntRep H) n ⟶
      groupCohomology (groupCohomologyTrivialIntRep (G × H)) n :=
  groupCohomology.map (groupCohomologySndHom G H)
    (groupCohomologyTrivialRestrictionHom (groupCohomologySndHom G H)) n

/-- Weibel's all-degree external cross product with integral coefficients:
`x × y = pr₁^*(x) ∪ pr₂^*(y)`. -/
noncomputable def groupCohomologyCrossProduct (p q r : ℕ) (hr : r = p + q) :
    (groupCohomology (groupCohomologyTrivialIntRep G) p ⊗
        groupCohomology (groupCohomologyTrivialIntRep H) q) ⟶
      groupCohomology (groupCohomologyTrivialIntRep (G × H)) r :=
  (groupCohomologyFstPullback G H p ⊗ₘ groupCohomologySndPullback G H q) ≫
    groupCohomologyCupProduct (G × H) p q r hr

@[simp]
lemma groupCohomologyCrossProduct_tmul (p q r : ℕ) (hr : r = p + q)
    (x : groupCohomology (groupCohomologyTrivialIntRep G) p)
    (y : groupCohomology (groupCohomologyTrivialIntRep H) q) :
    groupCohomologyCrossProduct G H p q r hr (x ⊗ₜ[ℤ] y) =
      groupCohomologyCupProduct (G × H) p q r hr
        (groupCohomologyFstPullback G H p x ⊗ₜ[ℤ]
          groupCohomologySndPullback G H q y) := by
  rfl

/-- The diagonal group homomorphism `G → G × G` used in Weibel's definition of
the cup product (FC05-C06-U090). -/
def groupCohomologyDiagonalHom : G →* G × G where
  toFun g := (g, g)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma groupCohomology_fst_comp_diagonal :
    (groupCohomologyFstHom G G).comp (groupCohomologyDiagonalHom G) =
      MonoidHom.id G := by
  ext g
  rfl

@[simp]
lemma groupCohomology_snd_comp_diagonal :
    (groupCohomologySndHom G G).comp (groupCohomologyDiagonalHom G) =
      MonoidHom.id G := by
  ext g
  rfl

/-- Restriction in ordinary integral group cohomology along the diagonal
`G → G × G`. -/
noncomputable def groupCohomologyDiagonalPullback (n : ℕ) :
    groupCohomology (groupCohomologyTrivialIntRep (G × G)) n ⟶
      groupCohomology (groupCohomologyTrivialIntRep G) n :=
  groupCohomology.map (groupCohomologyDiagonalHom G)
    (groupCohomologyTrivialRestrictionHom (groupCohomologyDiagonalHom G)) n

/-- Weibel's source-level cup product (FC05-C06-U090): form the external
cross product and restrict it along the diagonal `G → G × G`.

The separately constructed `groupCohomologyCupProduct` is the ordinary
inhomogeneous-cochain cup used to realize FC05-C06-U016's external product;
this declaration records the exact cross-product/diagonal presentation used
by the source. -/
noncomputable def groupCohomologyCupProductByDiagonal (p q r : ℕ)
    (hr : r = p + q) :
    (groupCohomology (groupCohomologyTrivialIntRep G) p ⊗
        groupCohomology (groupCohomologyTrivialIntRep G) q) ⟶
      groupCohomology (groupCohomologyTrivialIntRep G) r :=
  groupCohomologyCrossProduct G G p q r hr ≫
    groupCohomologyDiagonalPullback G r

@[simp]
lemma groupCohomologyCupProductByDiagonal_tmul (p q r : ℕ)
    (hr : r = p + q)
    (x : groupCohomology (groupCohomologyTrivialIntRep G) p)
    (y : groupCohomology (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupProductByDiagonal G p q r hr (x ⊗ₜ[ℤ] y) =
      groupCohomologyDiagonalPullback G r
        (groupCohomologyCrossProduct G G p q r hr (x ⊗ₜ[ℤ] y)) := by
  rfl

end LeanCategories.Homological
