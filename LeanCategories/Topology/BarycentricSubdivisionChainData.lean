/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.BarycentricSubdivision
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Barycentric subdivision on singular chains: definition data

Definition-level realization of Hatcher FC07-C02-U036.

For a singular \(n\)-simplex, barycentric subdivision is the signed sum of
the affine \(n\)-simplices coming from maximal flags of nonempty faces of the
standard simplex.  Maximal flags are indexed here by permutations of the
vertices.  The sign of the permutation gives the orientation coefficient.

Sweep III records only the degreewise homomorphism on singular chains.  The
affine simplex for a maximal face flag is constructed directly by barycentric
interpolation of the face barycenters.  Boundary compatibility and the prism
homotopy remain result content.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicTopology

namespace LeanCategories.Topology

/-- The maximal face flag associated to an ordering of the vertices.  At
position `j` it consists of the first `j + 1` vertices in that ordering. -/
def maximalBarycentricFaceFlag {n : ℕ}
    (π : Equiv.Perm (Fin (n + 1))) : BarycentricFaceFlag n n :=
  fun j =>
    (Finset.Iic j).image π

/-- Source coordinate prescription for the affine simplex associated to a
barycentric face flag.  The `j`th source vertex is sent to the barycenter of
the `j`th face. -/
def IsAffineBarycentricFaceFlagMap {n r : ℕ}
    (F : BarycentricFaceFlag n r)
    (f : C(stdSimplex ℝ (Fin (r + 1)), stdSimplex ℝ (Fin (n + 1)))) : Prop :=
  ∀ (w : stdSimplex ℝ (Fin (r + 1))) (i : Fin (n + 1)),
    f w i =
      ∑ j : Fin (r + 1),
        w j * faceBarycenterCoordinates (F j) i

/-- Every coordinate of a face barycenter is nonnegative. -/
lemma faceBarycenterCoordinates_nonneg {n : ℕ}
    (F : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    0 ≤ faceBarycenterCoordinates F i := by
  classical
  simp only [faceBarycenterCoordinates]
  split_ifs
  · positivity
  · exact le_rfl

/-- The barycentric coordinates of a nonempty face sum to one. -/
lemma sum_faceBarycenterCoordinates_eq_one {n : ℕ}
    (F : Finset (Fin (n + 1))) (hF : F.Nonempty) :
    ∑ i, faceBarycenterCoordinates F i = 1 := by
  classical
  simp only [faceBarycenterCoordinates]
  rw [← Finset.sum_filter]
  simp [hF.card_ne_zero]

/-- Each face in a maximal permutation flag is nonempty. -/
lemma maximalBarycentricFaceFlag_nonempty {n : ℕ}
    (π : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    (maximalBarycentricFaceFlag π j).Nonempty := by
  classical
  refine ⟨π 0, ?_⟩
  simp [maximalBarycentricFaceFlag]

/-- The affine simplex associated to a maximal barycentric face flag,
constructed directly from its barycentric-coordinate formula. -/
noncomputable def maximalBarycentricAffineMap {n : ℕ}
    (π : Equiv.Perm (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) where
  toFun w :=
    ⟨fun i => ∑ j : Fin (n + 1),
      w j * faceBarycenterCoordinates (maximalBarycentricFaceFlag π j) i, by
      constructor
      · intro i
        exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (stdSimplex.zero_le w j)
            (faceBarycenterCoordinates_nonneg _ _)
      · calc
          ∑ i, ∑ j : Fin (n + 1),
              w j * faceBarycenterCoordinates (maximalBarycentricFaceFlag π j) i =
              ∑ j, w j * ∑ i,
                faceBarycenterCoordinates (maximalBarycentricFaceFlag π j) i := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [Finset.mul_sum]
          _ = ∑ j, w j := by
                apply Finset.sum_congr rfl
                intro j _
                rw [sum_faceBarycenterCoordinates_eq_one _
                  (maximalBarycentricFaceFlag_nonempty π j), mul_one]
          _ = 1 := stdSimplex.sum_eq_one w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

/-- One maximal barycentric subsimplex of a singular simplex, indexed by a
permutation of the original vertices. -/
noncomputable def barycentricSubsimplexData
    (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (π : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  (X.toSSetObjEquiv _).symm
    ((X.toSSetObjEquiv _ σ).comp
      (maximalBarycentricAffineMap π))

/-- The signed barycentric subdivision chain associated to one singular
`n`-simplex. -/
noncomputable def singularSimplexBarycentricSubdivisionData
    (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).X n :=
  ∑ π : Equiv.Perm (Fin (n + 1)),
    (Equiv.Perm.sign π : ℤ) •
      (TopCat.toSSet.obj X).ιChainComplex
        (barycentricSubsimplexData X n σ π)

/-- Hatcher's barycentric subdivision homomorphism in degree `n`, obtained by
extending the signed subdivision of each singular simplex linearly.  No
boundary-commutation law is bundled into this definition. -/
noncomputable def singularBarycentricSubdivisionComponentData
    (X : TopCat.{0}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).X n :=
  Sigma.desc (singularSimplexBarycentricSubdivisionData X n)

/-- The all-degree family underlying singular barycentric subdivision.  The
assertion that this family is a chain map belongs to the theorem layer. -/
noncomputable def singularBarycentricSubdivisionData
    (X : TopCat.{0}) :
    ∀ n : ℕ,
      ((TopCat.toSSet.obj X).chainComplex
          (ModuleCat.of ℤ ℤ)).X n ⟶
        ((TopCat.toSSet.obj X).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  singularBarycentricSubdivisionComponentData X

end LeanCategories.Topology
