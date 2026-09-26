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

Sweep III records only the degreewise homomorphism on singular chains.
Affine flag-simplex maps are supplied as exact data satisfying the displayed
coordinate prescription; no arbitrary continuous map is selected before its
existence theorem.  Boundary compatibility and the prism homotopy remain
result content.
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

/-- Source-faithful affine flag-simplex data: a continuous simplex map
together with the exact barycentric coordinate prescription. -/
abbrev AffineBarycentricFaceFlagMapData {n r : ℕ}
    (F : BarycentricFaceFlag n r) :=
  {f : C(stdSimplex ℝ (Fin (r + 1)), stdSimplex ℝ (Fin (n + 1))) //
    IsAffineBarycentricFaceFlagMap F f}

/-- A source-facing family of valid affine maps for all barycentric face
flags. Existence of such a family is theorem content. -/
structure BarycentricAffineMapSystemData where
  map : ∀ {n r : ℕ} (F : BarycentricFaceFlag n r),
    AffineBarycentricFaceFlagMapData F

/-- One maximal barycentric subsimplex of a singular simplex, indexed by a
permutation of the original vertices. -/
noncomputable def barycentricSubsimplexData
    (D : BarycentricAffineMapSystemData)
    (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (π : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  (X.toSSetObjEquiv _).symm
    ((X.toSSetObjEquiv _ σ).comp
      (D.map (maximalBarycentricFaceFlag π)).1)

/-- The signed barycentric subdivision chain associated to one singular
`n`-simplex. -/
noncomputable def singularSimplexBarycentricSubdivisionData
    (D : BarycentricAffineMapSystemData)
    (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).X n :=
  ∑ π : Equiv.Perm (Fin (n + 1)),
    (Equiv.Perm.sign π : ℤ) •
      (TopCat.toSSet.obj X).ιChainComplex
        (barycentricSubsimplexData D X n σ π)

/-- Hatcher's barycentric subdivision homomorphism in degree `n`, obtained by
extending the signed subdivision of each singular simplex linearly.  No
boundary-commutation law is bundled into this definition. -/
noncomputable def singularBarycentricSubdivisionComponentData
    (D : BarycentricAffineMapSystemData)
    (X : TopCat.{0}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).X n :=
  Sigma.desc (singularSimplexBarycentricSubdivisionData D X n)

/-- The all-degree family underlying singular barycentric subdivision.  The
assertion that this family is a chain map belongs to the theorem layer. -/
noncomputable def singularBarycentricSubdivisionData
    (D : BarycentricAffineMapSystemData)
    (X : TopCat.{0}) :
    ∀ n : ℕ,
      ((TopCat.toSSet.obj X).chainComplex
          (ModuleCat.of ℤ ℤ)).X n ⟶
        ((TopCat.toSSet.obj X).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  singularBarycentricSubdivisionComponentData D X

end LeanCategories.Topology
