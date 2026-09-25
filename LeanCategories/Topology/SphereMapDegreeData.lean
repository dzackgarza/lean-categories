/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Degree data for self-maps of spheres

Definition-level realization of Hatcher FC07-C02-U046.

For a continuous self-map of the positive-dimensional sphere, Hatcher defines
its degree to be the integer by which the induced map on top integral singular
homology acts after identifying that homology group with `ℤ`.

Sweep III records exactly that characterization.  The existence and uniqueness
of the top-homology identification and of the resulting integer, together with
all standard degree formulas, are result content and are not proved or bundled
as constructor fields here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open AlgebraicTopology CategoryTheory

/-- Integral singular homology in degree `n` of a topological space. -/
abbrev integralSingularHomologyData (n : ℕ) (X : TopCat.{0}) : ModuleCat.{0} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj X

/-- Top integral singular homology of the standard `n`-sphere. -/
abbrev sphereTopIntegralHomologyData (n : ℕ) : ModuleCat.{0} ℤ :=
  integralSingularHomologyData n (TopCat.sphere.{0} n)

/-- The endomorphism of top integral homology induced by a self-map of
the standard `n`-sphere. -/
def sphereTopIntegralHomologyMapData {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    sphereTopIntegralHomologyData n ⟶ sphereTopIntegralHomologyData n :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f

/-- Hatcher's defining relation for the degree of a sphere self-map:
under an identification `H_n(S^n; ℤ) ≅ ℤ`, the induced map is
multiplication by `d`.

The relation deliberately asks only for the comparison isomorphism; proving
that such an isomorphism exists, and that the integer is independent of it and
unique, is Sweep-IV result work. -/
def IsSphereMapDegreeData {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) (d : ℤ) : Prop :=
  ∃ e : sphereTopIntegralHomologyData n ≅ ModuleCat.of ℤ ℤ,
    e.inv ≫ sphereTopIntegralHomologyMapData f ≫ e.hom =
      d • 𝟙 (ModuleCat.of ℤ ℤ)

/-- Hatcher's degree datum for `f : S^n → S^n`, with the source's
positive-dimension hypothesis explicit.

This is a definition-level selection from the intrinsic degree relation.
Existence and uniqueness of a satisfying integer are deferred to Sweep IV. -/
def sphereMapDegreeData {n : ℕ} (_hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) : ℤ :=
  Classical.epsilon (IsSphereMapDegreeData f)

end LeanCategories.Topology
