/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DiscreteProfiniteModule
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RepresentationTheory.Invariants

/-!
# Continuous cohomology of profinite groups

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.11.11,
pp. 206--215 (FC05-C06-U146).

For a profinite group `G`, continuous cohomology of a discrete `G`-module is
the right derived functor of invariants in the abelian category `C_G` of
discrete modules.  The abelian/enough-injectives instances are theorem-layer
inputs (Weibel 6.11.10), not proved here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u

variable (G : ProfiniteGrp.{u})

/-- The invariants functor on Weibel's category `C_G` of discrete profinite
`G`-modules. -/
noncomputable def discreteProfiniteInvariantsFunctor :
    DiscreteProfiniteModuleCat G ⥤ ModuleCat.{u} ℤ :=
  ObjectProperty.ι (fun A : Rep.{u} ℤ G => IsDiscreteProfiniteModule G A) ⋙
    Rep.invariantsFunctor ℤ G

instance discreteProfiniteInvariantsFunctor_additive :
    (discreteProfiniteInvariantsFunctor G).Additive := by
  dsimp [discreteProfiniteInvariantsFunctor]
  infer_instance

/-- Continuous cohomology `H^n(G;A)` as the `n`th right-derived functor of
invariants in `C_G`.

The typeclass hypotheses are exactly the structural assertions supplied by the
preceding theorem layer: `C_G` is abelian and has enough injectives. -/
noncomputable def continuousProfiniteCohomology
    [Abelian (DiscreteProfiniteModuleCat G)]
    [EnoughInjectives (DiscreteProfiniteModuleCat G)]
    (hF : @Functor.Additive
      (DiscreteProfiniteModuleCat G) (ModuleCat.{u} ℤ) _ _
      (@Abelian.toPreadditive (DiscreteProfiniteModuleCat G) _ _)
      (@Abelian.toPreadditive (ModuleCat.{u} ℤ) _ _)
      (discreteProfiniteInvariantsFunctor G))
    (A : DiscreteProfiniteModuleCat G) (n : ℕ) : ModuleCat.{u} ℤ :=
  (@Functor.rightDerived
      (DiscreteProfiniteModuleCat G) _ (ModuleCat.{u} ℤ) _ _ _ _
      (discreteProfiniteInvariantsFunctor G) hF n).obj A

end LeanCategories.Homological
