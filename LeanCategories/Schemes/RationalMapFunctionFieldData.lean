/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definition-level adaptation of mattrobball/explicit-unirational,
Apache-2.0, revision 67477084d2f2ac7b8c397503d6aec66905a5d70a.
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Function-field pullback data for rational maps

Definition-level realization of Hartshorne FC06-C01-U075.

For a rational map `f : X ⤏ Y`, Mathlib already supplies the function-field
point `f.fromFunctionField : Spec K(X) ⟶ Y`.  Evaluating this point at the
closed point of `Spec K(X)` and applying `Scheme.stalkClosedPointTo` gives the
canonical ring map from the stalk at the actual image point into `K(X)`.

For a dominant map of integral schemes, the checked external reference proves
that the actual image point is the generic point of `Y`.  The prerequisite
generic-point lemmas are ported here and used to construct the transported map
`K(Y) → K(X)` itself.  Algebra compatibility and injectivity remain
result-layer statements.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A dominant morphism of irreducible schemes sends the generic point to the
generic point. -/
theorem mapGenericPointOfDominantData {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  rw [isGenericPoint_def]
  have hsub : Set.range (f : X → Y) ⊆ closure {(f (genericPoint X) : Y)} := by
    rintro _ ⟨x, rfl⟩
    exact (specializes_iff_mem_closure).1
      ((genericPoint_specializes x).map f.continuous)
  have hdense : DenseRange (f : X → Y) := IsDominant.denseRange (f := f)
  rw [denseRange_iff_closure_range] at hdense
  apply Set.eq_univ_of_univ_subset
  calc
    Set.univ = closure (Set.range (f : X → Y)) := hdense.symm
    _ ⊆ closure (closure {(f (genericPoint X) : Y)}) := closure_mono hsub
    _ = closure {(f (genericPoint X) : Y)} := closure_closure

namespace Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The function-field point of a dominant partial map sends the closed point
of `Spec K(X)` to the generic point of the target. -/
theorem partialMapFromFunctionFieldClosedPointData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X.PartialMap Y) [IsDominant f.hom] :
    f.fromFunctionField (IsLocalRing.closedPoint X.functionField) =
      genericPoint Y := by
  have hmem : genericPoint X ∈ f.domain :=
    (genericPoint_specializes _).mem_open f.domain.2
      f.dense_domain.nonempty.choose_spec
  haveI : Nonempty f.domain := ⟨⟨genericPoint X, hmem⟩⟩
  change (f.domain.fromSpecStalkOfMem (genericPoint X) hmem ≫ f.hom)
    (IsLocalRing.closedPoint X.functionField) = genericPoint Y
  rw [Hom.comp_apply]
  have hpt : f.domain.fromSpecStalkOfMem (genericPoint X) hmem
      (IsLocalRing.closedPoint X.functionField) = ⟨genericPoint X, hmem⟩ := by
    apply f.domain.ι.isOpenEmbedding.injective
    have hcomp := Opens.fromSpecStalkOfMem_ι f.domain (genericPoint X) hmem
    have h : (f.domain.fromSpecStalkOfMem (genericPoint X) hmem ≫ f.domain.ι)
        (IsLocalRing.closedPoint _) =
        X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint _) := by
      simp only [hcomp]
    rwa [Hom.comp_apply, fromSpecStalk_closedPoint] at h
  rw [hpt]
  haveI : IsIntegral f.domain.toScheme :=
    isIntegral_of_isOpenImmersion f.domain.ι
  have hgp_dom : genericPoint f.domain.toScheme = ⟨genericPoint X, hmem⟩ :=
    Subtype.ext (genericPoint_eq_of_isOpenImmersion f.domain.ι)
  have h : f.hom (genericPoint f.domain.toScheme) = genericPoint Y :=
    mapGenericPointOfDominantData f.hom
  rwa [← hgp_dom]

/-- The function-field point of a dominant rational map sends the closed point
of `Spec K(X)` to the generic point of the target. -/
theorem rationalMapFromFunctionFieldClosedPointData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⤏ Y) [f.IsDominant] :
    f.fromFunctionField (IsLocalRing.closedPoint X.functionField) =
      genericPoint Y := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  haveI : IsDominant g.hom := by
    rwa [← g.isDominant_toRationalMap_iff]
  simpa using partialMapFromFunctionFieldClosedPointData g

end Scheme

end AlgebraicGeometry

namespace LeanCategories.Schemes

/-- The actual image in `Y` of the closed point of `Spec K(X)` under the
function-field point attached to a rational map. -/
def rationalMapFunctionFieldImagePointData
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⤏ Y) : Y :=
  f.fromFunctionField (IsLocalRing.closedPoint X.functionField)

/-- The stalk of `Y` at the actual image of the function-field point.

For a dominant rational map this is identified with `K(Y)` only after proving
that the image point is generic. -/
abbrev RationalMapFunctionFieldImageStalkData
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⤏ Y) : CommRingCat.{u} :=
  Y.presheaf.stalk (rationalMapFunctionFieldImagePointData f)

/-- Pullback by composition at the actual image stalk of a rational map.

This is the proof-free core of Hartshorne's `φ*`: it is the canonical stalk
map induced by `f.fromFunctionField`. -/
def rationalMapFunctionFieldPullbackAtImageData
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⤏ Y) :
    RationalMapFunctionFieldImageStalkData f ⟶ X.functionField :=
  Scheme.stalkClosedPointTo f.fromFunctionField

/-- Pullback on function fields induced by a dominant rational map. -/
noncomputable def rationalMapFunctionFieldPullbackData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⤏ Y) [f.IsDominant] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr
    (Inseparable.of_eq
      (Scheme.rationalMapFromFunctionFieldClosedPointData f).symm)).hom ≫
    rationalMapFunctionFieldPullbackAtImageData f

/-- Exact graph condition for a `K(Y) → K(X)` map to be the function-field
pullback induced by a dominant rational map.

This compatibility predicate is retained for downstream statements; the source
map itself is constructed above by `rationalMapFunctionFieldPullbackData`. -/
def IsRationalMapFunctionFieldPullbackData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⤏ Y) [f.IsDominant]
    (φ : Y.functionField ⟶ X.functionField) : Prop :=
  ∃ h : rationalMapFunctionFieldImagePointData f = genericPoint Y,
    φ =
      (Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
        rationalMapFunctionFieldPullbackAtImageData f

end LeanCategories.Schemes
