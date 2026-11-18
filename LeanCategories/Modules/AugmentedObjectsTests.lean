/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.AugmentedObjects
public import LeanCategories.Modules.TangentFraming

/-!
# Acceptance checks for dzackgarza/lean-categories#62

One `example` per acceptance condition of the issue, discharged by the named declaration of
`LeanCategories.Modules.AugmentedObjects` or `LeanCategories.Modules.TangentFraming`. This module
asserts the *statements*: each example fails to elaborate if the named statement changes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial
open LeanCategories.Modules LeanCategories.Modules.AugmentedGradedObject

namespace LeanCategories.Modules

/-- 1. The epimorphic augmentation `ℤ ↠ ℤ/2` is admitted as a selected augmented object: the
construction demands no cofiber condition. -/
example : AugmentedGradedObject (ModuleCat ℤ) := intCover

/-- 1. Its augmentation is an epimorphism (a free cover). -/
example : Epi intCover.augment := intCover_isFreeCover

/-- 1. Its cofiber does not vanish, so epimorphy does not imply `cofib(ε) ≃ 0`. -/
example : ¬ intCover.CofiberVanishes := intCover_not_cofiberVanishes

/-- 1. The nonzero kernel class `2ℤ` of `ℤ ↠ ℤ/2`. -/
example : (2 : ℤ) ∈ LinearMap.ker (ModuleCat.Hom.hom intToZModTwo) := two_mem_ker_intToZModTwo

/-- 2. The identity `ℤ ≅ ℤ` is a length-zero framing. -/
example : intFraming.IsFraming := intFraming_isFraming

/-- 2. Its cofiber vanishes. -/
example : intFraming.CofiberVanishes := intFraming_cofiberVanishes

/-- 2. A framing retains no chosen term above degree zero. -/
example : intFraming.LengthLe 1 := intFraming_isFraming.lengthLe

/-- 3. The truncated selected object keeps termwise free terms. -/
example : intTruncated.TermwiseFree := intTruncated_termwiseFree

/-- 3. Projectivity is an independently imposed degreewise classifier. -/
example : ObjectProperty (AugmentedGradedObject (ModuleCat ℤ)) := TermwiseProjective ℤ

/-- 3. A truncation implies no exactness at its last retained term. -/
example : ¬ intTruncated.TruncatedExact 1 := intTruncated_not_truncatedExact

/-- 3. The truncation is an actual morphism of selected diagrams, retaining the augmentation and
the chosen term in degree `0` by the identity. -/
example : intCover ⟶ intKoszul :=
  coverToTwoTerm ℤ (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ (ZMod 2)) twoMul
    intToZModTwo twoMul_comp_intToZModTwo

/-- 3. Truncation is an independently imposed refinement, and its levels are nested. -/
example : TruncationRefinement (C := ModuleCat ℤ) 1 ≤ TruncationRefinement (C := ModuleCat ℤ) 2 :=
  truncationRefinement_mono (by omega)

/-- 3. Forgetting the truncation refinement commutes with the underlying augmentation. -/
example (k : ℕ) :
    refinementPoint (C := ModuleCat ℤ) (TruncationRefinement (C := ModuleCat ℤ) k) =
      (TruncationRefinement (C := ModuleCat ℤ) k).ι ⋙ pointFunctor (C := ModuleCat ℤ) :=
  truncationRefinementPoint_eq k

/-- 3. The general truncation keeps every chosen term below `k`. -/
example (k n : ℕ) (h : n < k) : (intKoszul.truncate k).term n = intKoszul.term n :=
  truncate_term_of_lt intKoszul h

/-- 3. ... kills every chosen term in degree `k` and above -/
example (k n : ℕ) (h : k ≤ n) : IsZero ((intKoszul.truncate k).term n) := by
  rw [truncate_term_of_ge intKoszul h]
  exact isZero_zero _

/-- 3. ... has length at most `k` -/
example (k : ℕ) : (intKoszul.truncate k).LengthLe k := truncate_lengthLe intKoszul k

/-- 3. ... and truncating twice at the same degree changes nothing. -/
example (k : ℕ) : ((intKoszul.truncate k).truncate k).term =
    (intKoszul.truncate k).term :=
  truncate_idem_term intKoszul k

/-- 4. The same underlying augmented model is a full resolution. -/
example : intKoszul.CofiberVanishes := intKoszul_cofiberVanishes

/-- 4. ... with amplitude two -/
example : intKoszul.LengthLe 2 := intKoszul_lengthLe_two

/-- 4. ... while its amplitude is not one: length and truncation are separate. -/
example : ¬ intKoszul.LengthLe 1 := intKoszul_not_lengthLe_one

/-- 4. ... and it is `F`-acyclic for the forgetful functor to abelian groups. -/
example : intKoszul.IsAcyclicFor (forget₂ (ModuleCat ℤ) AddCommGrpCat) :=
  intKoszul_isAcyclicFor_forget

/-- 4. The realization of a selected augmented object under a functor: the chosen diagram is carried
into the enhancement degreewise. -/
example : AugmentedGradedObject (ModuleCat ℤ) := realize (𝟭 (ModuleCat ℤ)) intCover

/-- 4. The realized augmentation is an object of the slice `E_{/j(X)}`, not a new augmented object:
this is the correction recorded on the issue. -/
example : Over (intCover.point) := realization (𝟭 (ModuleCat ℤ)) intCover

/-- 4. A vanishing cofiber selects a full resolution after realization. -/
example : intKoszul.IsAcyclicFor (forget₂ (ModuleCat ℤ) AddCommGrpCat) :=
  isAcyclicFor_of_cofiberVanishes (forget₂ (ModuleCat ℤ) AddCommGrpCat) intKoszul_cofiberVanishes

/-- 5. The module framing case: a one-term object is a framing exactly when its augmentation is an
isomorphism. -/
example (P M : ModuleCat ℤ) (ε : P ⟶ M) :
    (oneTerm ℤ P M ε).IsFraming ↔ IsIso ε := oneTerm_isFraming_iff (R := ℤ) ε

/-- 5. The tangent-sheaf framing case is the general framing condition read in the category of
sheaves of `O_X`-modules. -/
example (X : TopCat) (S : AugmentedGradedObject (X.Sheaf (ModuleCat ℤ))) :
    S.IsFraming ↔ IsIso S.augment ∧ S.LengthLe 1 := sheafFraming_iff ℤ X S

/-- 5. Applying global sections to a framing of sheaves of modules is a consequence, not the
definition. -/
example (X : TopCat) {F T : X.Sheaf (ModuleCat ℤ)} (φ : F ⟶ T) [IsIso φ] :
    IsIso ((globalSections ℤ X).map φ) := sheafFraming_sections ℤ X φ

/-- 5. `O_X^{⊕n}` is the free sheaf of `O_X`-modules of rank `n`. -/
example {C : Type} [Category C] (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat] (R : Sheaf J RingCat) (n : ℕ) :
    SheafOfModules R := FreeSheaf (J := J) R n

/-- 5. A tangent framing of a sheaf of `O_X`-modules is an isomorphism of sheaves of modules. -/
example {C : Type} [Category C] (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat] (R : Sheaf J RingCat) (n : ℕ)
    (T : SheafOfModules R) (φ : FreeSheaf (J := J) R n ⟶ T) :
    IsTangentFraming R T φ ↔ IsIso φ := tangentFraming_iff_isIso R T φ

/-- 5. The parallelizable instance: the free sheaf carries the identity as a tangent framing. -/
example {C : Type} [Category C] (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat] (R : Sheaf J RingCat) (n : ℕ) :
    IsTangentFraming R (FreeSheaf (J := J) R n) (𝟙 _) := isTangentFraming_free R n

/-- 5. The tangent module of the affine line is the module of vector fields, and it is free of rank
one: a derivation of `R[X]` is determined by its value at `X`. -/
example : AffineLineTangent ℤ ≃ₗ[ℤ[X]] ℤ[X] := affineLineTangentEquiv (R := ℤ)

/-- 5. The affine line is parallelizable: its tangent module carries a framing. -/
example : (oneTerm ℤ[X] (ModuleCat.of ℤ[X] ℤ[X]) (ModuleCat.of ℤ[X] (AffineLineTangent ℤ))
    (affineLineTangentIso ℤ).hom).IsFraming := affineLineTangent_isFraming (R := ℤ)

/-- 5. The tangent sheaf of the affine line exists: it is `tilde` of the module of vector fields, a
sheaf of `O_{Spec R[X]}`-modules. -/
example : (AlgebraicGeometry.Spec (CommRingCat.of ℤ[X])).Modules := AffineLineTangentSheaf ℤ

/-- 5. It carries a tangent framing: a chosen isomorphism of sheaves of modules
`O_{𝔸¹}^{⊕1} ⟶ T_{𝔸¹}`. -/
example : AffineLineFreeSheaf ℤ ≅ AffineLineTangentSheaf ℤ := affineLineTangentSheafFraming ℤ

/-- 5. That framing is an isomorphism of sheaves of `O_{Spec R[X]}`-modules. -/
example : IsIso (affineLineTangentSheafFraming ℤ).hom :=
  affineLineTangentSheafFraming_isIso (R := ℤ)

/-- 6. Forgetting a refinement and forgetting the selected diagram commute definitionally. -/
example (P : ObjectProperty (AugmentedGradedObject (ModuleCat ℤ))) :
    refinementPoint (C := ModuleCat ℤ) P = P.ι ⋙ pointFunctor (C := ModuleCat ℤ) :=
  refinementPoint_eq P

/-- 6. A finer refinement forgets through the coarser one without changing the augmentation. -/
example (P Q : ObjectProperty (AugmentedGradedObject (ModuleCat ℤ))) (h : P ≤ Q) :
    ObjectProperty.ιOfLE h ⋙ refinementPoint (C := ModuleCat ℤ) Q =
      refinementPoint (C := ModuleCat ℤ) P :=
  refinementPoint_ιOfLE P Q h

/-- 6. The basis-preserving (diagram) convention is strictly finer than the convention of arbitrary
maps of the underlying modules: two morphisms agree on the augmentation point and differ on a
chosen term. -/
example : ∃ f g : intCover ⟶ intCover, Hom.point f = Hom.point g ∧ f ≠ g :=
  exists_hom_same_point_ne

end LeanCategories.Modules
