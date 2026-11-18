/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Selected augmented objects: augmentations, cofibers, truncations and framings

The single owner of FOUNDATIONS.md, *Governing construction* (before Definition 13.10) and
Definitions 76.1--76.3, tracked as dzackgarza/lean-categories#62.

The object of study is a **selected** augmented graded object: chosen terms `P_0, P_1, P_2, ...`,
chosen differentials `d_n : P_{n+1} ⟶ P_n` with `d_n d_{n+1} = 0`, and a chosen augmentation
`ε : P_0 ⟶ X` with `ε d_1 = 0` (Definition 76.1). Nothing else is imposed: the augmentation need
not be an epimorphism, a monomorphism or an isomorphism, the selected diagram need not be exact in
any degree, and the terms need not be free, projective or flat.

`AugmentedGradedObject C` is that owner. Each classifier the text keeps independent is a predicate
on it rather than a primitive case class:

* `AugmentedGradedObject.Termwise P`, a degreewise classifier;
* `AugmentedGradedObject.ExactAt k`, `TruncatedExact S n`, `CofiberVanishes S`, `IsResolution S`;
* `AugmentedGradedObject.LengthLe S N`, the amplitude condition, independent of truncation;
* `AugmentedGradedObject.IsFraming`, `LengthLe 1` together with `IsIso ε`;
* `AugmentedGradedObject.IsFreeCover`, `Epi ε` alone;
* `AugmentedGradedObject.IsAcyclicFor F`, the `F`-acyclic refinement for a functor `F` out of `C`.

Morphisms retain the whole selected diagram: `Hom` carries a map of every term and of the
augmentation point, commuting with every chosen differential and with `ε` (`Hom.comm_diff`,
`Hom.comm_augment`). `pointFunctor` forgets the diagram and keeps `X`, and the forgetful functor of
any refinement `Refinement P ⥤ C` is `(Refinement P).ι ⋙ pointFunctor`, so the two forgetful
conventions commute by `rfl` (`refinementPoint_eq`). The diagram convention is strictly finer than
the convention of arbitrary maps of the underlying modules: `exists_hom_same_point_ne` exhibits two
morphisms of the free cover that agree on the augmentation point and differ on a chosen term.

## Specimens (the acceptance conditions of #62)

In `ModuleCat ℤ`:

* `intCover` is the epimorphic augmentation `ℤ ↠ ℤ/2`: `intCover_isFreeCover` is a free cover with
  no exactness demanded, and `intCover_not_cofiberVanishes` says its cofiber does not vanish, so
  epimorphy does not imply `cofib(ε) ≃ 0` (`two_mem_ker_intToZModTwo` is the nonzero kernel class
  `2ℤ`). `intCover_not_isFraming` refuses the framing condition.
* `intFraming` is the identity `ℤ ≅ ℤ`: `intFraming_isFraming` (a length-zero framing) and
  `intFraming_cofiberVanishes` (its cofiber vanishes).
* `intKoszul` is `0 ⟶ ℤ --2--> ℤ --ε--> ℤ/2`: `intKoszul_cofiberVanishes` is a full resolution,
  `intKoszul_termwiseFree` and `intKoszul_lengthLe_two`, with `intKoszul_not_lengthLe_one` showing
  amplitude and exactness are independent. `intKoszul_isAcyclicFor_forget` is the `F`-acyclic
  refinement for the forgetful functor to abelian groups.
* `intTruncated` is `ℤ --0--> ℤ --ε--> ℤ/2`: `intTruncated_termwiseFree` and
  `intTruncated_isFreeCover` hold while `intTruncated_not_truncatedExact` says that a truncation
  presumes no exactness at its last retained term.
* `exists_hom_same_point_ne` is the morphism-convention distinction.

## Scope

The stable enhancement `j : C ⟶ E`, the cofiber sequence `R^• → j(X) → cofib(ε) → Σ R^•` and the
identification of `cofib(ε) ≃ 0` with an equivalence are stated in the ordinary abelian setting,
where `CofiberVanishes` is acyclicity of the mapping cone of `ε`. No stable infinity-category,
`Sp(C)` or `D(C)` is constructed: for an arbitrary `C` those do not exist, which is what the
governing construction insists on. The ambient category is additive (`Preadditive C`), which is the
setting in which augmented chain complexes exist at all (FOUNDATIONS Definition 77.1).

The module case of the framing is realized above (`IsFraming` at `C = ModuleCat R`, together with
`oneTerm_isFraming_iff`). The tangent-sheaf case of Remark 13.12 is available in the same sense
(`sheafFraming_iff` reads `IsFraming` in `Sh(X, Mod O_X)`, and `sheafFraming_sections` records that
applying global sections afterwards is a consequence), but no tangent sheaf `T_X` of a smooth
manifold and no free sheaf `O_X^{⊕n}` are constructed in this file; a specimen isomorphism
`O_X^{⊕n} → T_X` therefore does not exist here.
-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories.Modules

universe u v w

section General

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The selected terms and differentials of FOUNDATIONS Definition 76.1: chosen maps
`d_n : P_{n+1} ⟶ P_n` with `d_n d_{n+1} = 0`. -/
structure GradedDifferential where
  /-- the chosen term in each degree -/
  term : ℕ → C
  /-- the chosen differential `P_{n+1} ⟶ P_n` -/
  diff : ∀ n : ℕ, term (n + 1) ⟶ term n
  /-- consecutive chosen differentials compose to zero -/
  comp_diff : ∀ n : ℕ, diff (n + 1) ≫ diff n = 0

/-- FOUNDATIONS Definition 76.1: an augmented graded object over `X` is the selected terms and
differentials together with a chosen augmentation `ε : P_0 ⟶ X` satisfying `ε d_1 = 0`.

No exactness, epimorphy or termwise condition is part of this structure. -/
structure AugmentedGradedObject extends GradedDifferential C where
  /-- the augmentation target `X` -/
  point : C
  /-- the chosen augmentation `P_0 ⟶ X` -/
  augment : term 0 ⟶ point
  /-- the augmentation kills the chosen differential out of `P_1` -/
  comp_augment : diff 0 ≫ augment = 0

namespace AugmentedGradedObject

variable {C}

/-- A morphism of selected augmented objects: maps of the augmentation point and of every chosen
term, commuting with every chosen differential and with the augmentation. -/
@[ext]
structure Hom (S T : AugmentedGradedObject C) where
  /-- the map of augmentation points -/
  point : S.point ⟶ T.point
  /-- the map of the chosen term in each degree -/
  term : ∀ n : ℕ, S.term n ⟶ T.term n
  /-- the chosen differentials are compatible -/
  comm_diff : ∀ n : ℕ, term (n + 1) ≫ T.diff n = S.diff n ≫ term n
  /-- the chosen augmentations are compatible -/
  comm_augment : S.augment ≫ point = term 0 ≫ T.augment

namespace Hom

variable {S T U : AugmentedGradedObject C}

/-- The identity morphism of a selected augmented object. -/
def id (S : AugmentedGradedObject C) : Hom S S where
  point := 𝟙 S.point
  term _ := 𝟙 _
  comm_diff n := by rw [Category.comp_id, Category.id_comp]
  comm_augment := by rw [Category.comp_id, Category.id_comp]

/-- The composite of two morphisms of selected augmented objects. -/
def comp (f : Hom S T) (g : Hom T U) : Hom S U where
  point := f.point ≫ g.point
  term n := f.term n ≫ g.term n
  comm_diff n := by
    rw [Category.assoc, g.comm_diff n, ← Category.assoc, f.comm_diff n, Category.assoc]
  comm_augment := by
    rw [← Category.assoc, f.comm_augment, Category.assoc, g.comm_augment, ← Category.assoc]

end Hom

@[simp]
lemma id_point (S : AugmentedGradedObject C) : Hom.point (Hom.id S) = 𝟙 S.point := rfl

@[simp]
lemma id_term (S : AugmentedGradedObject C) (n : ℕ) : Hom.term (Hom.id S) n = 𝟙 (S.term n) := rfl

@[simp]
lemma comp_point {S T U : AugmentedGradedObject C} (f : Hom S T) (g : Hom T U) :
    Hom.point (Hom.comp f g) = Hom.point f ≫ Hom.point g := rfl

@[simp]
lemma comp_term {S T U : AugmentedGradedObject C} (f : Hom S T) (g : Hom T U) (n : ℕ) :
    Hom.term (Hom.comp f g) n = Hom.term f n ≫ Hom.term g n := rfl

instance : Category (AugmentedGradedObject C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    · rw [comp_point, id_point, Category.id_comp]
    · funext n
      rw [comp_term, id_term, Category.id_comp]
  comp_id f := by
    apply Hom.ext
    · rw [comp_point, id_point, Category.comp_id]
    · funext n
      rw [comp_term, id_term, Category.comp_id]
  assoc f g h := by
    apply Hom.ext
    · rw [comp_point, comp_point, comp_point, comp_point, Category.assoc]
    · funext n
      rw [comp_term, comp_term, comp_term, comp_term, Category.assoc]

/-- The functor forgetting the selected diagram and keeping the augmentation point `X`. -/
def pointFunctor : AugmentedGradedObject C ⥤ C where
  obj S := S.point
  map f := Hom.point f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A degreewise classifier: the chosen term in every degree satisfies `P`. -/
def Termwise (P : ObjectProperty C) : ObjectProperty (AugmentedGradedObject C) :=
  fun S => ∀ n : ℕ, P (S.term n)

/-- The short complex `P_{k+1} ⟶ P_k ⟶ P_{k-1}` of a selected augmented object, with
`P_{-1} := X` in degree `0`. -/
def shortComplex (S : AugmentedGradedObject C) : ℕ → ShortComplex C
  | 0 => ShortComplex.mk (S.diff 0) S.augment S.comp_augment
  | k + 1 => ShortComplex.mk (S.diff (k + 1)) (S.diff k) (S.comp_diff k)

/-- Exactness of the selected augmented object "at degree `k`": at `k = 0` this is
`im d_1 = ker ε`, at `k + 1` it is `im d_{k+2} = ker d_{k+1}`. -/
def ExactAt (S : AugmentedGradedObject C) (k : ℕ) : Prop := (S.shortComplex k).Exact

/-- Exactness in the first `n` degrees. A truncation imposes no exactness at its last retained
term, so this is an independent classifier and not part of the construction. -/
def TruncatedExact (S : AugmentedGradedObject C) (n : ℕ) : Prop := ∀ k : ℕ, k < n → S.ExactAt k

/-- The cofiber of the augmentation vanishes: every degree of the selected augmented object is
exact, i.e. the mapping cone of `ε` is acyclic. This is the condition `cofib(ε) ≃ 0`
(FOUNDATIONS, governing construction); it is optional and an epimorphism does not imply it. -/
def CofiberVanishes (S : AugmentedGradedObject C) : Prop := ∀ k : ℕ, S.ExactAt k

/-- A full resolution is a selected augmented object whose every degree is exact. -/
abbrev IsResolution (S : AugmentedGradedObject C) : Prop := S.CofiberVanishes

/-- The amplitude condition: every chosen term in degree at least `N` is a zero object. This is
independent of the truncation degree. -/
def LengthLe (S : AugmentedGradedObject C) (N : ℕ) : Prop := ∀ k : ℕ, N ≤ k → IsZero (S.term k)

/-- A categorical framing (FOUNDATIONS Definition 13.11 and Remark 13.12): the augmentation is an
isomorphism and no chosen term above degree zero remains. It is the length-zero free-resolution
case, a chosen basis rather than a chosen cover. -/
def IsFraming (S : AugmentedGradedObject C) : Prop := IsIso S.augment ∧ S.LengthLe 1

/-- A free cover: the augmentation is an epimorphism. No condition on the cofiber. -/
abbrev IsFreeCover (S : AugmentedGradedObject C) : Prop := Epi S.augment

/-- An isomorphism of augmentations is an epimorphism: a framing is in particular a free cover,
while the converse fails (`intCover_isFreeCover`, `intCover_not_isFraming`). -/
theorem IsFraming.isFreeCover {S : AugmentedGradedObject C} (hS : S.IsFraming) : S.IsFreeCover :=
  letI : IsIso S.augment := hS.1
  MorphismProperty.epimorphisms.infer_property S.augment

/-- A framing retains no term above degree zero. -/
theorem IsFraming.lengthLe {S : AugmentedGradedObject C} (hS : S.IsFraming) : S.LengthLe 1 :=
  hS.2

section Abelian

variable [HasZeroObject C]

/-- Exactness at degree zero is injectivity of an augmentation whose differential out of `P_1`
is zero. -/
theorem exactAt_zero_iff_mono {S : AugmentedGradedObject C} (h : S.diff 0 = 0) :
    S.ExactAt 0 ↔ Mono S.augment := by
  exact ShortComplex.exact_iff_mono (S.shortComplex 0) h

end Abelian

/-- The `F`-acyclic refinement of a selected augmented object: applying `F` degreewise leaves
every degree exact. This is the `F`-acyclic condition used to compute derived functors, and it is
independent of `S.CofiberVanishes`. -/
def IsAcyclicFor {D : Type w} [Category.{v} D] [Preadditive D] (S : AugmentedGradedObject C)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] : Prop :=
  ∀ k : ℕ, ((S.shortComplex k).map F).Exact


/-- The refinement of selected augmented objects by a classifier `P`: a full subcategory that
retains the whole selected diagram. -/
abbrev Refinement (P : ObjectProperty (AugmentedGradedObject C)) := P.FullSubcategory

/-- Forgetting a refinement and then forgetting the selected diagram is forgetting the selected
diagram: the two forgetful conventions commute definitionally. -/
abbrev refinementPoint (P : ObjectProperty (AugmentedGradedObject C)) : Refinement P ⥤ C :=
  P.ι ⋙ pointFunctor

/-- The forgetful functor of a refinement is exactly `pointFunctor` composed with the inclusion of
the refinement: the refinements do not change the underlying augmentation point. -/
theorem refinementPoint_eq (P : ObjectProperty (AugmentedGradedObject C)) :
    refinementPoint P = P.ι ⋙ pointFunctor := rfl

/-- The `k`-truncation refinement: the selected augmented objects whose chosen terms vanish in every
degree `k` or above. Truncation is one of the independently imposed refinements. -/
def TruncationRefinement (k : ℕ) : ObjectProperty (AugmentedGradedObject C) :=
  fun S => S.LengthLe k

/-- Forgetting the truncation refinement commutes with the underlying augmentation. -/
theorem truncationRefinementPoint_eq (k : ℕ) :
    refinementPoint (C := C) (TruncationRefinement (C := C) k) =
      (TruncationRefinement (C := C) k).ι ⋙ pointFunctor (C := C) := rfl

/-- Truncation levels are nested: a longer truncation retains everything a shorter one does. -/
theorem truncationRefinement_mono {k k' : ℕ} (h : k ≤ k') :
    TruncationRefinement (C := C) k ≤ TruncationRefinement (C := C) k' :=
  fun _ hS n hn => hS n (le_trans h hn)

/-- A finer refinement forgets through the coarser one without changing the underlying
augmentation point. -/
theorem refinementPoint_ιOfLE (P Q : ObjectProperty (AugmentedGradedObject C)) (h : P ≤ Q) :
    ObjectProperty.ιOfLE h ⋙ refinementPoint (C := C) Q = refinementPoint (C := C) P := rfl

section Realization

variable {E : Type w} [Category.{v} E] [Preadditive E]

/-- The degreewise realization of a selected augmented object under a zero-morphism-preserving
functor `j : C ⤳ E`, i.e. the issue's `R^•` carried into `E` together with its chosen terms,
differentials and augmentation. -/
def realize (j : C ⥤ E) [j.PreservesZeroMorphisms] (S : AugmentedGradedObject C) :
    AugmentedGradedObject E where
  term n := j.obj (S.term n)
  diff n := j.map (S.diff n)
  comp_diff n := by rw [← j.map_comp, S.comp_diff n, j.map_zero]
  point := j.obj S.point
  augment := j.map S.augment
  comp_augment := by rw [← j.map_comp, S.comp_augment, j.map_zero]

/-- The realized augmentation as an object of the slice `E_{/j(X)}` — the correction recorded on the
issue, that `ε` is an object of the slice, equivalently an arrow of `E`. -/
def realization (j : C ⥤ E) (S : AugmentedGradedObject C) : Over (j.obj S.point) :=
  Over.mk (j.map S.augment)

section Exact

variable (j : C ⥤ E) [j.PreservesZeroMorphisms] [j.PreservesHomology]

/-- **A vanishing cofiber selects a full resolution after realization**: if every degree of the
selected object is exact, the realized complex is acyclic in `E`. This is the statement that
`cofib(ε) ≃ 0` is an equivalence in the enhancement rather than a condition on the augmentation,
and that an epimorphic augmentation does not supply it (`intCover_not_cofiberVanishes`). -/
theorem isAcyclicFor_of_cofiberVanishes {S : AugmentedGradedObject C} (hS : S.CofiberVanishes) :
    S.IsAcyclicFor j := by
  intro k
  exact (hS k).map j

end Exact

end Realization

section Casts

variable {C : Type u} [Category.{v} C]

/-- Casts along an equality and its reverse cancel. -/
lemma eqToHom_comp_eqToHom_cancel {X Y : C} (p : X = Y) (q : Y = X) :
    eqToHom p ≫ eqToHom q = 𝟙 X := by
  rw [eqToHom_trans, eqToHom_refl]

/-- Casts along an equality and its reverse cancel in a composite. -/
lemma eqToHom_comp_eqToHom_cancel_assoc {X Y Z : C} (p : X = Y) (q : Y = X) (f : X ⟶ Z) :
    eqToHom p ≫ eqToHom q ≫ f = f := by
  rw [← Category.assoc, eqToHom_comp_eqToHom_cancel, Category.id_comp]

end Casts

section Truncate

open ZeroObject

variable [HasZeroObject C]

/-- The chosen terms of the `k`-truncation of a selected augmented object: the terms in degrees
below `k`, and the zero object above. -/
noncomputable def truncTerm (S : AugmentedGradedObject C) (k : ℕ) : ℕ → C :=
  fun n => if n < k then S.term n else 0

/-- The chosen differentials of the `k`-truncation: the differentials of `S` in degrees below `k`,
and zero above. -/
noncomputable def truncDiff (S : AugmentedGradedObject C) (k n : ℕ) :
    truncTerm S k (n + 1) ⟶ truncTerm S k n :=
  if h : n + 1 < k then
    eqToHom (by simp [truncTerm, h]) ≫ S.diff n ≫
      eqToHom (by simp [truncTerm, show n < k by omega])
  else 0

/-- The augmentation of the `k`-truncation. -/
noncomputable def truncAugment (S : AugmentedGradedObject C) (k : ℕ) :
    truncTerm S k 0 ⟶ S.point :=
  if h : 0 < k then eqToHom (by simp [truncTerm, h]) ≫ S.augment else 0

/-- The `k`-truncation of a selected augmented object: the chosen terms and differentials in
degrees below `k`, the zero object above, and the augmentation, which survives exactly when
`0 < k`. This is truncation as an operation on selected diagrams, not only as the predicate
`TruncationRefinement`. -/
noncomputable def truncate (S : AugmentedGradedObject C) (k : ℕ) : AugmentedGradedObject C where
  term := truncTerm S k
  diff := truncDiff S k
  comp_diff n := by
    simp only [truncDiff]
    by_cases h2 : n + 2 < k
    · have h1 : n + 1 < k := by omega
      have h0 : n < k := by omega
      simp [h2, h1, eqToHom_comp_eqToHom_cancel_assoc]
      rw [← Category.assoc, S.comp_diff n, zero_comp]
    · by_cases h1 : n + 1 < k
      · simp [h2, h1]
      · by_cases h0 : n < k
        · simp [h2, h1, h0]
        · simp [h2, h1, h0]
  point := S.point
  augment := truncAugment S k
  comp_augment := by
    simp only [truncDiff, truncAugment]
    by_cases h1 : 1 < k
    · have h0 : 0 < k := by omega
      simp [h1, h0, eqToHom_comp_eqToHom_cancel_assoc, S.comp_augment]
    · by_cases h0 : 0 < k
      · simp [h1, h0]
      · simp [h1, h0]

/-- A truncation keeps every chosen term below `k`. -/
theorem truncate_term_of_lt (S : AugmentedGradedObject C) {k n : ℕ} (h : n < k) :
    (truncate S k).term n = S.term n := by
  simp [truncate, truncTerm, h]

/-- A truncation kills every chosen term in degree `k` and above. -/
theorem truncate_term_of_ge (S : AugmentedGradedObject C) {k n : ℕ} (h : k ≤ n) :
    (truncate S k).term n = 0 := by
  simp [truncate, truncTerm, show ¬ n < k by omega]

/-- A truncation has length at most `k`. -/
theorem truncate_lengthLe (S : AugmentedGradedObject C) (k : ℕ) : (truncate S k).LengthLe k :=
  fun n hn => by
    rw [truncate_term_of_ge S hn]
    exact isZero_zero C

/-- Truncating twice at the same degree changes nothing: it is idempotent on chosen terms. -/
theorem truncate_idem_term (S : AugmentedGradedObject C) (k : ℕ) :
    (truncate (truncate S k) k).term = (truncate S k).term := by
  funext n
  by_cases hn : n < k
  · rw [truncate_term_of_lt _ hn, truncate_term_of_lt S hn]
  · rw [truncate_term_of_ge _ (by omega), truncate_term_of_ge S (by omega)]

end Truncate

end AugmentedGradedObject

end General
/-- The zero module, the chosen term above the truncation of the examples below. -/
abbrev zeroModule (R : Type u) [CommRing R] : ModuleCat.{v} R := ModuleCat.of R (ULift.{v} PUnit)

/-- The zero module is a zero object. -/
theorem isZero_zeroModule (R : Type u) [CommRing R] : IsZero (zeroModule R) :=
  ModuleCat.isZero_of_subsingleton _

section ModuleCat

variable (R : Type u) [CommRing R]

namespace AugmentedGradedObject

/-- The degreewise freeness classifier for a selected augmented object of `R`-modules
(FOUNDATIONS Definition 76.2). -/
def TermwiseFree : ObjectProperty (AugmentedGradedObject (ModuleCat.{v} R)) :=
  Termwise fun M => Module.Free R M

/-- The degreewise projectivity classifier for a selected augmented object of `R`-modules. -/
def TermwiseProjective : ObjectProperty (AugmentedGradedObject (ModuleCat.{v} R)) :=
  Termwise fun M => Module.Projective R M

/-- The degreewise flatness classifier for a selected augmented object of `R`-modules. -/
def TermwiseFlat : ObjectProperty (AugmentedGradedObject (ModuleCat.{v} R)) :=
  Termwise fun M => Module.Flat R M

/-- The chosen terms of a one-term object: `P` in degree zero, zero above it. -/
def oneTermTerms (P : ModuleCat.{v} R) : ℕ → ModuleCat.{v} R
  | 0 => P
  | _ + 1 => zeroModule R

/-- The selected augmented object with one chosen term `P` in degree zero and zero terms above it,
all differentials zero: the augmentation `P --ε--> M` alone. -/
def oneTerm (P M : ModuleCat.{v} R) (ε : P ⟶ M) : AugmentedGradedObject (ModuleCat.{v} R) where
  term := oneTermTerms R P
  diff _ := 0
  comp_diff _ := by simp
  point := M
  augment := ε
  comp_augment := zero_comp

/-- The chosen terms of a two-term object: `P` in degree zero, `Q` in degree one, zero above. -/
def twoTermTerms (Q P : ModuleCat.{v} R) : ℕ → ModuleCat.{v} R
  | 0 => P
  | 1 => Q
  | _ + 2 => zeroModule R

/-- The selected augmented object `Q --d--> P --ε--> M` with zero terms above degree one. Neither
`d` nor `ε` is required to be injective, surjective or exact. -/
def twoTerm (Q P M : ModuleCat.{v} R) (d : Q ⟶ P) (ε : P ⟶ M) (h : d ≫ ε = 0) :
    AugmentedGradedObject (ModuleCat.{v} R) where
  term := twoTermTerms R Q P
  diff
    | 0 => d
    | _ + 1 => 0
  comp_diff
    | 0 => zero_comp
    | _ + 1 => zero_comp
  point := M
  augment := ε
  comp_augment := h

/-- The `1`-truncation of a two-term selected object, as an actual morphism of selected diagrams:
the augmentation and the chosen term in degree `0` are carried by the identity and everything above
degree `0` is sent to zero. This is what a truncation retains: the defining diagram maps, with the
dropped differential no longer visible. -/
def coverToTwoTerm (Q P M : ModuleCat.{v} R) (d : Q ⟶ P) (ε : P ⟶ M) (h : d ≫ ε = 0) :
    oneTerm R P M ε ⟶ twoTerm R Q P M d ε h where
  point := 𝟙 M
  term
    | 0 => 𝟙 P
    | _ + 1 => 0
  comm_diff n := by
    match n with
    | 0 => exact zero_comp.trans zero_comp.symm
    | _ + 1 => exact zero_comp.trans zero_comp.symm
  comm_augment := (Category.comp_id ε).trans (Category.id_comp ε).symm

/-- A one-term object is a framing exactly when its augmentation is an isomorphism
(FOUNDATIONS Definition 13.11: a free resolution of length zero is a chosen basis). -/
theorem oneTerm_isFraming_iff {P M : ModuleCat.{v} R} (ε : P ⟶ M) :
    (oneTerm R P M ε).IsFraming ↔ IsIso ε := by
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    refine ⟨h, ?_⟩
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    change IsZero (zeroModule R)
    exact isZero_zeroModule R

/-- A one-term object is a free cover exactly when its augmentation is an epimorphism. -/
theorem oneTerm_isFreeCover_iff {P M : ModuleCat.{v} R} (ε : P ⟶ M) :
    (oneTerm R P M ε).IsFreeCover ↔ Epi ε := Iff.rfl

end AugmentedGradedObject

end ModuleCat
section Sheaves

open TopologicalSpace

variable (R : Type u) [CommRing R] (X : TopCat)

/-- Global sections of a sheaf of `O_X`-modules, as a functor to `R`-modules: the operation that
FOUNDATIONS Remark 13.12 applies *after* the framing, and which is not the framing. -/
noncomputable def globalSections : X.Sheaf (ModuleCat.{v} R) ⥤ ModuleCat.{v} R :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{v} R) ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{v} R)).obj (Opposite.op ⊤)

/-- FOUNDATIONS Remark 13.12: a framing of a sheaf of `O_X`-modules is a chosen isomorphism of
sheaves of `O_X`-modules. `IsFraming` is a predicate on selected augmented objects of any
additive category, so read in `Sh(X, Mod O_X)` it is the framing condition at the level of
sheaves, not at the level of the modules of sections of an open set. -/
theorem sheafFraming_iff (S : AugmentedGradedObject (X.Sheaf (ModuleCat.{v} R))) :
    S.IsFraming ↔ IsIso S.augment ∧ S.LengthLe 1 := Iff.rfl

/-- Applying global sections to a framing of sheaves of modules gives an isomorphism of
`R`-modules: that isomorphism is a consequence of the sheaf-level datum. -/
theorem sheafFraming_sections {F T : X.Sheaf (ModuleCat.{v} R)} (φ : F ⟶ T) [IsIso φ] :
    IsIso ((globalSections R X).map φ) :=
  Functor.map_isIso _ φ

end Sheaves

section Specimens

namespace AugmentedGradedObject

open LeanCategories.Modules

/-- The ring homomorphism `ℤ ⟶ ℤ/2` as a linear map, the augmentation of the free cover below. -/
noncomputable def intToZModTwo : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ (ZMod 2)) :=
  ModuleCat.ofHom (Algebra.linearMap ℤ (ZMod 2))

/-- The augmentation `ℤ ⟶ ℤ/2` is evaluation of the integer cast. -/
theorem intToZModTwo_apply (x : ℤ) : intToZModTwo x = (x : ZMod 2) := rfl

/-- The augmentation `ℤ ⟶ ℤ/2` is surjective. -/
theorem intToZModTwo_surjective : Function.Surjective intToZModTwo := by
  intro a
  refine ⟨((show ZMod 2 from a).val : ℤ), ?_⟩
  rw [intToZModTwo_apply]
  push_cast
  exact ZMod.natCast_zmod_val (show ZMod 2 from a)

/-- The augmentation `ℤ ⟶ ℤ/2` is not injective: `2 ↦ 0`. -/
theorem intToZModTwo_not_injective : ¬ Function.Injective intToZModTwo := by
  intro hinj
  have h : intToZModTwo 2 = intToZModTwo 0 := by
    rw [intToZModTwo_apply, intToZModTwo_apply]
    decide
  have h2 := hinj h
  norm_num at h2

/-- The augmentation `ℤ ⟶ ℤ/2` is an epimorphism: a free cover. -/
theorem intToZModTwo_epi : Epi intToZModTwo :=
  (ModuleCat.epi_iff_surjective intToZModTwo).mpr intToZModTwo_surjective

/-- The augmentation `ℤ ⟶ ℤ/2` is not a monomorphism: it is not a framing. -/
theorem intToZModTwo_not_mono : ¬ Mono intToZModTwo := by
  rw [ModuleCat.mono_iff_injective]
  exact intToZModTwo_not_injective

/-- `2` is a nonzero element of the kernel of `ℤ ⟶ ℤ/2`: the kernel class `2ℤ` in degree `-1` of
the cofiber (FOUNDATIONS, governing construction). -/
theorem two_mem_ker_intToZModTwo : (2 : ℤ) ∈ LinearMap.ker (ModuleCat.Hom.hom intToZModTwo) := by
  rw [LinearMap.mem_ker, ModuleCat.Hom.hom, intToZModTwo_apply]
  decide

/-- The kernel of `ℤ ⟶ ℤ/2` is the range of multiplication by two, so the cofiber of the free
cover is not acyclic. -/
theorem range_twoMul_eq_ker_intToZModTwo :
    LinearMap.range (LinearMap.lsmul ℤ ℤ (2 : ℤ)) =
      LinearMap.ker (ModuleCat.Hom.hom intToZModTwo) := by
  ext y
  rw [LinearMap.mem_range, LinearMap.mem_ker, ModuleCat.Hom.hom, intToZModTwo_apply]
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.lsmul_apply, zsmul_eq_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨x, by ring⟩
  · intro hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨c, by rw [LinearMap.lsmul_apply]; ring⟩

/-- The identity `ℤ ≅ ℤ`: a length-zero framing with vanishing cofiber. -/
noncomputable def intFraming : AugmentedGradedObject (ModuleCat ℤ) :=
  oneTerm ℤ (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) (𝟙 _)

/-- The identity framing is a framing: a length-zero free resolution of `ℤ`. -/
theorem intFraming_isFraming : intFraming.IsFraming :=
  (oneTerm_isFraming_iff (R := ℤ) (P := ModuleCat.of ℤ ℤ) (M := ModuleCat.of ℤ ℤ) (𝟙 _)).mpr
    inferInstance

/-- An isomorphism of augmentations is an epimorphism, so the identity framing is a free cover. -/
theorem intFraming_isFreeCover : intFraming.IsFreeCover := intFraming_isFraming.isFreeCover

/-- The identity framing has vanishing cofiber: every degree of the augmented complex is exact. -/
theorem intFraming_cofiberVanishes : intFraming.CofiberVanishes := by
  intro k
  match k with
  | 0 =>
      have hg : Mono (intFraming.shortComplex 0).g := by
        change Mono (𝟙 (ModuleCat.of ℤ ℤ))
        infer_instance
      exact (ShortComplex.exact_iff_mono (intFraming.shortComplex 0) rfl).mpr hg
  | _ + 1 => exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zeroModule ℤ)

/-- The one-term free cover `ℤ ⟶ ℤ/2`: an epimorphic augmentation with no condition on the
cofiber. -/
noncomputable def intCover : AugmentedGradedObject (ModuleCat ℤ) :=
  oneTerm ℤ (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ (ZMod 2)) intToZModTwo

/-- The epimorphism `ℤ ↠ ℤ/2` is a free cover. -/
theorem intCover_isFreeCover : intCover.IsFreeCover :=
  (oneTerm_isFreeCover_iff (R := ℤ) intToZModTwo).mpr intToZModTwo_epi

/-- The free cover `ℤ ↠ ℤ/2` is not a framing: its augmentation is not an isomorphism. -/
theorem intCover_not_isFraming : ¬ intCover.IsFraming := by
  rintro ⟨h, -⟩
  exact intToZModTwo_not_injective
    ((ConcreteCategory.isIso_iff_bijective intCover.augment).mp h).1

/-- The cofiber of the free cover `ℤ ↠ ℤ/2` does not vanish: epimorphy does not imply
`cofib(ε) ≃ 0`. -/
theorem intCover_not_cofiberVanishes : ¬ intCover.CofiberVanishes := by
  intro h
  have hm : Mono intCover.augment := (exactAt_zero_iff_mono (S := intCover) rfl).mp (h 0)
  exact intToZModTwo_not_injective ((ModuleCat.mono_iff_injective intCover.augment).mp hm)

/-- Multiplication by two on `ℤ`, as an endomorphism of the standard free module. -/
noncomputable def twoMul : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ) :=
  ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ (2 : ℤ))

/-- Multiplication by two sends `x` to `2 * x`. -/
theorem twoMul_apply (x : ℤ) : twoMul x = 2 * x := by
  change (LinearMap.lsmul ℤ ℤ (2 : ℤ)) x = 2 * x
  rw [LinearMap.lsmul_apply, zsmul_eq_mul]
  norm_num

/-- Multiplication by two is not the zero map. -/
theorem twoMul_ne_zero : twoMul ≠ 0 := by
  intro h
  have h1 := congrArg (fun (g : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ)) => g 1) h
  rw [twoMul_apply] at h1
  simp at h1

/-- Multiplication by two is injective on `ℤ`. -/
theorem twoMul_injective : Function.Injective twoMul := by
  intro x y hxy
  rw [twoMul_apply, twoMul_apply] at hxy
  exact mul_left_cancel₀ (by norm_num) hxy

/-- Multiplication by two is a monomorphism of `ℤ`-modules. -/
theorem twoMul_mono : Mono twoMul := (ModuleCat.mono_iff_injective twoMul).mpr twoMul_injective

/-- The chosen differential `ℤ --2--> ℤ` is killed by the augmentation, so it is a differential of
an augmented object over `ℤ/2`. -/
theorem twoMul_comp_intToZModTwo : twoMul ≫ intToZModTwo = 0 := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x => ?_
  have hx : (twoMul ≫ intToZModTwo) x = intToZModTwo (twoMul x) := rfl
  have hz : (ModuleCat.Hom.hom (0 : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ (ZMod 2)))) x = 0 := rfl
  rw [hx, twoMul_apply, intToZModTwo_apply, hz, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨x, by ring⟩

/-- The free resolution `0 ⟶ ℤ --2--> ℤ --ε--> ℤ/2 ⟶ 0`. -/
noncomputable def intKoszul : AugmentedGradedObject (ModuleCat ℤ) :=
  twoTerm ℤ (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ (ZMod 2)) twoMul intToZModTwo
    twoMul_comp_intToZModTwo

/-- The two-term complex `0 ⟶ ℤ --2--> ℤ --ε--> ℤ/2` is exact in every degree. -/
theorem intKoszul_cofiberVanishes : intKoszul.CofiberVanishes := by
  intro k
  match k with
  | 0 =>
      refine (ShortComplex.moduleCat_exact_iff_range_eq_ker (intKoszul.shortComplex 0)).mpr ?_
      change LinearMap.range (LinearMap.lsmul ℤ ℤ (2 : ℤ)) =
        LinearMap.ker (ModuleCat.Hom.hom intToZModTwo)
      exact range_twoMul_eq_ker_intToZModTwo
  | 1 =>
      exact (ShortComplex.exact_iff_mono (intKoszul.shortComplex 1) rfl).mpr twoMul_mono
  | _ + 2 => exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zeroModule ℤ)

/-- The resolution `0 ⟶ ℤ --2--> ℤ --ε--> ℤ/2` has amplitude two. -/
theorem intKoszul_lengthLe_two : intKoszul.LengthLe 2 := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  change IsZero (zeroModule (R := ℤ))
  exact isZero_zeroModule ℤ

/-- Its amplitude is not one: the chosen term in degree one is not a zero object. -/
theorem intKoszul_not_lengthLe_one : ¬ intKoszul.LengthLe 1 := by
  intro h
  have hz : IsZero (ModuleCat.of ℤ ℤ) := h 1 le_rfl
  have hsub : Subsingleton ℤ := ModuleCat.isZero_iff_subsingleton.mp hz
  exact absurd (hsub.allEq (0 : ℤ) 1) (by norm_num)

/-- Every chosen term of the resolution is free. -/
theorem intKoszul_termwiseFree : intKoszul.TermwiseFree := by
  intro k
  match k with
  | 0 => exact Module.Free.self ℤ
  | 1 => exact Module.Free.self ℤ
  | _ + 2 =>
      change Module.Free ℤ (zeroModule (R := ℤ))
      exact Module.Free.of_subsingleton ℤ _

/-- The truncated selected object `ℤ --0--> ℤ --ε--> ℤ/2`: termwise free with chosen
differentials, and its terminal augmentation is not exact. -/
noncomputable def intTruncated : AugmentedGradedObject (ModuleCat ℤ) :=
  twoTerm ℤ (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ (ZMod 2)) 0 intToZModTwo
    zero_comp

/-- The truncated object is still termwise free: termwise conditions are independent of
exactness. -/
theorem intTruncated_termwiseFree : intTruncated.TermwiseFree := by
  intro k
  match k with
  | 0 => exact Module.Free.self ℤ
  | 1 => exact Module.Free.self ℤ
  | _ + 2 =>
      change Module.Free ℤ (zeroModule (R := ℤ))
      exact Module.Free.of_subsingleton ℤ _

/-- The truncated object remains a free cover. -/
theorem intTruncated_isFreeCover : intTruncated.IsFreeCover := intToZModTwo_epi

/-- A truncation presumes no exactness at its last retained term: the one-truncation of this
selected object is not exact. -/
theorem intTruncated_not_truncatedExact : ¬ intTruncated.TruncatedExact 1 := by
  intro h
  exact intToZModTwo_not_mono ((exactAt_zero_iff_mono (S := intTruncated) rfl).mp (h 0 (by omega)))

/-- The map of chosen terms of a morphism is not a function of its map of augmentation points: two
morphisms of the free cover differ while inducing the same map of the underlying module. -/
theorem exists_hom_same_point_ne : ∃ f g : intCover ⟶ intCover,
    Hom.point f = Hom.point g ∧ f ≠ g := by
  let F : intCover ⟶ intCover := ⟨0, fun _ => 0, fun _ => by simp, by simp⟩
  let G : intCover ⟶ intCover :=
    ⟨0, fun n => match n with
      | 0 => twoMul
      | _ + 1 => 0,
      fun n => by
        match n with
        | 0 =>
            change (0 : zeroModule ℤ ⟶ zeroModule ℤ) ≫ (0 : zeroModule ℤ ⟶ ModuleCat.of ℤ ℤ) =
              (0 : zeroModule ℤ ⟶ ModuleCat.of ℤ ℤ) ≫ twoMul
            simp
        | _ + 1 =>
            change (0 : zeroModule ℤ ⟶ zeroModule ℤ) ≫ (0 : zeroModule ℤ ⟶ zeroModule ℤ) =
              (0 : zeroModule ℤ ⟶ zeroModule ℤ) ≫ (0 : zeroModule ℤ ⟶ zeroModule ℤ)
            simp,
      by
        simp only [comp_zero]
        exact twoMul_comp_intToZModTwo.symm⟩
  refine ⟨F, G, rfl, ?_⟩
  intro hFG
  have h : (0 : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ)) = twoMul :=
    congrArg (fun (f : intCover ⟶ intCover) => Hom.term f 0) hFG
  exact twoMul_ne_zero h.symm

/-- The resolution is `F`-acyclic for the forgetful functor to abelian groups: vanishing cofiber
implies `F`-acyclicity for this `F`, and `F`-acyclicity is a separate classifier. -/
theorem intKoszul_isAcyclicFor_forget :
    intKoszul.IsAcyclicFor (forget₂ (ModuleCat ℤ) AddCommGrpCat) :=
  fun k => (intKoszul_cofiberVanishes k).map _

end AugmentedGradedObject

end Specimens

end LeanCategories.Modules
