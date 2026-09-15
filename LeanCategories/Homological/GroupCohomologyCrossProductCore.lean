/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.ComplexShapeSigns
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Cohomological cross products for groups

Weibel, *An Introduction to Homological Algebra* (1994), Construction 6.1.14,
pp. 160--166 (FC05-C06-U016).

Keeping the notation of Proposition 6.1.13, let `P → ℤ` and `Q → ℤ` be
projective resolutions for `G` and `H` such that the direct-sum total complex
`P ⊗ℤ Q` is the chosen projective resolution for `G × H`.  Construction
6.1.14 first defines a morphism of total cochain complexes

`μ : Hom_G(P,ℤ) ⊗ Hom_H(Q,ℤ) → Hom_{G×H}(P ⊗ Q,ℤ)`

whose `(p,q)`-component is characterized by
`μ(f ⊗ f')(x ⊗ y) = f(x) * f'(y)`.  The cohomological cross product is the
map induced by `μ` on the cohomology of these chosen resolution models.
Mathlib's `groupCohomologyIso` separately identifies each such cohomology
object with its resolution-independent `groupCohomology` object; that model
comparison is not an additional clause of Construction 6.1.14.

In particular, an arbitrary family of graded maps is *not* a realization of
the source construction.  The structures below retain the tensor-total
resolution, the actual cochain map, its defining pure-tensor formula, and the
fact that the cohomology map is induced from that cochain map.  Independence
of the resolutions, unitality, and associativity are the subsequent exercise
layer and are not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

variable (G : Type) [Group G]
variable (H : Type) [Group H]

/-- The external tensor product of a `G`-representation and an
`H`-representation, regarded as a `(G × H)`-representation. -/
noncomputable abbrev groupExternalTensorRep
    (A : Rep ℤ G) (B : Rep ℤ H) : Rep ℤ (G × H) :=
  Rep.res (MonoidHom.fst G H) A ⊗ Rep.res (MonoidHom.snd G H) B

/-- The external tensor product as a bifunctor.  This is the functor whose
totalization gives the `P ⊗ℤ Q` appearing in Weibel 6.1.14.  It is obtained by
restricting along the two projections and then applying the existing tensor
bifunctor; no tensor functoriality is reimplemented here. -/
noncomputable abbrev groupExternalTensorBifunctor :
    Rep ℤ G ⥤ Rep ℤ H ⥤ Rep ℤ (G × H) :=
  (((Functor.whiskeringLeft₂ (Rep ℤ (G × H))).obj
      (Rep.resFunctor (MonoidHom.fst G H))).obj
    (Rep.resFunctor (MonoidHom.snd G H))).obj
      (curriedTensor (Rep ℤ (G × H)))

instance groupExternalTensorBifunctor_preservesZeroMorphisms :
    (groupExternalTensorBifunctor G H).PreservesZeroMorphisms where
  map_zero A A' := by
    ext B : 2
    change ((Rep.resFunctor (MonoidHom.fst G H)).map (0 : A ⟶ A')) ⊗ₘ
      𝟙 (Rep.res (MonoidHom.snd G H) B) = 0
    rw [Functor.map_zero]
    simp

instance groupExternalTensorBifunctor_obj_preservesZeroMorphisms (A : Rep ℤ G) :
    ((groupExternalTensorBifunctor G H).obj A).PreservesZeroMorphisms where
  map_zero B B' := by
    change 𝟙 (Rep.res (MonoidHom.fst G H) A) ⊗ₘ
      (Rep.resFunctor (MonoidHom.snd G H)).map (0 : B ⟶ B') = 0
    rw [Functor.map_zero]
    simp

/-- The direct-sum total complex `Tot^⊕(P ⊗ℤ Q)` of two chain complexes of
group representations. -/
noncomputable abbrev groupExternalTensorComplex
    (P : ChainComplex (Rep ℤ G) ℕ) (Q : ChainComplex (Rep ℤ H) ℕ) :
    ChainComplex (Rep ℤ (G × H)) ℕ :=
  HomologicalComplex.mapBifunctor P Q (groupExternalTensorBifunctor G H)
    (ComplexShape.down ℕ)

/-- The preceding proposition supplies precisely this datum for the free
resolutions used by Weibel: `Tot^⊕(P ⊗ℤ Q)` is itself a projective resolution
of the trivial `(G × H)`-module.  U016 consumes this fact; it does not replace
the tensor total by an unrelated resolution. -/
structure GroupExternalTensorResolution
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ)) where
  /-- Every term of the tensor total is projective. -/
  projective : ∀ n, Projective ((groupExternalTensorComplex G H P.complex Q.complex).X n)
  /-- The tensor total has homology objects in every degree. -/
  [hasHomology : ∀ n, (groupExternalTensorComplex G H P.complex Q.complex).HasHomology n]
  /-- Augmentation of the tensor total to the trivial product-group module. -/
  π : groupExternalTensorComplex G H P.complex Q.complex ⟶
    (ChainComplex.single₀ (Rep ℤ (G × H))).obj (Rep.trivial ℤ (G × H) ℤ)
  /-- The augmentation is a quasi-isomorphism. -/
  [quasiIso : QuasiIso π]

/-- Regard the tensor-total resolution datum as an ordinary projective
resolution. -/
noncomputable def GroupExternalTensorResolution.toProjectiveResolution
    {P : ProjectiveResolution (Rep.trivial ℤ G ℤ)}
    {Q : ProjectiveResolution (Rep.trivial ℤ H ℤ)}
    (T : GroupExternalTensorResolution G H P Q) :
    ProjectiveResolution (Rep.trivial ℤ (G × H) ℤ) where
  complex := groupExternalTensorComplex G H P.complex Q.complex
  projective := T.projective
  hasHomology := T.hasHomology
  π := T.π
  quasiIso := T.quasiIso

/-- Cochains obtained from a chosen projective resolution of the trivial
integral `K`-module.  Naming this construction keeps the cross-product
interface from repeatedly unfolding linear Yoneda and the resolution complex. -/
noncomputable abbrev groupResolutionCochains (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  P.complex.linearYonedaObj ℤ (Rep.trivial ℤ K ℤ)

/-- Inclusion of the `(p,q)` summand in the degree-`n` term of the external
tensor total, for a proof that `p+q=n`. -/
noncomputable def groupExternalTensorInclusion
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q n : ℕ) (h : p + q = n) :
    groupExternalTensorRep G H (P.complex.X p) (Q.complex.X q) ⟶
      (groupExternalTensorComplex G H P.complex Q.complex).X n :=
  HomologicalComplex.ιMapBifunctor P.complex Q.complex
    (groupExternalTensorBifunctor G H) (ComplexShape.down ℕ) p q n h

/-- Multiplication on the two restricted trivial representations.  Under the
underlying tensor-product model this is `a ⊗ b ↦ a * b`. -/
noncomputable def groupExternalTensorTrivialMul :
    groupExternalTensorRep G H (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ H ℤ) ⟶
      Rep.trivial ℤ (G × H) ℤ :=
  (λ_ (𝟙_ (Rep ℤ (G × H)))).hom

lemma groupExternalTensorPair_comp_left
    {A' A : Rep ℤ G} {B : Rep ℤ H}
    (d : A' ⟶ A) (f : A ⟶ Rep.trivial ℤ G ℤ)
    (g : B ⟶ Rep.trivial ℤ H ℤ) :
    ((Rep.resFunctor (MonoidHom.fst G H)).map d ▷
        Rep.res (MonoidHom.snd G H) B) ≫
        (((Rep.resFunctor (MonoidHom.fst G H)).map f ⊗ₘ
            (Rep.resFunctor (MonoidHom.snd G H)).map g) ≫
          groupExternalTensorTrivialMul G H) =
      (((Rep.resFunctor (MonoidHom.fst G H)).map (d ≫ f) ⊗ₘ
          (Rep.resFunctor (MonoidHom.snd G H)).map g) ≫
        groupExternalTensorTrivialMul G H) := by
  rw [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom]
  have hcomp :
      (Rep.resFunctor (MonoidHom.fst G H)).map d ≫
          (Rep.resFunctor (MonoidHom.fst G H)).map f =
        (Rep.resFunctor (MonoidHom.fst G H)).map (d ≫ f) :=
    (Functor.map_comp (Rep.resFunctor (MonoidHom.fst G H)) d f).symm
  rw [hcomp]
  simp only [Category.id_comp]

lemma groupExternalTensorPair_comp_right
    {A : Rep ℤ G} {B' B : Rep ℤ H}
    (f : A ⟶ Rep.trivial ℤ G ℤ) (d : B' ⟶ B)
    (g : B ⟶ Rep.trivial ℤ H ℤ) :
    (Rep.res (MonoidHom.fst G H) A ◁
        (Rep.resFunctor (MonoidHom.snd G H)).map d) ≫
        (((Rep.resFunctor (MonoidHom.fst G H)).map f ⊗ₘ
            (Rep.resFunctor (MonoidHom.snd G H)).map g) ≫
          groupExternalTensorTrivialMul G H) =
      (((Rep.resFunctor (MonoidHom.fst G H)).map f ⊗ₘ
          (Rep.resFunctor (MonoidHom.snd G H)).map (d ≫ g)) ≫
        groupExternalTensorTrivialMul G H) := by
  rw [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom]
  have hcomp :
      (Rep.resFunctor (MonoidHom.snd G H)).map d ≫
          (Rep.resFunctor (MonoidHom.snd G H)).map g =
        (Rep.resFunctor (MonoidHom.snd G H)).map (d ≫ g) :=
    (Functor.map_comp (Rep.resFunctor (MonoidHom.snd G H)) d g).symm
  rw [hcomp]
  simp only [Category.id_comp]

/-- Weibel's pure `(p,q)` cochain pairing on representation morphisms, viewed
in an arbitrary total degree `n`.  It is zero unless the `(p,q)` summand occurs
in degree `n`; on that summand it is the tensor product of the two cochains
followed by multiplication of the two copies of `ℤ`. -/
noncomputable def groupCochainPurePairingHomAt
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q n : ℕ)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    (groupExternalTensorComplex G H P.complex Q.complex).X n ⟶
      Rep.trivial ℤ (G × H) ℤ :=
  HomologicalComplex.mapBifunctorDesc
    (fun i j h ↦
      if hi : i = p then
        if hj : j = q then
          eqToHom (by subst hi; subst hj; rfl) ≫
            (((Rep.resFunctor (MonoidHom.fst G H)).map f ⊗ₘ
                (Rep.resFunctor (MonoidHom.snd G H)).map g) ≫
              groupExternalTensorTrivialMul G H)
        else 0
      else 0)

/-- Weibel's pure `(p,q)` cochain pairing in its natural total degree. -/
noncomputable abbrev groupCochainPurePairingHom
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    (groupExternalTensorComplex G H P.complex Q.complex).X (p + q) ⟶
      Rep.trivial ℤ (G × H) ℤ :=
  groupCochainPurePairingHomAt G H P Q p q (p + q) f g

@[reassoc]
lemma groupExternalTensorInclusion_comp_groupCochainPurePairingHomAt
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q n : ℕ) (h : p + q = n)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    groupExternalTensorInclusion G H P Q p q n h ≫
        groupCochainPurePairingHomAt G H P Q p q n f g =
      (((Rep.resFunctor (MonoidHom.fst G H)).map f ⊗ₘ
          (Rep.resFunctor (MonoidHom.snd G H)).map g) ≫
        groupExternalTensorTrivialMul G H) := by
  subst n
  unfold groupExternalTensorInclusion groupCochainPurePairingHomAt
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp [groupExternalTensorBifunctor]

@[reassoc]
lemma groupExternalTensorInclusion_comp_groupCochainPurePairingHomAt_of_ne_left
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (i j p q n : ℕ) (h : i + j = n) (hi : i ≠ p)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    groupExternalTensorInclusion G H P Q i j n h ≫
        groupCochainPurePairingHomAt G H P Q p q n f g = 0 := by
  unfold groupExternalTensorInclusion groupCochainPurePairingHomAt
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp [hi]

@[reassoc]
lemma groupExternalTensorInclusion_comp_groupCochainPurePairingHomAt_of_ne_right
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (i j p q n : ℕ) (h : i + j = n) (hj : j ≠ q)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    groupExternalTensorInclusion G H P Q i j n h ≫
        groupCochainPurePairingHomAt G H P Q p q n f g = 0 := by
  unfold groupExternalTensorInclusion groupCochainPurePairingHomAt
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp [hj]

lemma groupCochainPurePairingHom_add_left
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (f₁ f₂ : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    groupCochainPurePairingHom G H P Q p q (f₁ + f₂) g =
      groupCochainPurePairingHom G H P Q p q f₁ g +
        groupCochainPurePairingHom G H P Q p q f₂ g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [Preadditive.comp_add]
  simp only [groupCochainPurePairingHom, groupCochainPurePairingHomAt,
    HomologicalComplex.ι_mapBifunctorDesc]
  split_ifs with hi hj
  · subst i
    subst j
    have hmap :
        Rep.resMap (MonoidHom.fst G H) (f₁ + f₂) =
          Rep.resMap (MonoidHom.fst G H) f₁ + Rep.resMap (MonoidHom.fst G H) f₂ :=
      (Rep.resFunctor (MonoidHom.fst G H)).map_add
    rw [hmap, MonoidalPreadditive.add_tensor, Preadditive.add_comp,
      Preadditive.comp_add]
  all_goals simp

lemma groupCochainPurePairingHom_add_right
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g₁ g₂ : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    groupCochainPurePairingHom G H P Q p q f (g₁ + g₂) =
      groupCochainPurePairingHom G H P Q p q f g₁ +
        groupCochainPurePairingHom G H P Q p q f g₂ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [Preadditive.comp_add]
  simp only [groupCochainPurePairingHom, groupCochainPurePairingHomAt,
    HomologicalComplex.ι_mapBifunctorDesc]
  split_ifs with hi hj
  · subst i
    subst j
    have hmap :
        Rep.resMap (MonoidHom.snd G H) (g₁ + g₂) =
          Rep.resMap (MonoidHom.snd G H) g₁ + Rep.resMap (MonoidHom.snd G H) g₂ :=
      (Rep.resFunctor (MonoidHom.snd G H)).map_add
    rw [hmap, MonoidalPreadditive.tensor_add, Preadditive.add_comp,
      Preadditive.comp_add]
  all_goals simp

lemma groupCochainPurePairingHom_zero_left
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    groupCochainPurePairingHom G H P Q p q 0 g = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [groupCochainPurePairingHom, groupCochainPurePairingHomAt,
    HomologicalComplex.ι_mapBifunctorDesc]
  split_ifs with hi hj
  · have hmap :
        Rep.resMap (MonoidHom.fst G H)
            (0 : P.complex.X p ⟶ Rep.trivial ℤ G ℤ) = 0 :=
      (Rep.resFunctor (MonoidHom.fst G H)).map_zero _ _
    rw [hmap, MonoidalPreadditive.zero_tensor]
    simp only [comp_zero, zero_comp]
  all_goals simp

lemma groupCochainPurePairingHom_zero_right
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ) :
    groupCochainPurePairingHom G H P Q p q f 0 = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [groupCochainPurePairingHom, groupCochainPurePairingHomAt,
    HomologicalComplex.ι_mapBifunctorDesc]
  split_ifs with hi hj
  · have hmap :
        Rep.resMap (MonoidHom.snd G H)
            (0 : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) = 0 :=
      (Rep.resFunctor (MonoidHom.snd G H)).map_zero _ _
    rw [hmap, MonoidalPreadditive.tensor_zero]
    simp only [comp_zero, zero_comp]
  all_goals simp

/-- For a fixed left cochain, Weibel's pairing is additive in the right
cochain. -/
noncomputable def groupCochainPairingHomRightAdd
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ) :
    (Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) →+
      ((groupExternalTensorComplex G H P.complex Q.complex).X (p + q) ⟶
        Rep.trivial ℤ (G × H) ℤ) where
  toFun := groupCochainPurePairingHom G H P Q p q f
  map_zero' := groupCochainPurePairingHom_zero_right G H P Q p q f
  map_add' := groupCochainPurePairingHom_add_right G H P Q p q f

/-- The same map, using the canonical fact that additive maps of abelian
groups are `ℤ`-linear. -/
noncomputable def groupCochainPairingHomRightLinear
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ) :
    (Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) →ₗ[ℤ]
      ((groupExternalTensorComplex G H P.complex Q.complex).X (p + q) ⟶
        Rep.trivial ℤ (G × H) ℤ) :=
  (groupCochainPairingHomRightAdd G H P Q p q f).toIntLinearMap

/-- The pairing is additive in the left cochain, valued in right-linear
maps. -/
noncomputable def groupCochainPairingHomLeftAdd
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    (P.complex.X p ⟶ Rep.trivial ℤ G ℤ) →+
      ((Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) →ₗ[ℤ]
        ((groupExternalTensorComplex G H P.complex Q.complex).X (p + q) ⟶
          Rep.trivial ℤ (G × H) ℤ)) where
  toFun := groupCochainPairingHomRightLinear G H P Q p q
  map_zero' := by
    apply LinearMap.ext
    intro g
    change groupCochainPurePairingHom G H P Q p q 0 g = 0
    exact groupCochainPurePairingHom_zero_left G H P Q p q g
  map_add' := by
    intro f₁ f₂
    apply LinearMap.ext
    intro g
    change groupCochainPurePairingHom G H P Q p q (f₁ + f₂) g =
      groupCochainPurePairingHom G H P Q p q f₁ g +
        groupCochainPurePairingHom G H P Q p q f₂ g
    exact groupCochainPurePairingHom_add_left G H P Q p q f₁ f₂ g

/-- The bilinear form underlying Weibel's cochain pairing. -/
noncomputable def groupCochainPairingHomBilinear
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    (P.complex.X p ⟶ Rep.trivial ℤ G ℤ) →ₗ[ℤ]
      (Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) →ₗ[ℤ]
        ((groupExternalTensorComplex G H P.complex Q.complex).X (p + q) ⟶
          Rep.trivial ℤ (G × H) ℤ) :=
  (groupCochainPairingHomLeftAdd G H P Q p q).toIntLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`n` linear-Yoneda object is definitionally the module of
representation morphisms out of the degree-`n` resolution term.  This named
isomorphism keeps later constructions independent of transparency choices. -/
noncomputable def groupResolutionCochainIso
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :
    (groupResolutionCochains K P).X n ≅
      ModuleCat.of ℤ (P.complex.X n ⟶ Rep.trivial ℤ K ℤ) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- The analogous named isomorphism for the tensor-total resolution. -/
noncomputable def groupTensorResolutionCochainIso
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ)) (n : ℕ) :
    ((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
      (Rep.trivial ℤ (G × H) ℤ)).X n ≅
      ModuleCat.of ℤ
        ((groupExternalTensorComplex G H P.complex Q.complex).X n ⟶
          Rep.trivial ℤ (G × H) ℤ) :=
  Iso.refl _

/-- The `(p,q)` component of Weibel's natural cochain pairing
`Hom_G(P,ℤ) ⊗ Hom_H(Q,ℤ) → Hom_{G×H}(P⊗Q,ℤ)`. -/
noncomputable def groupCochainPairing
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    (groupResolutionCochains G P).X p ⊗ (groupResolutionCochains H Q).X q ⟶
      ((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
        (Rep.trivial ℤ (G × H) ℤ)).X (p + q) :=
  ((groupResolutionCochainIso G P p).hom ⊗ₘ
      (groupResolutionCochainIso H Q q).hom) ≫
    ModuleCat.ofHom (TensorProduct.lift (groupCochainPairingHomBilinear G H P Q p q)) ≫
    (groupTensorResolutionCochainIso G H P Q (p + q)).inv

/-- The `(p,q)` cochain pairing, regarded as landing in an ambient total
degree `n` identified with `p+q`. -/
noncomputable def groupCochainPairingAt
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q n : ℕ) (h : p + q = n) :
    (groupResolutionCochains G P).X p ⊗ (groupResolutionCochains H Q).X q ⟶
      ((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
        (Rep.trivial ℤ (G × H) ℤ)).X n :=
  groupCochainPairing G H P Q p q ≫
    eqToHom (congrArg
      (((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
        (Rep.trivial ℤ (G × H) ℤ)).X) h)

@[simp]
lemma groupCochainPairingAt_self
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) (h : p + q = p + q) :
    groupCochainPairingAt G H P Q p q (p + q) h =
      groupCochainPairing G H P Q p q := by
  have : h = rfl := Subsingleton.elim _ _
  cases this
  simp [groupCochainPairingAt]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma groupResolutionCochains_d_apply
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ))
    (n : ℕ) (f : (groupResolutionCochains K P).X n) :
    (groupResolutionCochains K P).d n (n + 1) f =
      P.complex.d (n + 1) n ≫ f := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma groupTensorResolutionCochains_d_apply
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (n : ℕ)
    (f : ((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
      (Rep.trivial ℤ (G × H) ℤ)).X n) :
    ((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
      (Rep.trivial ℤ (G × H) ℤ)).d n (n + 1) f =
        (groupExternalTensorComplex G H P.complex Q.complex).d (n + 1) n ≫ f := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma groupCochainPairingAt_tmul
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q n : ℕ) (h : p + q = n)
    (f : (groupResolutionCochains G P).X p)
    (g : (groupResolutionCochains H Q).X q) :
    groupCochainPairingAt G H P Q p q n h (f ⊗ₜ[ℤ] g) =
      groupCochainPurePairingHomAt G H P Q p q n f g := by
  subst n
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma groupCochainPairing_tmul
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (f : (groupResolutionCochains G P).X p)
    (g : (groupResolutionCochains H Q).X q) :
    groupCochainPairing G H P Q p q (f ⊗ₜ[ℤ] g) =
      groupCochainPurePairingHom G H P Q p q f g := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma groupTensorResolutionCochainIso_hom_pairing_tmul
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (f : (groupResolutionCochains G P).X p)
    (g : (groupResolutionCochains H Q).X q) :
    (groupTensorResolutionCochainIso G H P Q (p + q)).hom
        (groupCochainPairing G H P Q p q (f ⊗ₜ[ℤ] g)) =
      groupCochainPurePairingHom G H P Q p q
        ((groupResolutionCochainIso G P p).hom f)
        ((groupResolutionCochainIso H Q q).hom g) := by
  rfl

/-- The chain-level Leibniz identity underlying Weibel's cochain map. -/
lemma groupCochainPurePairingHom_d
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ)
    (f : P.complex.X p ⟶ Rep.trivial ℤ G ℤ)
    (g : Q.complex.X q ⟶ Rep.trivial ℤ H ℤ) :
    (groupExternalTensorComplex G H P.complex Q.complex).d (p + q + 1) (p + q) ≫
        groupCochainPurePairingHom G H P Q p q f g =
      groupCochainPurePairingHomAt G H P Q (p + 1) q (p + q + 1)
          (P.complex.d (p + 1) p ≫ f) g +
        ((-1 : ℤ) ^ p) •
          groupCochainPurePairingHomAt G H P Q p (q + 1) (p + q + 1)
            f (Q.complex.d (q + 1) q ≫ g) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change i + j = p + q + 1 at h
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc, Preadditive.add_comp,
    Linear.comp_smul, Units.smul_def, groupCochainPurePairingHomAt,
    HomologicalComplex.ι_mapBifunctorDesc, one_smul, zero_smul, zero_add,
    add_zero, zero_comp, comp_zero]
  rcases i with _ | i
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero P.complex Q.complex
      (groupExternalTensorBifunctor G H) (ComplexShape.down ℕ) 0 j (p + q) (by simp)]
    simp only [zero_comp, zero_add]
    rcases j with _ | j
    · omega
    · rw [HomologicalComplex.mapBifunctor.d₂_eq P.complex Q.complex
        (groupExternalTensorBifunctor G H) (ComplexShape.down ℕ) 0
        (show (ComplexShape.down ℕ).Rel (j + 1) j by simp) (p + q) (by
          change 0 + j = p + q
          omega)]
      dsimp [ComplexShape.ε₂]
      rw [pow_zero, one_smul, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      by_cases hp : p = 0
      · subst p
        have hj : j = q := by omega
        subst j
        simpa [groupExternalTensorBifunctor] using
          (groupExternalTensorPair_comp_right G H f (Q.complex.d (q + 1) q) g)
      · have hp0 : 0 ≠ p := Ne.symm hp
        simp [hp, hp0, groupCochainPurePairingHomAt]
  · rw [HomologicalComplex.mapBifunctor.d₁_eq P.complex Q.complex
      (groupExternalTensorBifunctor G H) (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (i + 1) i by simp) j (p + q) (by
        change i + j = p + q
        omega)]
    dsimp [ComplexShape.ε₁]
    rw [one_smul, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    rcases j with _ | j
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero P.complex Q.complex
        (groupExternalTensorBifunctor G H) (ComplexShape.down ℕ) (i + 1) 0 (p + q)
        (by simp)]
      by_cases hq : q = 0
      · subst q
        have hi : i = p := by omega
        subst i
        simpa [groupExternalTensorBifunctor] using
          (groupExternalTensorPair_comp_left G H (P.complex.d (p + 1) p) f g)
      · have hq0 : 0 ≠ q := Ne.symm hq
        simp [hq, hq0, groupCochainPurePairingHomAt]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq P.complex Q.complex
        (groupExternalTensorBifunctor G H) (ComplexShape.down ℕ) (i + 1)
        (show (ComplexShape.down ℕ).Rel (j + 1) j by simp) (p + q) (by
          change (i + 1) + j = p + q
          omega)]
      have hε :
          ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (ComplexShape.down ℕ) (i + 1, j + 1) =
            (-1 : ℤˣ) ^ (i + 1) := rfl
      rw [hε, Linear.units_smul_comp, Category.assoc,
        HomologicalComplex.ι_mapBifunctorDesc]
      by_cases hip : i = p
      · subst i
        have hq : q = j + 1 := by omega
        subst q
        simpa [groupExternalTensorBifunctor] using
          (groupExternalTensorPair_comp_left G H (P.complex.d (p + 1) p) f g)
      · by_cases hi1p : i + 1 = p
        · subst p
          have hq : q = j := by omega
          subst q
          have hr := groupExternalTensorPair_comp_right G H f
            (Q.complex.d (j + 1) j) g
          simp only [dif_neg hip, dif_neg (by omega : j + 1 ≠ j),
            dif_neg (by omega : i + 1 ≠ i + 1 + 1), dif_pos rfl,
            dif_pos trivial, eqToHom_refl, Category.id_comp, zero_comp, comp_zero, zero_add]
          change
            ((-1 : ℤ) ^ (i + 1)) •
                ((Rep.res (MonoidHom.fst G H) (P.complex.X (i + 1)) ◁
                    (Rep.resFunctor (MonoidHom.snd G H)).map (Q.complex.d (j + 1) j)) ≫
                  (((Rep.resFunctor (MonoidHom.fst G H)).map f ⊗ₘ
                      (Rep.resFunctor (MonoidHom.snd G H)).map g) ≫
                    groupExternalTensorTrivialMul G H)) =
              ((-1 : ℤ) ^ (i + 1)) •
                (((Rep.resFunctor (MonoidHom.fst G H)).map f ⊗ₘ
                    (Rep.resFunctor (MonoidHom.snd G H)).map (Q.complex.d (j + 1) j ≫ g)) ≫
                  groupExternalTensorTrivialMul G H)
          exact congrArg (fun k => ((-1 : ℤ) ^ (i + 1)) • k) hr
        · have hi1p1 : i + 1 ≠ p + 1 := by omega
          simp [hip, hi1p, hi1p1, groupCochainPurePairingHomAt,
            groupExternalTensorBifunctor]

set_option backward.isDefEq.respectTransparency false in
/-- The pure-tensor Leibniz formula above is the differential identity for
Weibel's bilinear cochain pairing. -/
lemma groupCochainPairing_d
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    groupCochainPairing G H P Q p q ≫
        ((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
          (Rep.trivial ℤ (G × H) ℤ)).d (p + q) (p + q + 1) =
      ((groupResolutionCochains G P).d p (p + 1) ⊗ₘ
          𝟙 ((groupResolutionCochains H Q).X q)) ≫
          groupCochainPairingAt G H P Q (p + 1) q (p + q + 1) (by omega) +
        ((-1 : ℤ) ^ p) •
          ((𝟙 ((groupResolutionCochains G P).X p) ⊗ₘ
              (groupResolutionCochains H Q).d q (q + 1)) ≫
            groupCochainPairingAt G H P Q p (q + 1) (p + q + 1) (by omega)) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp [smul_zero]
  | tmul f g =>
      convert groupCochainPurePairingHom_d G H P Q p q f g using 1 <;> try rfl
      dsimp [Linear.leftComp]
      change
        groupCochainPairingAt G H P Q (p + 1) q (p + q + 1) (by omega)
              ((P.complex.d (p + 1) p ≫ f) ⊗ₜ[ℤ] g) +
            ((-1 : ℤ) ^ p) •
              groupCochainPairingAt G H P Q p (q + 1) (p + q + 1) (by omega)
                (f ⊗ₜ[ℤ] (Q.complex.d (q + 1) q ≫ g)) = _
      rw [groupCochainPairingAt_tmul, groupCochainPairingAt_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor-total complex of the two resolution cochain complexes. -/
noncomputable abbrev groupCochainTensorComplex
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ)) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  HomologicalComplex.mapBifunctor (groupResolutionCochains G P)
    (groupResolutionCochains H Q) (curriedTensor (ModuleCat ℤ))
    (ComplexShape.up ℕ)

/-- Inclusion of a `(p,q)` summand in the cochain tensor total. -/
noncomputable abbrev groupCochainTensorInclusion
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q n : ℕ) (h : p + q = n) :
    (groupResolutionCochains G P).X p ⊗ (groupResolutionCochains H Q).X q ⟶
      (groupCochainTensorComplex G H P Q).X n :=
  HomologicalComplex.ιMapBifunctor (groupResolutionCochains G P)
    (groupResolutionCochains H Q) (curriedTensor (ModuleCat ℤ))
    (ComplexShape.up ℕ) p q n h

/-- Degree `n` component of Weibel's total cochain morphism. -/
noncomputable def groupCochainTotalPairingDegree
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ)) (n : ℕ) :
    (groupCochainTensorComplex G H P Q).X n ⟶
      ((groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
        (Rep.trivial ℤ (G × H) ℤ)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (fun p q h => groupCochainPairingAt G H P Q p q n h)

@[reassoc (attr := simp)]
lemma groupCochainTensorInclusion_comp_totalPairingDegree
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q n : ℕ) (h : p + q = n) :
    groupCochainTensorInclusion G H P Q p q n h ≫
        groupCochainTotalPairingDegree G H P Q n =
      groupCochainPairingAt G H P Q p q n h := by
  apply HomologicalComplex.ι_mapBifunctorDesc

set_option backward.isDefEq.respectTransparency false in
/-- Weibel's morphism of total cochain complexes
`Hom_G(P,ℤ) ⊗ Hom_H(Q,ℤ) → Hom_{G×H}(Tot(P⊗Q),ℤ)`. -/
noncomputable def groupCochainTotalPairing
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ)) :
    groupCochainTensorComplex G H P Q ⟶
      (groupExternalTensorComplex G H P.complex Q.complex).linearYonedaObj ℤ
        (Rep.trivial ℤ (G × H) ℤ) where
  f n := groupCochainTotalPairingDegree G H P Q n
  comm' n n' hnn' := by
    have hn' : n' = n + 1 := by
      exact hnn'.symm
    subst n'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    subst n
    simp only [groupCochainTensorInclusion_comp_totalPairingDegree_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
      Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq
      (groupResolutionCochains G P) (groupResolutionCochains H Q)
      (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel p (p + 1) by simp) q (p + q + 1) (by
        change (p + 1) + q = p + q + 1
        omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq
      (groupResolutionCochains G P) (groupResolutionCochains H Q)
      (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ) p
      (show (ComplexShape.up ℕ).Rel q (q + 1) by simp) (p + q + 1) (by
        change p + (q + 1) = p + q + 1
        omega)]
    have hε :
        ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
            (ComplexShape.up ℕ) (p, q) = ((-1 : ℤˣ) ^ p) := rfl
    have hε₁ :
        ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
            (ComplexShape.up ℕ) (p, q) = 1 := rfl
    rw [hε, hε₁, one_smul, Linear.units_smul_comp, Category.assoc,
      groupCochainTensorInclusion_comp_totalPairingDegree,
      Category.assoc, groupCochainTensorInclusion_comp_totalPairingDegree]
    rw [Units.smul_def]
    simpa [Category.assoc] using groupCochainPairing_d G H P Q p q

lemma moduleTensor_map_left {A A' B : ModuleCat ℤ} (f : A ⟶ A') :
    ((curriedTensor (ModuleCat ℤ)).map f).app B = f ⊗ₘ 𝟙 B := by
  rw [tensorHom_id]
  rfl

lemma moduleTensor_map_right {A B B' : ModuleCat ℤ} (g : B ⟶ B') :
    ((curriedTensor (ModuleCat ℤ)).obj A).map g = 𝟙 A ⊗ₘ g := by
  rw [id_tensorHom]
  rfl

/-- The tensor of two cocycles is a cocycle in the tensor-total cochain
complex.  This is the cycle-level map underlying the canonical
`H^p(C) ⊗ H^q(D) → H^{p+q}(Tot(C⊗D))`. -/
noncomputable def groupCochainTensorCycles
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    (groupResolutionCochains G P).cycles p ⊗
        (groupResolutionCochains H Q).cycles q ⟶
      (groupCochainTensorComplex G H P Q).cycles (p + q) :=
  (groupCochainTensorComplex G H P Q).liftCycles
    (((groupResolutionCochains G P).iCycles p ⊗ₘ
        (groupResolutionCochains H Q).iCycles q) ≫
      groupCochainTensorInclusion G H P Q p q (p + q) rfl)
    (p + q + 1)
    ((ComplexShape.up ℕ).next_eq'
      (show (ComplexShape.up ℕ).Rel (p + q) (p + q + 1) by simp)) (by
      rw [Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
        Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
        HomologicalComplex.mapBifunctor.ι_D₂]
      rw [HomologicalComplex.mapBifunctor.d₁_eq
        (groupResolutionCochains G P) (groupResolutionCochains H Q)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ)
        (show (ComplexShape.up ℕ).Rel p (p + 1) by simp) q (p + q + 1) (by
          change (p + 1) + q = p + q + 1
          omega)]
      rw [HomologicalComplex.mapBifunctor.d₂_eq
        (groupResolutionCochains G P) (groupResolutionCochains H Q)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ) p
        (show (ComplexShape.up ℕ).Rel q (q + 1) by simp) (p + q + 1) (by
          change p + (q + 1) = p + q + 1
          omega)]
      have hε :
          ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (p, q) = ((-1 : ℤˣ) ^ p) := rfl
      have hε₁ :
          ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (p, q) = 1 := rfl
      rw [hε, hε₁, one_smul]
      rw [Preadditive.comp_add]
      have hleft :
          ((groupResolutionCochains G P).iCycles p ⊗ₘ
              (groupResolutionCochains H Q).iCycles q) ≫
              ((curriedTensor (ModuleCat ℤ)).map
                ((groupResolutionCochains G P).d p (p + 1))).app
                  ((groupResolutionCochains H Q).X q) ≫
              groupCochainTensorInclusion G H P Q (p + 1) q
                (p + q + 1) (by omega) = 0 := by
        rw [moduleTensor_map_left, ← Category.assoc, tensorHom_comp_tensorHom,
          HomologicalComplex.iCycles_d, MonoidalPreadditive.zero_tensor, zero_comp]
      have hright :
          ((groupResolutionCochains G P).iCycles p ⊗ₘ
              (groupResolutionCochains H Q).iCycles q) ≫
              ((curriedTensor (ModuleCat ℤ)).obj
                ((groupResolutionCochains G P).X p)).map
                  ((groupResolutionCochains H Q).d q (q + 1)) ≫
              groupCochainTensorInclusion G H P Q p (q + 1)
                (p + q + 1) (by omega) = 0 := by
        rw [moduleTensor_map_right, ← Category.assoc, tensorHom_comp_tensorHom,
          HomologicalComplex.iCycles_d, MonoidalPreadditive.tensor_zero, zero_comp]
      rw [hleft]
      simp only [zero_add]
      rw [Units.smul_def, Linear.comp_smul, hright, smul_zero])

@[reassoc (attr := simp)]
lemma groupCochainTensorCycles_i
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    groupCochainTensorCycles G H P Q p q ≫
        (groupCochainTensorComplex G H P Q).iCycles (p + q) =
      ((groupResolutionCochains G P).iCycles p ⊗ₘ
          (groupResolutionCochains H Q).iCycles q) ≫
        groupCochainTensorInclusion G H P Q p q (p + q) rfl := by
  unfold groupCochainTensorCycles
  exact HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The homology class in the tensor-total cochain complex represented by a
tensor of cocycles. -/
noncomputable def groupCochainTensorCycleClass
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    (groupResolutionCochains G P).cycles p ⊗
        (groupResolutionCochains H Q).cycles q ⟶
      (groupCochainTensorComplex G H P Q).homology (p + q) :=
  groupCochainTensorCycles G H P Q p q ≫
    (groupCochainTensorComplex G H P Q).homologyπ (p + q)

/-- Tensoring a coboundary in the left factor with a cocycle represents zero
in the homology of the tensor-total cochain complex. -/
lemma groupCochainTensorCycleClass_left_boundary
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    ((groupResolutionCochains G P).toCycles ((ComplexShape.up ℕ).prev p) p ⊗ₘ
        𝟙 ((groupResolutionCochains H Q).cycles q)) ≫
        groupCochainTensorCycleClass G H P Q p q = 0 := by
  rcases p with _ | p
  · have hp : ¬(ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0 := by
      intro h
      change (ComplexShape.up ℕ).prev 0 + 1 = 0 at h
      omega
    rw [(groupResolutionCochains G P).toCycles_eq_zero hp,
      MonoidalPreadditive.zero_tensor, zero_comp]
  · have hprev : (ComplexShape.up ℕ).prev (p + 1) = p :=
      (ComplexShape.up ℕ).prev_eq'
        (show (ComplexShape.up ℕ).Rel p (p + 1) by simp)
    rw [hprev]
    let T := groupCochainTensorComplex G H P Q
    let x :
        (groupResolutionCochains G P).X p ⊗
            (groupResolutionCochains H Q).cycles q ⟶
          T.X (p + q) :=
      (𝟙 ((groupResolutionCochains G P).X p) ⊗ₘ
          (groupResolutionCochains H Q).iCycles q) ≫
        groupCochainTensorInclusion G H P Q p q (p + q) rfl
    have hx :
        (((groupResolutionCochains G P).toCycles p (p + 1) ⊗ₘ
              𝟙 ((groupResolutionCochains H Q).cycles q)) ≫
            ((groupResolutionCochains G P).iCycles (p + 1) ⊗ₘ
              (groupResolutionCochains H Q).iCycles q) ≫
            groupCochainTensorInclusion G H P Q (p + 1) q
              (p + 1 + q) rfl) =
          x ≫ T.d (p + q) (p + 1 + q) := by
      dsimp [x, T]
      rw [← Category.assoc, tensorHom_comp_tensorHom,
        HomologicalComplex.toCycles_i]
      rw [Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
        Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
        HomologicalComplex.mapBifunctor.ι_D₂]
      rw [HomologicalComplex.mapBifunctor.d₁_eq
        (groupResolutionCochains G P) (groupResolutionCochains H Q)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ)
        (show (ComplexShape.up ℕ).Rel p (p + 1) by simp) q (p + 1 + q) rfl]
      rw [HomologicalComplex.mapBifunctor.d₂_eq
        (groupResolutionCochains G P) (groupResolutionCochains H Q)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ) p
        (show (ComplexShape.up ℕ).Rel q (q + 1) by simp) (p + 1 + q) (by
          change p + (q + 1) = p + 1 + q
          omega)]
      have hε :
          ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (p, q) = ((-1 : ℤˣ) ^ p) := rfl
      have hε₁ :
          ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (p, q) = 1 := rfl
      rw [hε, hε₁, one_smul]
      rw [Preadditive.comp_add, moduleTensor_map_left, moduleTensor_map_right]
      simp only [Linear.comp_units_smul, ← Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id,
        HomologicalComplex.iCycles_d, MonoidalPreadditive.tensor_zero,
        zero_comp, comp_zero]
      rw [smul_zero, add_zero]
    unfold groupCochainTensorCycleClass groupCochainTensorCycles
    rw [← Category.assoc, HomologicalComplex.comp_liftCycles]
    apply HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
      (K := T) (i' := p + q) (x := x)
    simpa [T, add_assoc] using hx

/-- Tensoring a cocycle in the left factor with a coboundary in the right
factor represents zero in the homology of the tensor-total cochain complex. -/
lemma groupCochainTensorCycleClass_right_boundary
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    (𝟙 ((groupResolutionCochains G P).cycles p) ⊗ₘ
        (groupResolutionCochains H Q).toCycles ((ComplexShape.up ℕ).prev q) q) ≫
        groupCochainTensorCycleClass G H P Q p q = 0 := by
  rcases q with _ | q
  · have hq : ¬(ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0 := by
      intro h
      change (ComplexShape.up ℕ).prev 0 + 1 = 0 at h
      omega
    rw [(groupResolutionCochains H Q).toCycles_eq_zero hq,
      MonoidalPreadditive.tensor_zero, zero_comp]
  · have hprev : (ComplexShape.up ℕ).prev (q + 1) = q :=
      (ComplexShape.up ℕ).prev_eq'
        (show (ComplexShape.up ℕ).Rel q (q + 1) by simp)
    rw [hprev]
    let T := groupCochainTensorComplex G H P Q
    let x₀ :
        (groupResolutionCochains G P).cycles p ⊗
            (groupResolutionCochains H Q).X q ⟶
          T.X (p + q) :=
      ((groupResolutionCochains G P).iCycles p ⊗ₘ
          𝟙 ((groupResolutionCochains H Q).X q)) ≫
        groupCochainTensorInclusion G H P Q p q (p + q) rfl
    let ε : ℤˣ := (-1 : ℤˣ) ^ p
    let x := ε • x₀
    have hx :
        ((𝟙 ((groupResolutionCochains G P).cycles p) ⊗ₘ
              (groupResolutionCochains H Q).toCycles q (q + 1)) ≫
            ((groupResolutionCochains G P).iCycles p ⊗ₘ
              (groupResolutionCochains H Q).iCycles (q + 1)) ≫
            groupCochainTensorInclusion G H P Q p (q + 1)
              (p + (q + 1)) rfl) =
          x ≫ T.d (p + q) (p + (q + 1)) := by
      dsimp [x, x₀, ε, T]
      rw [← Category.assoc, tensorHom_comp_tensorHom,
        HomologicalComplex.toCycles_i]
      rw [Linear.units_smul_comp, Category.assoc,
        HomologicalComplex.mapBifunctor.d_eq,
        Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
        HomologicalComplex.mapBifunctor.ι_D₂]
      rw [HomologicalComplex.mapBifunctor.d₁_eq
        (groupResolutionCochains G P) (groupResolutionCochains H Q)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ)
        (show (ComplexShape.up ℕ).Rel p (p + 1) by simp) q (p + (q + 1)) (by
          change (p + 1) + q = p + (q + 1)
          omega)]
      rw [HomologicalComplex.mapBifunctor.d₂_eq
        (groupResolutionCochains G P) (groupResolutionCochains H Q)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.up ℕ) p
        (show (ComplexShape.up ℕ).Rel q (q + 1) by simp) (p + (q + 1)) rfl]
      have hε :
          ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (p, q) = ((-1 : ℤˣ) ^ p) := rfl
      have hε₁ :
          ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (p, q) = 1 := rfl
      rw [hε, hε₁, one_smul]
      rw [Preadditive.comp_add, moduleTensor_map_left, moduleTensor_map_right]
      simp only [Linear.comp_units_smul, ← Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id,
        HomologicalComplex.iCycles_d, MonoidalPreadditive.zero_tensor,
        zero_comp, comp_zero]
      rw [zero_add, smul_smul, Int.units_mul_self, one_smul]
    unfold groupCochainTensorCycleClass groupCochainTensorCycles
    rw [← Category.assoc, HomologicalComplex.comp_liftCycles]
    apply HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
      (K := T) (i' := p + q) (x := x)
    simpa [T, add_assoc] using hx

/-- The cokernel presentation of the cohomology of the chosen resolution
cochain complex in degree `n`. -/
noncomputable abbrev groupResolutionHomologyCofork
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :
    CokernelCofork
      ((groupResolutionCochains K P).toCycles ((ComplexShape.up ℕ).prev n) n) :=
  CokernelCofork.ofπ
    ((groupResolutionCochains K P).homologyπ n)
    ((groupResolutionCochains K P).toCycles_comp_homologyπ
      ((ComplexShape.up ℕ).prev n) n)

/-- The preceding cofork is a cokernel, by the standard homology
construction. -/
noncomputable def groupResolutionHomologyCoforkIsColimit
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :
    IsColimit (groupResolutionHomologyCofork K P n) :=
  (groupResolutionCochains K P).homologyIsCokernel
    ((ComplexShape.up ℕ).prev n) n rfl

/-- The tensor-of-cocycles homology class as a cofork over the sum of the two
boundary maps. -/
noncomputable def groupCochainTensorCycleClassCofork
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    CokernelCofork
      (coprod.desc
        (((groupResolutionCochains G P).toCycles ((ComplexShape.up ℕ).prev p) p) ▷
          (groupResolutionCochains H Q).cycles q)
        ((groupResolutionCochains G P).cycles p ◁
          (groupResolutionCochains H Q).toCycles ((ComplexShape.up ℕ).prev q) q)) :=
  CokernelCofork.ofπ (groupCochainTensorCycleClass G H P Q p q) (by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, comp_zero]
      simpa only [← tensorHom_id] using
        groupCochainTensorCycleClass_left_boundary G H P Q p q
    · rw [coprod.inr_desc_assoc, comp_zero]
      simpa only [← id_tensorHom] using
        groupCochainTensorCycleClass_right_boundary G H P Q p q)

/-- The canonical cross map from the tensor product of the two resolution
cohomology groups to the cohomology of their tensor-total complex.  It is
obtained by descending the tensor of cocycles through both homology
cokernels. -/
noncomputable def groupCochainTensorHomologyMap
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    (groupResolutionCochains G P).homology p ⊗
        (groupResolutionCochains H Q).homology q ⟶
      (groupCochainTensorComplex G H P Q).homology (p + q) := by
  exact (CokernelCofork.isColimitTensor
      (groupResolutionHomologyCoforkIsColimit G P p)
      (groupResolutionHomologyCoforkIsColimit H Q q)).desc
    (groupCochainTensorCycleClassCofork G H P Q p q)

@[reassoc (attr := simp)]
lemma groupCochainTensorHomologyMap_π
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    ((groupResolutionCochains G P).homologyπ p ⊗ₘ
        (groupResolutionCochains H Q).homologyπ q) ≫
        groupCochainTensorHomologyMap G H P Q p q =
      groupCochainTensorCycleClass G H P Q p q := by
  change _ = (groupCochainTensorCycleClassCofork G H P Q p q).π
  exact Cofork.IsColimit.π_desc
    (CokernelCofork.isColimitTensor
      (groupResolutionHomologyCoforkIsColimit G P p)
      (groupResolutionHomologyCoforkIsColimit H Q q))

/-- Weibel's cohomological cross product at the level of the chosen
resolutions: first take the canonical class in the homology of the tensor
total, then apply the map on homology induced by the constructed total
cochain morphism `μ`. -/
noncomputable def groupResolutionCohomologyCrossProduct
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :=
  groupCochainTensorHomologyMap G H P Q p q ≫
    HomologicalComplex.homologyMap (groupCochainTotalPairing G H P Q) (p + q)

@[reassoc (attr := simp)]
lemma groupResolutionCohomologyCrossProduct_π
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (Q : ProjectiveResolution (Rep.trivial ℤ H ℤ))
    (p q : ℕ) :
    ((groupResolutionCochains G P).homologyπ p ⊗ₘ
        (groupResolutionCochains H Q).homologyπ q) ≫
        groupResolutionCohomologyCrossProduct G H P Q p q =
      groupCochainTensorCycleClass G H P Q p q ≫
        HomologicalComplex.homologyMap (groupCochainTotalPairing G H P Q) (p + q) := by
  simp [groupResolutionCohomologyCrossProduct]

/-- The comparison from Mathlib's resolution-independent group cohomology to
the cohomology computed from a chosen projective resolution.  Naming this
morphism keeps later tensor constructions from unfolding the full Ext
comparison. -/
noncomputable def groupCohomologyResolutionComparisonHom
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :=
  (groupCohomologyIso (Rep.trivial ℤ K ℤ) n P).hom

/-- The inverse comparison from a chosen projective resolution back to
Mathlib's resolution-independent group cohomology. -/
noncomputable def groupCohomologyResolutionComparisonInv
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :=
  (groupCohomologyIso (Rep.trivial ℤ K ℤ) n P).inv

@[reassoc (attr := simp)]
lemma groupCohomologyResolutionComparisonInv_comp_hom
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :
    groupCohomologyResolutionComparisonInv K P n ≫
        (groupCohomologyIso (Rep.trivial ℤ K ℤ) n P).hom = 𝟙 _ := by
  unfold groupCohomologyResolutionComparisonInv
  exact (groupCohomologyIso (Rep.trivial ℤ K ℤ) n P).inv_hom_id

end LeanCategories.Homological
