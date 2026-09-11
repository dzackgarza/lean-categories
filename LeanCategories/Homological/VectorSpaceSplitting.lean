/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SplitComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.LinearAlgebra.Projection

import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Splittings of complexes of vector spaces

Weibel, *An Introduction to Homological Algebra* (1994), §1.4,
FC05-C01-U030.

Over a field, choosing complements to the image of each differential produces
reverse-degree maps satisfying `d = d s d`.  The basic construction below works
over any division ring and for an arbitrary homological-complex shape.

For ordinary `ℤ`-indexed chain complexes, the chosen generalized inverses are
normalized so that consecutive splitting maps compose to zero.  Then
`p = d s + s d` is an idempotent null-homotopic projection.  Its kernel is a
zero-differential complex representing homology, its range is contractible, and
the two complementary summands give an isomorphism of complexes
`range(p) ⊞ ker(p) ≅ C`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

/-- Every linear map of vector spaces has an inner inverse `g` with `f = f g f`. -/
theorem existsInnerInverse
    {K : Type u} [DivisionRing K]
    {V W : Type v} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) : ∃ g : W →ₗ[K] V, f = f.comp (g.comp f) := by
  obtain ⟨q, hq⟩ := f.range.exists_isCompl
  obtain ⟨r, hr⟩ :=
    f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let g : W →ₗ[K] V := r.comp (f.range.projectionOnto q hq)
  refine ⟨g, LinearMap.ext fun x => ?_⟩
  change f x = f (r (f.range.projectionOnto q hq (f x)))
  rw [Submodule.projectionOnto_apply_of_mem_left hq (LinearMap.mem_range_self f x)]
  have hrx := LinearMap.congr_fun hr ⟨f x, LinearMap.mem_range_self f x⟩
  exact congrArg Subtype.val hrx |>.symm

variable {K : Type u} [DivisionRing K]
variable {ι : Type*} {c : ComplexShape ι}

/-- Every complex of vector spaces admits Weibel splitting maps `d = d s d`. -/
noncomputable def vectorSpaceSplitting
    (C : HomologicalComplex (ModuleCat.{v} K) c) : Splitting C where
  s i j _ := ModuleCat.ofHom <| Classical.choose (existsInnerInverse (C.d j i).hom)
  d_s_d i j _ := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    rw [LinearMap.comp_assoc]
    exact Classical.choose_spec (existsInnerInverse (C.d i j).hom)

/-- Every complex of vector spaces is split in Weibel's sense. -/
theorem isSplit_vectorSpace
    (C : HomologicalComplex (ModuleCat.{v} K) c) : IsSplit C :=
  ⟨vectorSpaceSplitting C⟩

end LeanCategories.Homological

namespace LeanCategories.Homological

open CategoryTheory Limits

universe v u

/-- Every linear map of vector spaces admits a reflexive generalized inverse. -/
theorem existsReflexiveInverse {K : Type u} [DivisionRing K]
    {V W : Type v} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) :
    ∃ g : W →ₗ[K] V, f = f.comp (g.comp f) ∧ g = g.comp (f.comp g) := by
  let g := Classical.choose (existsInnerInverse f)
  have hfgf : f = f.comp (g.comp f) := Classical.choose_spec (existsInnerInverse f)
  have e (x : V) : f (g (f x)) = f x :=
    (LinearMap.congr_fun hfgf x).symm
  let h := g.comp (f.comp g)
  refine ⟨h, ?_, ?_⟩
  · ext x
    simp only [h, LinearMap.comp_apply]
    rw [e, e]
  · ext y
    simp only [h, LinearMap.comp_apply]
    rw [e, e]


variable {K : Type u} [DivisionRing K]

/-- A reflexive generalized inverse for an individual differential. -/
noncomputable def rawDifferentialInverse
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (i j : ℤ) : C.X j ⟶ C.X i :=
  ModuleCat.ofHom (Classical.choose (existsReflexiveInverse (C.d i j).hom))

@[reassoc]
theorem rawDifferentialInverse_d_s_d
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (i j : ℤ) :
    C.d i j ≫ rawDifferentialInverse C i j ≫ C.d i j = C.d i j := by
  apply ModuleCat.hom_ext
  simpa [rawDifferentialInverse, ModuleCat.hom_comp, LinearMap.comp_assoc] using
    (Classical.choose_spec (existsReflexiveInverse (C.d i j).hom)).1.symm

@[reassoc]
theorem rawDifferentialInverse_s_d_s
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (i j : ℤ) :
    rawDifferentialInverse C i j ≫ C.d i j ≫ rawDifferentialInverse C i j =
      rawDifferentialInverse C i j := by
  apply ModuleCat.hom_ext
  simpa [rawDifferentialInverse, ModuleCat.hom_comp, LinearMap.comp_assoc] using
    (Classical.choose_spec (existsReflexiveInverse (C.d i j).hom)).2.symm

noncomputable def coherentChainSplittingMap
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) : C.X n ⟶ C.X (n + 1) :=
  (𝟙 (C.X n) - C.d n (n - 1) ≫ rawDifferentialInverse C n (n - 1)) ≫
    rawDifferentialInverse C (n + 1) n

@[reassoc]
theorem coherentChainSplittingMap_d_s_d
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    C.d (n + 1) n ≫ coherentChainSplittingMap C n ≫ C.d (n + 1) n = C.d (n + 1) n := by
  have hkill :
      C.d (n + 1) n ≫
        (𝟙 (C.X n) - C.d n (n - 1) ≫ rawDifferentialInverse C n (n - 1)) =
        C.d (n + 1) n := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, C.d_comp_d,
      Limits.zero_comp, sub_zero]
  calc
    C.d (n + 1) n ≫ coherentChainSplittingMap C n ≫ C.d (n + 1) n =
        C.d (n + 1) n ≫ rawDifferentialInverse C (n + 1) n ≫ C.d (n + 1) n := by
          simpa only [coherentChainSplittingMap, Category.assoc] using
            congrArg (fun k => k ≫ rawDifferentialInverse C (n + 1) n ≫ C.d (n + 1) n) hkill
    _ = C.d (n + 1) n := rawDifferentialInverse_d_s_d C (n + 1) n

@[reassoc]
theorem coherentChainSplittingMap_sq
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    coherentChainSplittingMap C n ≫ coherentChainSplittingMap C (n + 1) = 0 := by
  have hrs :
      rawDifferentialInverse C (n + 1) n ≫
        (C.d (n + 1) n ≫ rawDifferentialInverse C (n + 1) n) =
        rawDifferentialInverse C (n + 1) n := by
    simpa only [Category.assoc] using rawDifferentialInverse_s_d_s C (n + 1) n
  have hmiddle :
      rawDifferentialInverse C (n + 1) n ≫
        (𝟙 (C.X (n + 1)) -
          C.d (n + 1) n ≫ rawDifferentialInverse C (n + 1) n) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, hrs, sub_self]
  have hn : n + 1 - 1 = n := by omega
  rw [coherentChainSplittingMap, coherentChainSplittingMap, hn]
  simpa only [Category.assoc, Limits.zero_comp, Limits.comp_zero] using
    congrArg
      (fun k =>
        (𝟙 (C.X n) - C.d n (n - 1) ≫ rawDifferentialInverse C n (n - 1)) ≫
          k ≫ rawDifferentialInverse C (n + 1 + 1) (n + 1)) hmiddle

/-- The splitting map associated to a differential `C.d i j`, with `i = j + 1`. -/
noncomputable def differentialSplittingMap
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (i j : ℤ) (h : j + 1 = i) :
    C.X j ⟶ C.X i :=
  coherentChainSplittingMap C j ≫ (C.XIsoOfEq h).hom

@[reassoc]
lemma differentialSplittingMap_d_s_d
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (i j : ℤ) (h : j + 1 = i) :
    C.d i j ≫ differentialSplittingMap C i j h ≫ C.d i j = C.d i j := by
  subst i
  simpa only [differentialSplittingMap, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id] using coherentChainSplittingMap_d_s_d C j

@[reassoc]
lemma differentialSplittingMap_comp_next
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (i j k : ℤ)
    (hij : j + 1 = i) (hik : i + 1 = k) :
    differentialSplittingMap C i j hij ≫ differentialSplittingMap C k i hik = 0 := by
  subst i
  subst k
  simpa only [differentialSplittingMap, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id] using coherentChainSplittingMap_sq C j

/-- The normalized degree-reversing maps, indexed by the chain-complex relation. -/
noncomputable def normalizedChainSplitting
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : Splitting C where
  s i j hij :=
    differentialSplittingMap C j i (by simpa only [ComplexShape.down_Rel] using hij)
  d_s_d i j hij :=
    (differentialSplittingMap_d_s_d C i j
      (by simpa only [ComplexShape.down_Rel] using hij)).symm

/-- The endomorphism `d s + s d` attached to the normalized splitting maps. -/
noncomputable def splittingProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : C ⟶ C :=
  Homotopy.nullHomotopicMap' (normalizedChainSplitting C).s

lemma splittingProjection_f
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    (splittingProjection C).f n =
      C.d n (n - 1) ≫ differentialSplittingMap C n (n - 1) (by omega) +
        differentialSplittingMap C (n + 1) n (by omega) ≫ C.d (n + 1) n := by
  have hleft : (ComplexShape.down ℤ).Rel n (n - 1) := by simp
  have hright : (ComplexShape.down ℤ).Rel (n + 1) n := by simp
  simpa only [splittingProjection, normalizedChainSplitting] using
    Homotopy.nullHomotopicMap'_f (C := C) (D := C) hright hleft
      (normalizedChainSplitting C).s

lemma splittingProjection_idempotent
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    splittingProjection C ≫ splittingProjection C = splittingProjection C := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f]
  rw [splittingProjection_f]
  rw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [Category.assoc]
  rw [Preadditive.comp_add]
  rw [differentialSplittingMap_d_s_d_assoc]
  rw [differentialSplittingMap_comp_next_assoc, Limits.zero_comp]
  rw [C.d_comp_d_assoc, Limits.zero_comp]
  rw [differentialSplittingMap_d_s_d]
  simp

lemma splittingProjection_comp_d
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    (splittingProjection C).f n ≫ C.d n (n - 1) = C.d n (n - 1) := by
  rw [splittingProjection_f, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [differentialSplittingMap_d_s_d]
  rw [C.d_comp_d, Limits.comp_zero, add_zero]

/-- The complementary idempotent `1 - (d s + s d)`. -/
noncomputable def homologyProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : C ⟶ C :=
  𝟙 C - splittingProjection C

lemma homologyProjection_comp_splittingProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    homologyProjection C ≫ splittingProjection C = 0 := by
  rw [homologyProjection, Preadditive.sub_comp, Category.id_comp,
    splittingProjection_idempotent, sub_self]

lemma splittingProjection_comp_homologyProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    splittingProjection C ≫ homologyProjection C = 0 := by
  rw [homologyProjection, Preadditive.comp_sub, Category.comp_id,
    splittingProjection_idempotent, sub_self]

lemma homologyProjection_idempotent
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    homologyProjection C ≫ homologyProjection C = homologyProjection C := by
  rw [homologyProjection, Preadditive.sub_comp, Preadditive.comp_sub,
    Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    splittingProjection_idempotent]
  abel

lemma splittingProjection_linear_idempotent
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    IsIdempotentElem ((splittingProjection C).f n).hom := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp]
  have h := congrArg (fun f : C ⟶ C => f.f n) (splittingProjection_idempotent C)
  have hh := congrArg ModuleCat.Hom.hom h
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp] using hh

lemma splittingProjection_linear_isProj
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    LinearMap.IsProj (LinearMap.range ((splittingProjection C).f n).hom)
      ((splittingProjection C).f n).hom := by
  let f := ((splittingProjection C).f n).hom
  have hidem : IsIdempotentElem f := by
    simpa only [f] using splittingProjection_linear_idempotent C n
  have hcomp : f.comp f = f := by
    simpa only [Module.End.mul_eq_comp] using hidem.eq
  refine ⟨fun x => LinearMap.mem_range_self f x, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact LinearMap.congr_fun hcomp x

/-- Degreewise Weibel decomposition into the contractible projection range and its kernel. -/
noncomputable def vectorSpaceDegreeDecomposition
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    (LinearMap.range ((splittingProjection C).f n).hom ×
        LinearMap.ker ((splittingProjection C).f n).hom) ≃ₗ[K] C.X n :=
  Submodule.prodEquivOfIsCompl _ _
    (splittingProjection_linear_isProj C n).isCompl

lemma splittingProjectionKernel_d_eq_zero
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ)
    (x : LinearMap.ker ((splittingProjection C).f n).hom) :
    (C.d n (n - 1)).hom x = 0 := by
  have h := congrArg ModuleCat.Hom.hom (splittingProjection_comp_d C n)
  have hx := LinearMap.congr_fun h x.1
  have hker : ((splittingProjection C).f n).hom x = 0 := x.2
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hker, map_zero] using hx.symm

/-- The degree-`n` kernel of the contractible projection. -/
noncomputable abbrev homologyRepresentativeSpace
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) : ModuleCat.{v} K :=
  ModuleCat.of K (LinearMap.ker ((splittingProjection C).f n).hom)

/-- The kernel of `d s + s d`, regarded as a chain complex with zero differentials. -/
noncomputable def homologyRepresentativeComplex
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : ChainComplex (ModuleCat.{v} K) ℤ where
  X n := homologyRepresentativeSpace C n
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := Limits.zero_comp

/-- Inclusion of the zero-differential homology representative into the original complex. -/
noncomputable def homologyRepresentativeInclusion
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : homologyRepresentativeComplex C ⟶ C where
  f n := show homologyRepresentativeSpace C n ⟶ C.X n from
    ModuleCat.ofHom (LinearMap.ker ((splittingProjection C).f n).hom).subtype
  comm' i j hij := by
    have h : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    subst i
    change ModuleCat.ofHom (LinearMap.ker ((splittingProjection C).f (j + 1)).hom).subtype ≫
        C.d (j + 1) j = 0
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hz := splittingProjectionKernel_d_eq_zero C (j + 1) x
    rw [show j + 1 - 1 = j by omega] at hz
    simpa [ModuleCat.hom_comp] using hz


lemma d_comp_homologyProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    C.d n (n - 1) ≫ (homologyProjection C).f (n - 1) = 0 := by
  have hpcomm := (splittingProjection C).comm n (n - 1)
  have hn : (ComplexShape.down ℤ).Rel n (n - 1) := by simp
  have hpcomm' := (splittingProjection C).comm' n (n - 1) hn
  rw [homologyProjection]
  change C.d n (n - 1) ≫ (𝟙 (C.X (n - 1)) - (splittingProjection C).f (n - 1)) = 0
  rw [Preadditive.comp_sub, Category.comp_id, ← hpcomm', splittingProjection_comp_d, sub_self]

lemma homologyProjection_mem_kernel
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) (x : C.X n) :
    (homologyProjection C).f n x ∈ LinearMap.ker ((splittingProjection C).f n).hom := by
  change ((splittingProjection C).f n).hom ((homologyProjection C).f n x) = 0
  have h := congrArg (fun f : C ⟶ C => f.f n)
    (homologyProjection_comp_splittingProjection C)
  have hh := congrArg ModuleCat.Hom.hom h
  have hx := LinearMap.congr_fun hh x
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.zero_f_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hx

/-- Projection from the original complex onto the zero-differential homology representative. -/
noncomputable def homologyRepresentativeProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : C ⟶ homologyRepresentativeComplex C where
  f n := show C.X n ⟶ homologyRepresentativeSpace C n from
    ModuleCat.ofHom (((homologyProjection C).f n).hom.codRestrict _
      (homologyProjection_mem_kernel C n))
  comm' i j hij := by
    have h : j + 1 = i := by
      simpa only [ComplexShape.down_Rel] using hij
    subst i
    change 0 = C.d (j + 1) j ≫
      ModuleCat.ofHom (((homologyProjection C).f j).hom.codRestrict _
        (homologyProjection_mem_kernel C j))
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hz := d_comp_homologyProjection C (j + 1)
    rw [show j + 1 - 1 = j by omega] at hz
    have hzh := congrArg ModuleCat.Hom.hom hz
    have hzx := LinearMap.congr_fun hzh x
    ext
    simpa [ModuleCat.hom_comp] using hzx.symm

lemma homologyRepresentativeProjection_inclusion
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    homologyRepresentativeProjection C ≫ homologyRepresentativeInclusion C =
      homologyProjection C := by
  ext n x
  rfl

@[reassoc (attr := simp)]
lemma homologyRepresentativeInclusion_projection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    homologyRepresentativeInclusion C ≫ homologyRepresentativeProjection C =
      𝟙 (homologyRepresentativeComplex C) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change homologyRepresentativeSpace C n at x
  apply Subtype.ext
  change (homologyProjection C).f n (x : C.X n) = (x : C.X n)
  rw [homologyProjection]
  change x - (splittingProjection C).f n x = x
  have hx : ((splittingProjection C).f n).hom x = 0 := x.2
  rw [show (splittingProjection C).f n x = 0 from hx, sub_zero]

noncomputable def splittingProjectionNullHomotopic
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    Homotopy (splittingProjection C) 0 := by
  let h := Homotopy.nullHomotopy'
    (fun i j hij => differentialSplittingMap C j i (by
      simpa only [ComplexShape.down_Rel] using hij))
  exact h

noncomputable def homologyProjectionHomotopyId
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    Homotopy (homologyProjection C) (𝟙 C) := by
  let e : Homotopy (homologyProjection C) (𝟙 C) ≃
      Homotopy (homologyProjection C - 𝟙 C) 0 := Homotopy.equivSubZero
  refine e.symm ?_
  have h := (splittingProjectionNullHomotopic C).smul (-1 : ℤ)
  simpa [homologyProjection, sub_eq_add_neg] using h

/-- A complex of vector spaces is homotopy equivalent to the zero-differential
kernel of `d s + s d`; its complementary range is the contractible summand. -/
noncomputable def vectorSpaceHomotopyEquivHomologyRepresentative
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    HomotopyEquiv (homologyRepresentativeComplex C) C where
  hom := homologyRepresentativeInclusion C
  inv := homologyRepresentativeProjection C
  homotopyHomInvId := Homotopy.ofEq (homologyRepresentativeInclusion_projection C)
  homotopyInvHomId :=
    (Homotopy.ofEq (homologyRepresentativeProjection_inclusion C)).trans
      (homologyProjectionHomotopyId C)


lemma differential_mem_splittingProjection_range
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (i j : ℤ)
    (x : LinearMap.range ((splittingProjection C).f i).hom) :
    (C.d i j).hom x ∈ LinearMap.range ((splittingProjection C).f j).hom := by
  rw [(splittingProjection_linear_isProj C j).mem_iff_map_id]
  have hx := (splittingProjection_linear_isProj C i).map_id x x.2
  have hcomm := congrArg ModuleCat.Hom.hom ((splittingProjection C).comm i j)
  have hcommx := LinearMap.congr_fun hcomm x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hx] using hcommx.symm

/-- The range of `d s + s d`, with the differential induced from `C`. -/
noncomputable def contractibleRepresentativeComplex
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : ChainComplex (ModuleCat.{v} K) ℤ where
  X n := ModuleCat.of K (LinearMap.range ((splittingProjection C).f n).hom)
  d i j := ModuleCat.ofHom (((C.d i j).hom.domRestrict
    (LinearMap.range ((splittingProjection C).f i).hom)).codRestrict _
      (differential_mem_splittingProjection_range C i j))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d i j).hom x = 0
    rw [C.shape i j hij]
    rfl
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d j k).hom ((C.d i j).hom x) = 0
    have hz := congrArg ModuleCat.Hom.hom (C.d_comp_d i j k)
    exact LinearMap.congr_fun hz x

/-- Inclusion of the contractible projection range into `C`. -/
noncomputable def contractibleRepresentativeInclusion
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : contractibleRepresentativeComplex C ⟶ C where
  f n := ModuleCat.ofHom (LinearMap.range ((splittingProjection C).f n).hom).subtype
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Projection of `C` onto the range of `d s + s d`. -/
noncomputable def contractibleRepresentativeProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) : C ⟶ contractibleRepresentativeComplex C where
  f n := ModuleCat.ofHom (((splittingProjection C).f n).hom.codRestrict _
    (fun x => LinearMap.mem_range_self _ x))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d i j).hom (((splittingProjection C).f i).hom x) =
      ((splittingProjection C).f j).hom ((C.d i j).hom x)
    have hcomm := congrArg ModuleCat.Hom.hom ((splittingProjection C).comm i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using LinearMap.congr_fun hcomm x

lemma contractibleRepresentativeProjection_inclusion
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    contractibleRepresentativeProjection C ≫ contractibleRepresentativeInclusion C =
      splittingProjection C := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

@[reassoc (attr := simp)]
lemma contractibleRepresentativeInclusion_projection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    contractibleRepresentativeInclusion C ≫ contractibleRepresentativeProjection C =
      𝟙 (contractibleRepresentativeComplex C) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ModuleCat.of K (LinearMap.range ((splittingProjection C).f n).hom) at x
  apply Subtype.ext
  change ((splittingProjection C).f n).hom (x : C.X n) = (x : C.X n)
  exact (splittingProjection_linear_isProj C n).map_id x x.2

/-- The projection-range summand is contractible. -/
noncomputable def contractibleRepresentativeContraction
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    Homotopy (𝟙 (contractibleRepresentativeComplex C)) 0 := by
  have hp : Homotopy (splittingProjection C) 0 := splittingProjectionNullHomotopic C
  have h := (hp.compLeft (contractibleRepresentativeInclusion C)).compRight
    (contractibleRepresentativeProjection C)
  refine (Homotopy.ofEq ?_).symm.trans (h.trans (Homotopy.ofEq ?_))
  · rw [← contractibleRepresentativeProjection_inclusion]
    simp only [Category.assoc, contractibleRepresentativeInclusion_projection]
    simpa only [Category.comp_id] using contractibleRepresentativeInclusion_projection C
  · simp


@[reassoc (attr := simp)]
lemma contractibleInclusion_homologyProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    contractibleRepresentativeInclusion C ≫ homologyRepresentativeProjection C = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ModuleCat.of K (LinearMap.range ((splittingProjection C).f n).hom) at x
  apply Subtype.ext
  change (homologyProjection C).f n (x : C.X n) = 0
  rw [homologyProjection]
  change x - (splittingProjection C).f n x = 0
  exact sub_eq_zero.mpr ((splittingProjection_linear_isProj C n).map_id x x.2).symm

@[reassoc (attr := simp)]
lemma homologyInclusion_contractibleProjection
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    homologyRepresentativeInclusion C ≫ contractibleRepresentativeProjection C = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change homologyRepresentativeSpace C n at x
  apply Subtype.ext
  change ((splittingProjection C).f n).hom (x : C.X n) = 0
  exact x.2

/-- Weibel's decomposition of a chain complex of vector spaces into the contractible
projection range and the zero-differential homology representative. -/
noncomputable def vectorSpaceComplexDecomposition
    (C : ChainComplex (ModuleCat.{v} K) ℤ) :
    contractibleRepresentativeComplex C ⊞ homologyRepresentativeComplex C ≅ C where
  hom := biprod.desc (contractibleRepresentativeInclusion C) (homologyRepresentativeInclusion C)
  inv := biprod.lift (contractibleRepresentativeProjection C) (homologyRepresentativeProjection C)
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [Category.assoc, contractibleRepresentativeInclusion_projection]
      · simp [Category.assoc, contractibleInclusion_homologyProjection]
    · apply biprod.hom_ext
      · simp [Category.assoc, homologyInclusion_contractibleProjection]
      · simp [Category.assoc, homologyRepresentativeInclusion_projection]
  inv_hom_id := by
    rw [biprod.lift_desc, contractibleRepresentativeProjection_inclusion,
      homologyRepresentativeProjection_inclusion, homologyProjection]
    abel


/-- The zero-differential kernel summand in degree `n` is canonically isomorphic
to the ordinary homology of `C` in degree `n`. -/
noncomputable def homologyRepresentativeIsoHomology
    (C : ChainComplex (ModuleCat.{v} K) ℤ) (n : ℤ) :
    homologyRepresentativeSpace C n ≅ C.homology n :=
  let H := homologyRepresentativeComplex C
  H.pOpcyclesIso (n + 1) n
      ((ComplexShape.down ℤ).prev_eq' (by simp)) rfl ≪≫
    (H.isoHomologyι n (n - 1)
      ((ComplexShape.down ℤ).next_eq' (by simp)) rfl).symm ≪≫
    (vectorSpaceHomotopyEquivHomologyRepresentative C).toHomologyIso n



end LeanCategories.Homological
