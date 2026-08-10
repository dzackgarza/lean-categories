/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Torsion
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable {R : Type u} [CommRing R]
variable {W : Type u} [AddCommGroup W] [Module R W]

namespace BilinModuleCat

/-- The form on the `I`-primary component. -/
def primaryComponent (A : BilinModuleCat R W) (I : Ideal R) :
    BilinModuleCat R W :=
  A.restrict (Ideal.primaryComponent A.carrier I)

/-- The inclusion of the `I`-primary formed component. -/
def primaryComponentInclusion (A : BilinModuleCat R W) (I : Ideal R) :
    A.primaryComponent I ⟶ A :=
  A.restrictInclusion (Ideal.primaryComponent A.carrier I)

@[simp]
theorem primaryComponent_pairing (A : BilinModuleCat R W) (I : Ideal R)
    (x y : Ideal.primaryComponent A.carrier I) :
    (A.primaryComponent I).pairing x y = A.pairing x y :=
  rfl

/-- A formed morphism restricts to each primary component. -/
def primaryComponentMap {A B : BilinModuleCat R W} (I : Ideal R) (f : A ⟶ B) :
    A.primaryComponent I ⟶ B.primaryComponent I :=
  homMk (Ideal.primaryComponent.map I (underlyingMap f)) fun x y ↦
    map_pairing f x.1 y.1

@[simp]
theorem underlyingMap_primaryComponentMap {A B : BilinModuleCat R W}
    (I : Ideal R) (f : A ⟶ B) :
    underlyingMap (primaryComponentMap I f) =
      Ideal.primaryComponent.map I (underlyingMap f) :=
  rfl

/-- Restriction to an ideal-primary component is functorial on formed modules. -/
def primaryComponentFunctor (I : Ideal R) :
    BilinModuleCat R W ⥤ BilinModuleCat R W where
  obj A := A.primaryComponent I
  map f := primaryComponentMap I f
  map_id A := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Each primary component includes naturally into its formed module. -/
def primaryComponentInclusionNatTrans (I : Ideal R) :
    primaryComponentFunctor I ⟶ 𝟭 (BilinModuleCat R W) where
  app A := A.primaryComponentInclusion I
  naturality A B f := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    rfl

end BilinModuleCat

/-- The `I`-primary component of a finite torsion symmetric form. -/
noncomputable def primaryComponent
    [IsNoetherianRing R]
    (I : Ideal R) (A : FiniteTorsionSymBilinModuleCat R W) :
    FiniteTorsionSymBilinModuleCat R W := by
  let P := Ideal.primaryComponent A.obj.carrier I
  letI : Module.Finite R A.obj.carrier := A.property.1
  haveI : IsNoetherian R A.obj.carrier := inferInstance
  haveI : IsNoetherian R P :=
    isNoetherian_of_submodule_of_noetherian R A.obj.carrier P inferInstance
  refine ⟨A.obj.primaryComponent I, ?_, ?_, ?_⟩
  · change Module.Finite R P
    infer_instance
  · intro x
    obtain ⟨a, ha⟩ := A.property.2.1 (x := x.1)
    exact ⟨a, Subtype.ext ha⟩
  · intro x y
    exact A.property.2.2 x.1 y.1

/-- Primary restriction is a functor on finite torsion symmetric forms. -/
noncomputable def finiteTorsionPrimaryComponentFunctor
    [IsNoetherianRing R] (I : Ideal R) :
    FiniteTorsionSymBilinModuleCat R W ⥤
      FiniteTorsionSymBilinModuleCat R W where
  obj A := primaryComponent I A
  map f := ObjectProperty.homMk
    (BilinModuleCat.primaryComponentMap I f.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentFunctor I).map_id A.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentFunctor I).map_comp f.hom g.hom

/-- The primary-component inclusions are natural on finite torsion symmetric forms. -/
noncomputable def finiteTorsionPrimaryComponentInclusionNatTrans
    [IsNoetherianRing R] (I : Ideal R) :
    finiteTorsionPrimaryComponentFunctor I ⟶
      𝟭 (FiniteTorsionSymBilinModuleCat R W) where
  app A := ObjectProperty.homMk
    (A.obj.primaryComponentInclusion I)
  naturality A B f := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentInclusionNatTrans I).naturality f.hom

/-- The carrier primary components span a torsion form over a Dedekind domain. -/
theorem iSup_primaryComponent_eq_top [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W) :
    ⨆ P : IsDedekindDomain.HeightOneSpectrum R,
        Ideal.primaryComponent A.obj.carrier P.asIdeal = ⊤ :=
  Ideal.iSup_primaryComponent_eq_top A.property.2.1

/-- The carrier primary components form an independent family. -/
theorem iSupIndep_primaryComponent [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W) :
    iSupIndep fun P : IsDedekindDomain.HeightOneSpectrum R ↦
      Ideal.primaryComponent A.obj.carrier P.asIdeal :=
  Ideal.iSupIndep_primaryComponent R A.obj.carrier

/-- A finite torsion carrier is the direct sum of its height-one primary components. -/
noncomputable def primaryComponentLinearEquiv [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W) :
    (Π₀ P : IsDedekindDomain.HeightOneSpectrum R,
      Ideal.primaryComponent A.obj.carrier P.asIdeal) ≃ₗ[R]
        A.obj.carrier := by
  classical
  exact (iSupIndep_primaryComponent A).linearEquiv
    (iSup_primaryComponent_eq_top A)

/-- The bilinear form on the direct sum of all height-one primary components. -/
noncomputable def primaryComponentDirectSumBilinMap [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W) :
    LinearMap.BilinMap R
      (Π₀ P : IsDedekindDomain.HeightOneSpectrum R,
        Ideal.primaryComponent A.obj.carrier P.asIdeal) W :=
  let e := primaryComponentLinearEquiv A
  (A.obj.bilinMap.compl₂ e.toLinearMap).comp e.toLinearMap

/-- The formed direct sum of all height-one primary components. -/
noncomputable def primaryComponentDirectSum [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W) : BilinModuleCat R W :=
  BilinModuleCat.ofBilinMap (primaryComponentDirectSumBilinMap A)

@[simp]
theorem primaryComponentDirectSum_pairing [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (x y : Π₀ P : IsDedekindDomain.HeightOneSpectrum R,
      Ideal.primaryComponent A.obj.carrier P.asIdeal) :
    (primaryComponentDirectSum A).pairing x y =
      A.obj.pairing (primaryComponentLinearEquiv A x)
        (primaryComponentLinearEquiv A y) :=
  rfl

/-- A finite torsion form is the formed direct sum of its primary components. -/
noncomputable def primaryComponentDirectSumIso [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W) :
    primaryComponentDirectSum A ≅ A.obj := by
  let e := primaryComponentLinearEquiv A
  exact {
    hom := BilinModuleCat.homMk e.toLinearMap (fun _ _ ↦ rfl)
    inv := BilinModuleCat.homMk e.symm.toLinearMap (fun x y ↦ by
      change A.obj.pairing (e (e.symm x)) (e (e.symm y)) =
        A.obj.pairing x y
      rw [e.apply_symm_apply, e.apply_symm_apply])
    hom_inv_id := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      change e.symm (e x) = x
      exact e.symm_apply_apply x
    inv_hom_id := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      change e (e.symm x) = x
      exact e.apply_symm_apply x
  }

/-- A formed morphism acts on the direct sum of all primary components. -/
noncomputable def primaryComponentDirectSumMap [IsDedekindDomain R]
    {A B : FiniteTorsionSymBilinModuleCat R W} (f : A ⟶ B) :
    primaryComponentDirectSum A ⟶ primaryComponentDirectSum B :=
  (primaryComponentDirectSumIso A).hom ≫ f.hom ≫
    (primaryComponentDirectSumIso B).inv

/-- Primary decomposition is a functor to formed modules. -/
noncomputable def primaryComponentDirectSumFunctor [IsDedekindDomain R] :
    FiniteTorsionSymBilinModuleCat R W ⥤ BilinModuleCat R W where
  obj := primaryComponentDirectSum
  map := primaryComponentDirectSumMap
  map_id A := by
    simp [primaryComponentDirectSumMap]
  map_comp f g := by
    simp [primaryComponentDirectSumMap, Category.assoc]

/-- The primary direct-sum functor is naturally isomorphic to the underlying form. -/
noncomputable def primaryComponentDirectSumNatIso [IsDedekindDomain R] :
    primaryComponentDirectSumFunctor ≅
      (isFiniteTorsionSymBilinModule R W).ι :=
  NatIso.ofComponents primaryComponentDirectSumIso fun {A B} f ↦ by
    simp [primaryComponentDirectSumFunctor, primaryComponentDirectSumMap,
      Category.assoc]

/-- A vector supported at one height-one primary component. -/
noncomputable def primaryComponentSingle [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (x : Ideal.primaryComponent A.obj.carrier P.asIdeal) :
    Π₀ Q : IsDedekindDomain.HeightOneSpectrum R,
      Ideal.primaryComponent A.obj.carrier Q.asIdeal := by
  classical
  exact DFinsupp.single P x

/-- The direct-sum equivalence includes a vector from one primary component. -/
@[simp]
theorem primaryComponentLinearEquiv_single [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (x : Ideal.primaryComponent A.obj.carrier P.asIdeal) :
    primaryComponentLinearEquiv A (primaryComponentSingle A P x) = x.1 := by
  classical
  have hx := (iSupIndep_primaryComponent A).linearEquiv_symm_apply
    (iSup_primaryComponent_eq_top A) x.property
  have hx' : (primaryComponentLinearEquiv A).symm x.1 =
      primaryComponentSingle A P x := by
    simpa [primaryComponentLinearEquiv, primaryComponentSingle] using hx
  rw [← hx']
  exact (primaryComponentLinearEquiv A).apply_symm_apply x.1

/-- The direct-sum form restricts to the original form on each component. -/
theorem primaryComponentDirectSum_pairing_single [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (x y : Ideal.primaryComponent A.obj.carrier P.asIdeal) :
    (primaryComponentDirectSum A).pairing
      (primaryComponentSingle A P x) (primaryComponentSingle A P y) =
        (A.obj.primaryComponent P.asIdeal).pairing x y := by
  rw [primaryComponentDirectSum_pairing,
    primaryComponentLinearEquiv_single,
    primaryComponentLinearEquiv_single]
  rfl

/-- The canonical projection onto one height-one primary component. -/
noncomputable def primaryComponentProjection [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (P : IsDedekindDomain.HeightOneSpectrum R) :
    A.obj.carrier →ₗ[R] Ideal.primaryComponent A.obj.carrier P.asIdeal :=
  (DFinsupp.lapply (R := R)
    (M := fun Q : IsDedekindDomain.HeightOneSpectrum R ↦
      Ideal.primaryComponent A.obj.carrier Q.asIdeal) P).comp
    (primaryComponentLinearEquiv A).symm.toLinearMap

/-- The primary projection fixes its selected component. -/
@[simp]
theorem primaryComponentProjection_apply [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (x : Ideal.primaryComponent A.obj.carrier P.asIdeal) :
    primaryComponentProjection A P x.1 = x := by
  classical
  change (DFinsupp.lapply (R := R)
    (M := fun Q : IsDedekindDomain.HeightOneSpectrum R ↦
      Ideal.primaryComponent A.obj.carrier Q.asIdeal) P)
      ((primaryComponentLinearEquiv A).symm x.1) = x
  have hx := (iSupIndep_primaryComponent A).linearEquiv_symm_apply
    (iSup_primaryComponent_eq_top A) x.property
  rw [show (primaryComponentLinearEquiv A).symm x.1 =
      DFinsupp.single P x by
    simpa [primaryComponentLinearEquiv] using hx]
  change (DFinsupp.single
    (β := fun Q : IsDedekindDomain.HeightOneSpectrum R ↦
      Ideal.primaryComponent A.obj.carrier Q.asIdeal) P x) P = x
  exact DFinsupp.single_eq_same

/-- The selected primary projection vanishes on every different component. -/
theorem primaryComponentProjection_apply_of_ne [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    {P Q : IsDedekindDomain.HeightOneSpectrum R} (hQP : Q ≠ P)
    (x : Ideal.primaryComponent A.obj.carrier Q.asIdeal) :
    primaryComponentProjection A P x.1 = 0 := by
  classical
  change (DFinsupp.lapply (R := R)
    (M := fun S : IsDedekindDomain.HeightOneSpectrum R ↦
      Ideal.primaryComponent A.obj.carrier S.asIdeal) P)
      ((primaryComponentLinearEquiv A).symm x.1) = 0
  have hx := (iSupIndep_primaryComponent A).linearEquiv_symm_apply
    (iSup_primaryComponent_eq_top A) x.property
  rw [show (primaryComponentLinearEquiv A).symm x.1 =
      DFinsupp.single Q x by
    simpa [primaryComponentLinearEquiv] using hx]
  change (DFinsupp.single
    (β := fun S : IsDedekindDomain.HeightOneSpectrum R ↦
      Ideal.primaryComponent A.obj.carrier S.asIdeal) Q x) P = 0
  exact DFinsupp.single_eq_of_ne (Ne.symm hQP)

/-- Distinct height-one primary components are orthogonal. -/
theorem primaryComponent_pairing_eq_zero_of_ne [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    {P Q : IsDedekindDomain.HeightOneSpectrum R} (hPQ : P ≠ Q)
    (x : Ideal.primaryComponent A.obj.carrier P.asIdeal)
    (y : Ideal.primaryComponent A.obj.carrier Q.asIdeal) :
    A.obj.pairing x y = 0 := by
  obtain ⟨n, hx⟩ :=
    (Ideal.primaryComponent_mem A.obj.carrier P.asIdeal x).mp x.property
  obtain ⟨m, hy⟩ :=
    (Ideal.primaryComponent_mem A.obj.carrier Q.asIdeal y).mp y.property
  have hx0 := (Submodule.mem_torsionBySet_iff _ x.1).mp hx
  have hy0 := (Submodule.mem_torsionBySet_iff _ y.1).mp hy
  have hzP : A.obj.pairing x y ∈
      Submodule.torsionBySet R W ↑(P.asIdeal ^ n) := by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have h := congrArg (fun v : A.obj.carrier ↦ A.obj.pairing v y)
      (hx0 a)
    simpa using h
  have hzQ : A.obj.pairing x y ∈
      Submodule.torsionBySet R W ↑(Q.asIdeal ^ m) := by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have h := congrArg (fun v : A.obj.carrier ↦ A.obj.pairing x v)
      (hy0 a)
    simpa using h
  have hd : Disjoint
      (Submodule.torsionBySet R W ↑(P.asIdeal ^ n))
      (Submodule.torsionBySet R W ↑(Q.asIdeal ^ m)) :=
    Submodule.disjoint_torsionBySet_ideal
      ((P.isCoprime_pow_of_ne Q hPQ n m).sup_eq)
  exact Submodule.disjoint_def.mp hd _ hzP hzQ

/-- Vectors in different direct-sum primary components are orthogonal. -/
theorem primaryComponentDirectSum_pairing_single_eq_zero_of_ne
    [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    {P Q : IsDedekindDomain.HeightOneSpectrum R} (hPQ : P ≠ Q)
    (x : Ideal.primaryComponent A.obj.carrier P.asIdeal)
    (y : Ideal.primaryComponent A.obj.carrier Q.asIdeal) :
    (primaryComponentDirectSum A).pairing
      (primaryComponentSingle A P x) (primaryComponentSingle A Q y) = 0 := by
  rw [primaryComponentDirectSum_pairing,
    primaryComponentLinearEquiv_single,
    primaryComponentLinearEquiv_single]
  exact primaryComponent_pairing_eq_zero_of_ne A hPQ x y

/-- Projecting the first argument preserves pairings with the selected component. -/
theorem primaryComponentProjection_pairing [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (x : A.obj.carrier)
    (y : Ideal.primaryComponent A.obj.carrier P.asIdeal) :
    A.obj.pairing (primaryComponentProjection A P x).1 y.1 =
      A.obj.pairing x y.1 := by
  classical
  let e := primaryComponentLinearEquiv A
  let includeP : Ideal.primaryComponent A.obj.carrier P.asIdeal →ₗ[R]
      A.obj.carrier := (Ideal.primaryComponent A.obj.carrier P.asIdeal).subtype
  let f : A.obj.carrier →ₗ[R] W :=
    (A.obj.bilinMap.flip y.1).comp
      (includeP.comp (primaryComponentProjection A P))
  let g : A.obj.carrier →ₗ[R] W := A.obj.bilinMap.flip y.1
  have hcomp : f.comp e.toLinearMap = g.comp e.toLinearMap := by
    apply DFinsupp.lhom_ext
    intro Q z
    simp only [LinearMap.comp_apply]
    have he : e (DFinsupp.single Q z) = z.1 := by
      simpa [e, primaryComponentSingle] using
        primaryComponentLinearEquiv_single A Q z
    change A.obj.pairing
        (primaryComponentProjection A P (e (DFinsupp.single Q z))).1 y.1 =
      A.obj.pairing (e (DFinsupp.single Q z)) y.1
    rw [he]
    by_cases hQP : Q = P
    · subst Q
      rw [primaryComponentProjection_apply]
    · rw [primaryComponentProjection_apply_of_ne A hQP z]
      change A.obj.bilinMap (0 : A.obj.carrier) y.1 =
        A.obj.pairing z.1 y.1
      rw [map_zero, LinearMap.zero_apply]
      exact (primaryComponent_pairing_eq_zero_of_ne A hQP z y).symm
  have hx := LinearMap.congr_fun hcomp (e.symm x)
  change A.obj.pairing
      (primaryComponentProjection A P (e (e.symm x))).1 y.1 =
    A.obj.pairing (e (e.symm x)) y.1 at hx
  rw [e.apply_symm_apply] at hx
  exact hx

/-- A height-one primary restriction of a radical-free torsion form has zero radical. -/
theorem primaryComponent_isNondegenerate [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (hA : A.obj.IsNondegenerate)
    (P : IsDedekindDomain.HeightOneSpectrum R) :
    (A.obj.primaryComponent P.asIdeal).IsNondegenerate := by
  rw [BilinModuleCat.isNondegenerate_iff_adjoint_injective]
  intro x y hxy
  apply Subtype.ext
  apply (BilinModuleCat.isNondegenerate_iff_adjoint_injective A.obj).mp hA
  apply LinearMap.ext
  intro z
  let f := A.obj.adjoint x.1 - A.obj.adjoint y.1
  have hcomponent (Q : IsDedekindDomain.HeightOneSpectrum R) :
      Ideal.primaryComponent A.obj.carrier Q.asIdeal ≤ LinearMap.ker f := by
    intro w hw
    rw [LinearMap.mem_ker]
    change A.obj.pairing x.1 w - A.obj.pairing y.1 w = 0
    by_cases hQP : Q = P
    · subst Q
      apply sub_eq_zero.mpr
      exact LinearMap.congr_fun hxy ⟨w, hw⟩
    · rw [primaryComponent_pairing_eq_zero_of_ne A (Ne.symm hQP) x ⟨w, hw⟩,
        primaryComponent_pairing_eq_zero_of_ne A (Ne.symm hQP) y ⟨w, hw⟩]
      exact sub_self 0
  have hall : (⨆ Q : IsDedekindDomain.HeightOneSpectrum R,
      Ideal.primaryComponent A.obj.carrier Q.asIdeal) ≤ LinearMap.ker f :=
    iSup_le hcomponent
  rw [iSup_primaryComponent_eq_top A] at hall
  have hzmem : z ∈ LinearMap.ker f := hall (by simp)
  have hz := LinearMap.mem_ker.mp hzmem
  change (A.obj.adjoint x.1) z - (A.obj.adjoint y.1) z = 0 at hz
  exact sub_eq_zero.mp hz

/-- A height-one primary restriction of a perfect torsion form is perfect. -/
theorem primaryComponent_isPerfect [IsDedekindDomain R]
    (A : FiniteTorsionSymBilinModuleCat R W)
    (hA : A.obj.IsPerfect)
    (P : IsDedekindDomain.HeightOneSpectrum R) :
    (A.obj.primaryComponent P.asIdeal).IsPerfect := by
  constructor
  · rw [← BilinModuleCat.isNondegenerate_iff_adjoint_injective]
    exact primaryComponent_isNondegenerate A
      (A.obj.isNondegenerate_of_isPerfect hA) P
  · intro φ
    let extended : A.obj.carrier →ₗ[R] W :=
      φ.comp (primaryComponentProjection A P)
    obtain ⟨x, hx⟩ := hA.2 extended
    refine ⟨primaryComponentProjection A P x, ?_⟩
    apply LinearMap.ext
    intro y
    change A.obj.pairing (primaryComponentProjection A P x).1 y.1 = φ y
    rw [primaryComponentProjection_pairing]
    have hxy := LinearMap.congr_fun hx y.1
    change A.obj.pairing x y.1 =
      φ (primaryComponentProjection A P y.1) at hxy
    rw [primaryComponentProjection_apply] at hxy
    exact hxy

/-- The radical-free category is closed under height-one primary restriction. -/
noncomputable def radicalFreePrimaryComponent [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (A : RadicalFreeFiniteTorsionBilinModuleCat R W) :
    RadicalFreeFiniteTorsionBilinModuleCat R W := by
  let B : FiniteTorsionSymBilinModuleCat R W :=
    ⟨A.obj, A.property.1, A.property.2.1, A.property.2.2.1⟩
  let C := primaryComponent P.asIdeal B
  exact ⟨C.obj, C.property.1, C.property.2.1, C.property.2.2,
    primaryComponent_isNondegenerate B A.property.2.2.2 P⟩

/-- Height-one primary restriction is functorial on radical-free torsion forms. -/
noncomputable def radicalFreePrimaryComponentFunctor [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) :
    RadicalFreeFiniteTorsionBilinModuleCat R W ⥤
      RadicalFreeFiniteTorsionBilinModuleCat R W where
  obj A := radicalFreePrimaryComponent P A
  map f := ObjectProperty.homMk
    (BilinModuleCat.primaryComponentMap P.asIdeal f.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentFunctor P.asIdeal).map_id A.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentFunctor P.asIdeal).map_comp f.hom g.hom

/-- Radical-free primary components include naturally into their source forms. -/
noncomputable def radicalFreePrimaryComponentInclusionNatTrans
    [IsDedekindDomain R] (P : IsDedekindDomain.HeightOneSpectrum R) :
    radicalFreePrimaryComponentFunctor P ⟶
      𝟭 (RadicalFreeFiniteTorsionBilinModuleCat R W) where
  app A := ObjectProperty.homMk
    (A.obj.primaryComponentInclusion P.asIdeal)
  naturality A B f := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentInclusionNatTrans P.asIdeal).naturality f.hom

/-- The perfect finite torsion category is closed under primary restriction. -/
noncomputable def nonsingularPrimaryComponent [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (A : NonsingularFiniteTorsionBilinModuleCat R W) :
    NonsingularFiniteTorsionBilinModuleCat R W := by
  let B : FiniteTorsionSymBilinModuleCat R W :=
    ⟨A.obj, A.property.1, A.property.2.1, A.property.2.2.1⟩
  let C := primaryComponent P.asIdeal B
  exact ⟨C.obj, C.property.1, C.property.2.1, C.property.2.2,
    primaryComponent_isPerfect B A.property.2.2.2 P⟩

/-- Height-one primary restriction is functorial on nonsingular torsion forms. -/
noncomputable def nonsingularPrimaryComponentFunctor [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) :
    NonsingularFiniteTorsionBilinModuleCat R W ⥤
      NonsingularFiniteTorsionBilinModuleCat R W where
  obj A := nonsingularPrimaryComponent P A
  map f := ObjectProperty.homMk
    (BilinModuleCat.primaryComponentMap P.asIdeal f.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentFunctor P.asIdeal).map_id A.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentFunctor P.asIdeal).map_comp f.hom g.hom

/-- Nonsingular primary components include naturally into their source forms. -/
noncomputable def nonsingularPrimaryComponentInclusionNatTrans
    [IsDedekindDomain R] (P : IsDedekindDomain.HeightOneSpectrum R) :
    nonsingularPrimaryComponentFunctor P ⟶
      𝟭 (NonsingularFiniteTorsionBilinModuleCat R W) where
  app A := ObjectProperty.homMk
    (A.obj.primaryComponentInclusion P.asIdeal)
  naturality A B f := by
    apply ObjectProperty.hom_ext
    exact (BilinModuleCat.primaryComponentInclusionNatTrans P.asIdeal).naturality f.hom

end LeanCategories.Modules.Bilinear.Valued
