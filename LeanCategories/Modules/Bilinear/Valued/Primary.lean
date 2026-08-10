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

end LeanCategories.Modules.Bilinear.Valued
