/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.OreLocalization.Ring

/-!
# The localization comparison map for Hom

Weibel, *An Introduction to Homological Algebra* (1994), §3.3, pp. 73--75
(FC05-C03-U031).

The source allows a central multiplicative set in a possibly noncommutative
ring.  We use Mathlib's Ore localization for the ring and modules, and localize
`Hom_R(A,B)` over the commutative center `Z(R)`.  Centrality identifies the
given multiplicative set with a submonoid of `Z(R)`, so no commutativity
hypothesis on `R` is introduced.

For fractions the comparison is

`(f/s)(a/t) = f(a)/(st)`.

The comparison map and its fraction formula are constructed here.  The next
source unit, FC05-C03-U032, is the theorem that it is an isomorphism when `A`
is finitely presented.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v w

/-- A multiplicative subset lies in the center of an associative ring. -/
def IsCentralSubmonoid {R : Type u} [Ring R] (S : Submonoid R) : Prop :=
  ∀ (s : S) (r : R), (s : R) * r = r * (s : R)

/-- A central submonoid is a left Ore set.  For central denominators the Ore numerator and
denominator are the original numerator and denominator. -/
@[instance_reducible]
def centralOreSet {R : Type u} [Ring R] (S : Submonoid R) (hS : IsCentralSubmonoid S) :
    OreLocalization.OreSet S where
  ore_right_cancel r₁ r₂ s h := by
    refine ⟨s, ?_⟩
    rw [hS s r₁, h, ← hS s r₂]
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := hS s r

/-- Regard the central elements of `S` as a submonoid of the center of `R`.

Under `IsCentralSubmonoid S`, every element of `S` has a representative here; the definition is
made without that hypothesis so the type does not depend on a proof of centrality. -/
def centralSubmonoid {R : Type u} [Ring R] (S : Submonoid R) :
    Submonoid (Subring.center R) :=
  S.comap (Subring.subtype (Subring.center R)).toMonoidHom

/-- Forget that a denominator was regarded as an element of the center. -/
def toCentralDenom {R : Type u} [Ring R] (S : Submonoid R) (s : centralSubmonoid S) : S :=
  ⟨(s.1 : R), s.2⟩

/-- Regard a denominator from a central submonoid as an element of the center. -/
def ofCentralDenom {R : Type u} [Ring R] (S : Submonoid R) (hS : IsCentralSubmonoid S)
    (s : S) : centralSubmonoid S :=
  ⟨⟨s, Subring.mem_center_iff.mpr fun r => (hS s r).symm⟩, s.2⟩

/-- For `f : A →ₗ[R] B` and `d ∈ S`, the localized linear map
`a/t ↦ f(a)/(dt)`.

This is `S⁻¹R`-linear even when `R` is noncommutative because every denominator is central. -/
noncomputable def localizedLinearMapFraction {R : Type u} [Ring R]
    (S : Submonoid R) (hS : IsCentralSubmonoid S)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (d : S) :
    letI := centralOreSet S hS
    A[S⁻¹] →ₗ[R[S⁻¹]] B[S⁻¹] := by
  let _ := centralOreSet S hS
  refine
    { toFun := OreLocalization.liftExpand (fun a s => f a /ₒ (d * s)) ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro a r s hrs
    have hrds : r * ((d : R) * s) = (d : R) * (r * s) := by
      calc
        r * ((d : R) * s) = (r * d) * s := (mul_assoc _ _ _).symm
        _ = (d * r) * s := by rw [hS d r]
        _ = d * (r * s) := mul_assoc _ _ _
    have hmem : r * ((d : R) * s) ∈ S := by
      rw [hrds]
      exact mul_mem d.2 hrs
    have hexpand := OreLocalization.expand (f a) (d * s) r hmem
    rw [f.map_smul]
    exact hexpand.trans <| by
      congr 1
      apply Subtype.ext
      simp only [Submonoid.coe_mul]
      exact hrds
  · intro x y
    induction x using OreLocalization.ind with | _ a s => ?_
    induction y using OreLocalization.ind with | _ b t => ?_
    rw [OreLocalization.oreDiv_add_char (r := a) (r' := b) s t (s : R) t (hS t s)]
    simp only [OreLocalization.liftExpand_of, Submonoid.smul_def, f.map_add, f.map_smul]
    have hadd : (t : R) * ((d : R) * s) = (s : R) * ((d : R) * t) := by
      calc
        (t : R) * (d * s) = (t * d) * s := (mul_assoc _ _ _).symm
        _ = (d * t) * s := by rw [hS t d]
        _ = d * (t * s) := mul_assoc _ _ _
        _ = d * (s * t) := by rw [hS t s]
        _ = (d * s) * t := (mul_assoc _ _ _).symm
        _ = (s * d) * t := by rw [hS d s]
        _ = s * (d * t) := mul_assoc _ _ _
    rw [OreLocalization.oreDiv_add_char (r := f a) (r' := f b) (d * s) (d * t)
      (s : R) t hadd]
    simp only [Submonoid.smul_def]
    have hden : d * (t * s) = t * (d * s) := by
      apply Subtype.ext
      simp only [Submonoid.coe_mul]
      calc
        (d : R) * (t * s) = (d * t) * s := (mul_assoc _ _ _).symm
        _ = (t * d) * s := by rw [hS t d]
        _ = t * (d * s) := mul_assoc _ _ _
    rw [hden]
  · intro q x
    induction q using OreLocalization.ind with | _ r s => ?_
    induction x using OreLocalization.ind with | _ a t => ?_
    rw [OreLocalization.oreDiv_smul_char r a s t r t (hS t r)]
    simp only [OreLocalization.liftExpand_of, f.map_smul, RingHom.id_apply]
    rw [OreLocalization.oreDiv_smul_char r (f a) s (d * t) r (d * t) (hS (d * t) r)]
    have hden : d * (t * s) = (d * t) * s := by
      apply Subtype.ext
      simp only [Submonoid.coe_mul, mul_assoc]
    rw [hden]

@[simp]
theorem localizedLinearMapFraction_oreDiv {R : Type u} [Ring R]
    (S : Submonoid R) (hS : IsCentralSubmonoid S)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (d : S) (a : A) (s : S) :
    letI := centralOreSet S hS
    localizedLinearMapFraction S hS f d (a /ₒ s) = f a /ₒ (d * s) := by
  let _ := centralOreSet S hS
  simp [localizedLinearMapFraction]

/-- The additive group `S⁻¹ Hom_R(A,B)`, implemented by localizing over the commutative center of
`R`. -/
abbrev CentralLocalizedHom {R : Type u} [Ring R] (S : Submonoid R)
    (A : Type v) [AddCommGroup A] [Module R A]
    (B : Type w) [AddCommGroup B] [Module R B] :=
  LocalizedModule (centralSubmonoid S) (A →ₗ[R] B)

noncomputable def comparisonPair {R : Type u} [Ring R]
    (S : Submonoid R) (hS : IsCentralSubmonoid S)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (p : (A →ₗ[R] B) × centralSubmonoid S) :
    letI := centralOreSet S hS
    A[S⁻¹] →ₗ[R[S⁻¹]] B[S⁻¹] := by
  let _ := centralOreSet S hS
  exact localizedLinearMapFraction S hS p.1 (toCentralDenom S p.2)

theorem comparisonPair_wd {R : Type u} [Ring R]
    (S : Submonoid R) (hS : IsCentralSubmonoid S)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (p p' : (A →ₗ[R] B) × centralSubmonoid S) (hpp' : p ≈ p') :
    letI := centralOreSet S hS
    comparisonPair S hS p = comparisonPair S hS p' := by
  let _ := centralOreSet S hS
  rcases p with ⟨f, d⟩
  rcases p' with ⟨g, e⟩
  change ∃ u : centralSubmonoid S, u • e • f = u • d • g at hpp'
  rcases hpp' with ⟨u, hu⟩
  apply LinearMap.ext
  intro x
  induction x using OreLocalization.ind with | _ a t => ?_
  simp only [comparisonPair, localizedLinearMapFraction_oreDiv]
  apply OreLocalization.oreDiv_eq_iff.mpr
  let U : S := toCentralDenom S u
  let D : S := toCentralDenom S d
  let E : S := toCentralDenom S e
  refine ⟨U * D, (U : R) * E, ?_, ?_⟩
  · have heval := congrArg (fun k : A →ₗ[R] B => k a) hu
    simp only [smul_smul] at heval
    change ((U : R) * E) • f a = (U * D : S) • g a at heval
    simpa only [Submonoid.smul_def] using heval.symm
  · simp only [Submonoid.coe_mul]
    calc
      (U : R) * D * (E * t) = U * (D * E) * t := by simp only [mul_assoc]
      _ = U * (E * D) * t := by rw [hS D E]
      _ = (U * E) * (D * t) := by simp only [mul_assoc]

/-- Weibel's comparison map
`S⁻¹ Hom_R(A,B) → Hom_{S⁻¹R}(S⁻¹A,S⁻¹B)` for a central multiplicative set in an associative
ring. -/
noncomputable def centralHomLocalizationComparison {R : Type u} [Ring R]
    (S : Submonoid R) (hS : IsCentralSubmonoid S)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B] :
    letI := centralOreSet S hS
    CentralLocalizedHom S A B →+ (A[S⁻¹] →ₗ[R[S⁻¹]] B[S⁻¹]) := by
  let _ := centralOreSet S hS
  refine
    { toFun := fun x => LocalizedModule.liftOn x (comparisonPair S hS) (comparisonPair_wd S hS)
      map_zero' := ?_
      map_add' := ?_ }
  · rw [← LocalizedModule.zero_mk (S := centralSubmonoid S) (M := A →ₗ[R] B) 1,
      LocalizedModule.liftOn_mk]
    apply LinearMap.ext
    intro x
    induction x using OreLocalization.ind with | _ a t => ?_
    simp only [comparisonPair, localizedLinearMapFraction_oreDiv, LinearMap.zero_apply]
    exact OreLocalization.zero_oreDiv _
  · intro x y
    induction x, y using LocalizedModule.induction_on₂ with | _ f g d e => ?_
    rw [LocalizedModule.mk_add_mk]
    simp only [LocalizedModule.liftOn_mk]
    apply LinearMap.ext
    intro x
    induction x using OreLocalization.ind with | _ a t => ?_
    simp only [comparisonPair, localizedLinearMapFraction_oreDiv, LinearMap.add_apply]
    let D : S := toCentralDenom S d
    let E : S := toCentralDenom S e
    change ((e • f + d • g) a) /ₒ (toCentralDenom S (d * e) * t) =
      f a /ₒ (D * t) + g a /ₒ (E * t)
    have hcomm : (E : R) * ((D : R) * t) = (D : R) * ((E : R) * t) := by
      calc
        (E : R) * (D * t) = (E * D) * t := (mul_assoc _ _ _).symm
        _ = (D * E) * t := by rw [hS E D]
        _ = D * (E * t) := mul_assoc _ _ _
    rw [OreLocalization.oreDiv_add_char (r := f a) (r' := g a) (D * t) (E * t)
      (D : R) E hcomm]
    simp only [LinearMap.add_apply, Submonoid.smul_def]
    change ((E : R) • f a + (D : R) • g a) /ₒ (toCentralDenom S (d * e) * t) =
      ((E : R) • f a + (D : R) • g a) /ₒ (E * (D * t))
    have hden : toCentralDenom S (d * e) * t = E * (D * t) := by
      apply Subtype.ext
      change ((D : R) * E) * t = E * (D * t)
      rw [← hS E D, mul_assoc]
    rw [hden]

@[simp]
theorem centralHomLocalizationComparison_mk {R : Type u} [Ring R]
    (S : Submonoid R) (hS : IsCentralSubmonoid S)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (d : centralSubmonoid S) :
    letI := centralOreSet S hS
    centralHomLocalizationComparison S hS (A := A) (B := B) (LocalizedModule.mk f d) =
      localizedLinearMapFraction S hS f (toCentralDenom S d) := by
  let _ := centralOreSet S hS
  change LocalizedModule.liftOn (LocalizedModule.mk f d) (comparisonPair S hS)
      (comparisonPair_wd S hS) = localizedLinearMapFraction S hS f (toCentralDenom S d)
  rw [LocalizedModule.liftOn_mk]
  rfl

/-- The defining fraction formula `(f/s)(a/t)=f(a)/(st)` for the localization comparison. -/
theorem centralHomLocalizationComparison_fraction {R : Type u} [Ring R]
    (S : Submonoid R) (hS : IsCentralSubmonoid S)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (s t : S) (a : A) :
    letI := centralOreSet S hS
    centralHomLocalizationComparison S hS (A := A) (B := B)
        (LocalizedModule.mk f (ofCentralDenom S hS s)) (a /ₒ t) =
      f a /ₒ (s * t) := by
  let _ := centralOreSet S hS
  rw [centralHomLocalizationComparison_mk, localizedLinearMapFraction_oreDiv]
  rfl

end LeanCategories.Homological
