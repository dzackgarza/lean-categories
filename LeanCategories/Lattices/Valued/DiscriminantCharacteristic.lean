/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantAction

/-!
# The characteristic class of a `2`-elementary quadratic form (#115)

Let `q : A → Frac(R)/2R` be a quadratic form whose polar form is twice an `Frac(R)/R`-valued
pairing `b`: for every even lattice `L` the quadratic discriminant form `q_A` and the
discriminant pairing `b_A` satisfy `q_A(x+y) - q_A(x) - q_A(y) = 2·b_A(x,y)`
(`evenDiscriminantQuadraticMap_polar`). When `A` is killed by `2`, the reduction
`x ↦ q(x) mod 1` is additive: the polar term `2·b(x,y) = b(2x,y)` vanishes on a `2`-elementary
group.

A class `w` whose pairing against every `x` reproduces the *linear* form `q mod 1` is the
characteristic class of the quadratic form. It exists and is unique when the pairing is perfect,
and every isometry of the pair `(q,b)` fixes it. At `T_Co` (#115) it is the class `[h/2]`, and
the invariance statement is that `O(T_Co)` fixes `[h/2]`.

Everything here is proved for an arbitrary input: an arbitrary quadratic map with its polar
pairing (the abstract statements), and an arbitrary even lattice whose discriminant group is
`2`-elementary (the existence and invariance statements). The lattice `T_Co` enters only in
`CobleLattice`, where these general facts are applied.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

-- Pin the quotient module instance of the fraction-ring quotients and of the discriminant
-- carrier, so that types mentioning a quotient are read with one instance list throughout.
attribute [local instance 10000] Submodule.Quotient.module

universe u

section ModOne

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Reduction of `Frac(R) / 2R` modulo `Frac(R) / R`: the map sending a class modulo `2R` to the
class modulo `R` it determines. For `R = ℤ` this is the map `q ↦ q mod 1`. -/
noncomputable def doubleFractionModOne :
    DoubleFractionValueQuotient R →ₗ[R] FractionValueQuotient R :=
  Submodule.mapQ (LinearMap.range (doubleAlgebraMap R))
    (LinearMap.range (Algebra.linearMap R (FractionRing R))) LinearMap.id (by
      rintro x ⟨r, rfl⟩
      exact ⟨(2 : R) • r, by simp [doubleAlgebraMap, Algebra.smul_def]⟩)

omit [IsDomain R] in
@[simp]
theorem doubleFractionModOne_mk (x : FractionRing R) :
    doubleFractionModOne R (Submodule.Quotient.mk x) = fractionValueProjection R x :=
  rfl

omit [IsDomain R] in
/-- Reducing the double of a class modulo `1` multiplies it by two. -/
theorem doubleFractionModOne_doubleValueMap (x : FractionValueQuotient R) :
    doubleFractionModOne R (doubleValueMap R x) = (2 : R) • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ r =>
      rw [doubleValueMap_mk, doubleFractionModOne_mk]
      have h : fractionValueProjection R (twiceFraction R r) =
          (2 : R) • Submodule.Quotient.mk r := by
        rw [twiceFraction, LinearMap.lsmul_apply, fractionValueProjection, Submodule.mkQ_apply,
          Submodule.Quotient.mk_smul]
      rw [h]

omit [IsDomain R] in
/-- Reducing a class modulo `2R` and then modulo `R` is the same as reducing its
representative modulo `R`: the reduction of a reduced quadratic form is the discriminant
quadratic form itself. -/
@[simp]
theorem doubleFractionModOne_doubleFractionValueProjection (x : FractionRing R) :
    doubleFractionModOne R (doubleFractionValueProjection R x) = fractionValueProjection R x :=
  rfl

end ModOne

/-! ## Additivity of `q mod 1` on a `2`-elementary group -/

section AbstractForm

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The reduction modulo `1` of an `Frac(R)/2R`-valued quadratic form: the function written
`x ↦ q(x) mod 1`. -/
noncomputable def quadraticModOne
    (q : QuadraticMap R M (DoubleFractionValueQuotient R)) :
    M → FractionValueQuotient R :=
  fun x => doubleFractionModOne R (q x)

/-- `IsCharacteristicClassOf q b w` says that pairing with `w` reproduces `q` modulo `1`: the
class of `w` is the characteristic class of the quadratic form `q` for the pairing `b`. -/
def IsCharacteristicClassOf
    (q : QuadraticMap R M (DoubleFractionValueQuotient R))
    (b : LinearMap.BilinMap R M (FractionValueQuotient R)) (w : M) : Prop :=
  ∀ x, b w x = quadraticModOne q x

end AbstractForm

section Abstract

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type u} [AddCommGroup M] [Module R M]

omit [IsDomain R] in
/-- **`x ↦ q(x) mod 1` is additive when the group is killed by `2`.** -/
theorem quadraticModOne_add
    (q : QuadraticMap R M (DoubleFractionValueQuotient R))
    (b : LinearMap.BilinMap R M (FractionValueQuotient R))
    (hpolar : ∀ x y, QuadraticMap.polar q x y = doubleValueMap R (b x y))
    (h2 : ∀ x : M, (2 : R) • x = 0) (x y : M) :
    quadraticModOne q (x + y) = quadraticModOne q x + quadraticModOne q y := by
  have hz : (2 : R) • b x y = 0 := by
    have h1 : b ((2 : R) • x) y = 0 := by rw [h2 x, map_zero]; rfl
    rwa [map_smul, LinearMap.smul_apply] at h1
  have hsum : q (x + y) = q x + q y + doubleValueMap R (b x y) := by
    rw [QuadraticMap.map_add (⇑q) x y, hpolar]
  simp only [quadraticModOne, hsum]
  rw [map_add, map_add, doubleFractionModOne_doubleValueMap, hz, add_zero]

omit [IsDomain R] in
/-- **The characteristic class is unique** under a nondegenerate pairing. -/
theorem isCharacteristicClassOf_unique
    (q : QuadraticMap R M (DoubleFractionValueQuotient R))
    (b : LinearMap.BilinMap R M (FractionValueQuotient R))
    (hsep : ∀ w : M, (∀ x, b w x = 0) → w = 0) {w w' : M}
    (hw : IsCharacteristicClassOf q b w) (hw' : IsCharacteristicClassOf q b w') : w = w' := by
  refine sub_eq_zero.mp (hsep (w - w') fun x => ?_)
  rw [map_sub, LinearMap.sub_apply, hw x, hw' x, sub_self]

omit [IsDomain R] in
/-- **Every isometry of the quadratic form that preserves its polarization fixes the
characteristic class.** -/
theorem isometry_fixes_isCharacteristicClassOf
    (q : QuadraticMap R M (DoubleFractionValueQuotient R))
    (b : LinearMap.BilinMap R M (FractionValueQuotient R))
    (hsep : ∀ w : M, (∀ x, b w x = 0) → w = 0)
    (g : M ≃ₗ[R] M) (hq : ∀ x, q (g x) = q x) (hb : ∀ x y, b (g x) (g y) = b x y)
    {w : M} (hw : IsCharacteristicClassOf q b w) : g w = w := by
  refine sub_eq_zero.mp (hsep (g w - w) fun y => ?_)
  obtain ⟨z, rfl⟩ := g.surjective y
  rw [map_sub, LinearMap.sub_apply, hb, hw (g z), hw z, quadraticModOne, quadraticModOne,
    hq z, sub_self]

end Abstract

/-! ## The characteristic class of an even lattice with `2`-elementary discriminant -/

section Lattice

variable {L : IntegralLatticeCat ℤ}

/-- The discriminant pairing of an even lattice with finite free carrier is bijective: the
discriminant form is perfect. -/
theorem discriminantBilinMap_bijective
    [Module.Free ℤ L.obj.carrier] [Module.Finite ℤ L.obj.carrier]
    (hL : IsFractionFieldPerfect ℤ L) :
    Function.Bijective (discriminantBilinMap ℤ L hL) :=
  (BilinModuleCat.isPerfect_iff_adjoint_bijective_of_isSymmetric _
    (discriminantBilinObject_isSymmetric ℤ L hL)).mp
    (discriminantBilinObject_isPerfect (R := ℤ) L hL)

/-- **The characteristic class of a `2`-elementary discriminant form is unique.**

For an even lattice with `2`-elementary discriminant group, there is at most one class `w` of
`A_L` whose pairing against every class `x` reproduces the reduced quadratic form
`q_A(x) mod 1`; existence is exhibited for `T_Co` in `CobleLattice`. -/
theorem isCharacteristicClassOf_unique'
    [Module.Free ℤ L.obj.carrier] [Module.Finite ℤ L.obj.carrier]
    (hL : IsFractionFieldPerfect ℤ L) (hEven : IsEven L) {w w' : L.obj.defect}
    (hw : IsCharacteristicClassOf (evenDiscriminantQuadraticMap L hL hEven)
      (discriminantBilinMap ℤ L hL) w)
    (hw' : IsCharacteristicClassOf (evenDiscriminantQuadraticMap L hL hEven)
      (discriminantBilinMap ℤ L hL) w') : w = w' := by
  have hbij : Function.Bijective (discriminantBilinMap ℤ L hL) :=
    discriminantBilinMap_bijective (L := L) hL
  exact isCharacteristicClassOf_unique _ _
    (fun v hv => hbij.1 (LinearMap.ext fun x => by
      rw [map_zero, LinearMap.zero_apply]; exact hv x)) hw hw'

/-- **Every isometry of an even lattice with `2`-elementary discriminant fixes its characteristic
class.** -/
theorem actOnDefect_eq_of_isCharacteristicClassOf
    [Module.Free ℤ L.obj.carrier] [Module.Finite ℤ L.obj.carrier]
    (hL : IsFractionFieldPerfect ℤ L) (hEven : IsEven L)
    {w : L.obj.defect}
    (hw : IsCharacteristicClassOf (evenDiscriminantQuadraticMap L hL hEven)
      (discriminantBilinMap ℤ L hL) w)
    (g : OrthogonalGroup L) : OrthogonalGroup.actOnDefect g w = w := by
  have hbij : Function.Bijective (discriminantBilinMap ℤ L hL) :=
    discriminantBilinMap_bijective (L := L) hL
  exact isometry_fixes_isCharacteristicClassOf
    (evenDiscriminantQuadraticMap L hL hEven) (discriminantBilinMap ℤ L hL)
    (fun v hv => hbij.1 (LinearMap.ext fun x => by
      rw [map_zero, LinearMap.zero_apply]; exact hv x))
    (OrthogonalGroup.actOnDefect g)
    (fun x => OrthogonalGroup.evenDiscriminantQuadraticMap_actOnDefect g hL hEven x)
    (fun x y => OrthogonalGroup.discriminantBilinMap_actOnDefect g hL x y) hw

end Lattice

end LeanCategories.Lattices.Valued
