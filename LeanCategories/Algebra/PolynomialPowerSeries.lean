/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.StandardConstructions
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u

/-! ### Polynomial rings over varying commutative rings -/

/-- The discrete fiber of polynomial elements over a commutative ring. -/
abbrev PolynomialFiber (R : CommRingCat.{u}) := Discrete (Polynomial R)

/-- The polynomial-element family over `CommRingCat`, using `Polynomial.map`. -/
def polynomialFamily : CommRingCat.{u} ⥤ Cat.{u, u + 1} where
  obj R := Cat.of (PolynomialFiber R)
  map {R S} f :=
    (Discrete.functor (fun p : PolynomialFiber R =>
      (⟨p.as.map f.hom⟩ : PolynomialFiber S))).toCatHom
  map_id R := by
    apply Cat.Hom.ext
    apply Functor.ext
    · intro p
      exact congrArg Discrete.mk (Polynomial.map_id p.as)
    · intro p q h
      apply Subsingleton.elim
  map_comp f g := by
    apply Cat.Hom.ext
    apply Functor.ext
    · intro p
      apply congrArg Discrete.mk
      apply Polynomial.ext
      intro n
      simp [Polynomial.coeff_map]
    · intro p q h
      apply Subsingleton.elim

/-- The total category of polynomial elements over varying commutative rings. -/
abbrev PolynomialTotalCat := Grothendieck polynomialFamily

/-- Projection from polynomial elements to their coefficient ring. -/
abbrev polynomialBaseProjection : PolynomialTotalCat.{u} ⥤ CommRingCat.{u} :=
  Grothendieck.forget polynomialFamily

/-- Inclusion of the polynomial fiber over a fixed commutative ring. -/
abbrev polynomialFixedFiber (R : CommRingCat.{u}) :
    PolynomialFiber R ⥤ PolynomialTotalCat :=
  Grothendieck.ι polynomialFamily R

/-- The polynomial base-change functor induced by a ring homomorphism. -/
abbrev polynomialBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PolynomialFiber R ⥤ PolynomialFiber S :=
  (polynomialFamily.map f).toFunctor

/-- The canonical base-change object associated to a polynomial and a ring map. -/
abbrev polynomialBaseChangeObject {R S : CommRingCat.{u}}
    (p : PolynomialFiber R) (f : R ⟶ S) : PolynomialFiber S :=
  (polynomialBaseChange f).obj p

/-- The canonical base-change morphism in the total polynomial category. -/
abbrev polynomialBaseChangeHom (X : PolynomialTotalCat.{u})
    {S : CommRingCat.{u}} (f : X.base ⟶ S) : X ⟶ Grothendieck.transport X f :=
  Grothendieck.toTransport X f

/-! ### Polynomial differentiation -/

/-- Formal differentiation as a natural transformation of polynomial fibers.

This is the categorical form of `Polynomial.derivative_map`: differentiation
commutes with coefficient-ring maps. -/
def polynomialDerivativeNatTrans : polynomialFamily ⟶ polynomialFamily where
  app R :=
    (Discrete.functor (fun p : PolynomialFiber R =>
      (⟨Polynomial.derivative p.as⟩ : PolynomialFiber R))).toCatHom
  naturality := by
    intro R S f
    apply Cat.Hom.ext
    apply Functor.ext
    · intro p
      apply congrArg Discrete.mk
      exact (Polynomial.derivative_map p.as f.hom).symm
    · intro p q h
      apply Subsingleton.elim

/-- The induced differentiation functor on the total polynomial category. -/
abbrev polynomialDerivativeFunctor : PolynomialTotalCat.{u} ⥤ PolynomialTotalCat.{u} :=
  Grothendieck.map polynomialDerivativeNatTrans

/-! ### Formal power-series rings over varying commutative rings -/

/-- The discrete fiber of power-series elements over a commutative ring. -/
abbrev PowerSeriesFiber (R : CommRingCat.{u}) := Discrete (PowerSeries R)

/-- The power-series-element family over `CommRingCat`, using `PowerSeries.map`. -/
def powerSeriesFamily : CommRingCat.{u} ⥤ Cat.{u, u + 1} where
  obj R := Cat.of (PowerSeriesFiber R)
  map {R S} f :=
    (Discrete.functor (fun p : PowerSeriesFiber R =>
      (⟨PowerSeries.map f.hom p.as⟩ : PowerSeriesFiber S))).toCatHom
  map_id R := by
    apply Cat.Hom.ext
    apply Functor.ext
    · intro p
      exact congrArg Discrete.mk (by
        simpa using congrArg (fun h : PowerSeries R →+* PowerSeries R => h p.as)
          (PowerSeries.map_id (R := R)))
    · intro p q h
      apply Subsingleton.elim
  map_comp f g := by
    apply Cat.Hom.ext
    apply Functor.ext
    · intro p
      exact congrArg Discrete.mk (by
        simpa using congrArg (fun h : PowerSeries R →+* PowerSeries _ => h p.as)
          (PowerSeries.map_comp f.hom g.hom))
    · intro p q h
      apply Subsingleton.elim

/-- The total category of power-series elements over varying commutative rings. -/
abbrev PowerSeriesTotalCat := Grothendieck powerSeriesFamily

/-- Projection from power-series elements to their coefficient ring. -/
abbrev powerSeriesBaseProjection : PowerSeriesTotalCat.{u} ⥤ CommRingCat.{u} :=
  Grothendieck.forget powerSeriesFamily

/-- Inclusion of the power-series fiber over a fixed commutative ring. -/
abbrev powerSeriesFixedFiber (R : CommRingCat.{u}) :
    PowerSeriesFiber R ⥤ PowerSeriesTotalCat :=
  Grothendieck.ι powerSeriesFamily R

/-- The power-series base-change functor induced by a ring homomorphism. -/
abbrev powerSeriesBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PowerSeriesFiber R ⥤ PowerSeriesFiber S :=
  (powerSeriesFamily.map f).toFunctor

/-- The canonical base-change object associated to a power series and a ring map. -/
abbrev powerSeriesBaseChangeObject {R S : CommRingCat.{u}}
    (p : PowerSeriesFiber R) (f : R ⟶ S) : PowerSeriesFiber S :=
  (powerSeriesBaseChange f).obj p

/-- The canonical base-change morphism in the total power-series category. -/
abbrev powerSeriesBaseChangeHom (X : PowerSeriesTotalCat.{u})
    {S : CommRingCat.{u}} (f : X.base ⟶ S) : X ⟶ Grothendieck.transport X f :=
  Grothendieck.toTransport X f

end LeanCategories.Algebra
