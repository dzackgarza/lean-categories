/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.StandardConstructions
public import LeanCategories.ForMathlib.GrothendieckCocartesian
public import Mathlib.Algebra.Category.Ring.Basic
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
noncomputable def polynomialFamily : CommRingCat.{u} ⥤ Cat.{u, u} where
  obj R := Cat.of (PolynomialFiber R)
  map {R S} f :=
    (Discrete.functor (fun p : Polynomial R =>
      (⟨p.map f.hom⟩ : PolynomialFiber S))).toCatHom
  map_id R := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro p Y f
      rcases p with ⟨p⟩
      rcases Y with ⟨Y⟩
      rcases f with ⟨⟨h⟩⟩
      cases h
      cat_disch
    · intro p
      exact congrArg Discrete.mk (Polynomial.map_id (p := p.as))
  map_comp f g := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro p Y f
      rcases p with ⟨p⟩
      rcases Y with ⟨Y⟩
      rcases f with ⟨⟨h⟩⟩
      cases h
      cat_disch
    · intro p
      apply congrArg Discrete.mk
      apply Polynomial.ext
      intro n
      simp [Polynomial.coeff_map]

/-- The total category of polynomial elements over varying commutative rings. -/
noncomputable abbrev PolynomialTotalCat := Grothendieck polynomialFamily

/-- Projection from polynomial elements to their coefficient ring. -/
noncomputable abbrev polynomialBaseProjection : PolynomialTotalCat.{u} ⥤ CommRingCat.{u} :=
  Grothendieck.forget polynomialFamily

/-- Inclusion of the polynomial fiber over a fixed commutative ring. -/
noncomputable abbrev polynomialFixedFiber (R : CommRingCat.{u}) :
    PolynomialFiber R ⥤ PolynomialTotalCat :=
  Grothendieck.ι polynomialFamily R

/-- The polynomial base-change functor induced by a ring homomorphism. -/
noncomputable abbrev polynomialBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PolynomialFiber R ⥤ PolynomialFiber S :=
  (polynomialFamily.map f).toFunctor

/-- The canonical base-change object associated to a polynomial and a ring map. -/
noncomputable abbrev polynomialBaseChangeObject {R S : CommRingCat.{u}}
    (p : PolynomialFiber R) (f : R ⟶ S) : PolynomialFiber S :=
  (polynomialBaseChange f).obj p

/-- The canonical base-change morphism in the total polynomial category. -/
noncomputable abbrev polynomialBaseChangeHom (X : PolynomialTotalCat.{u})
    {S : CommRingCat.{u}} (f : X.base ⟶ S) : X ⟶ Grothendieck.transport X f :=
  Grothendieck.toTransport X f

/-- Polynomial base change is the canonical strongly co-Cartesian Grothendieck lift. -/
noncomputable instance polynomialBaseChangeHom_isStronglyCocartesian
    (X : PolynomialTotalCat.{u}) {S : CommRingCat.{u}} (f : X.base ⟶ S) :
    Functor.IsStronglyCocartesian polynomialBaseProjection f (polynomialBaseChangeHom X f) :=
  Grothendieck.isStronglyCocartesian_cocartesianLift X.fiber f

/-! ### Polynomial differentiation -/

/-- Formal differentiation as a natural transformation of polynomial fibers.

This is the categorical form of `Polynomial.derivative_map`: differentiation
commutes with coefficient-ring maps. -/
noncomputable def polynomialDerivativeNatTrans : polynomialFamily ⟶ polynomialFamily where
  app R :=
    (Discrete.functor (fun p : Polynomial R =>
      (⟨Polynomial.derivative p⟩ : PolynomialFiber R))).toCatHom
  naturality := by
    intro R S f
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro p Y f
      rcases p with ⟨p⟩
      rcases Y with ⟨Y⟩
      rcases f with ⟨⟨h⟩⟩
      cases h
      cat_disch
    · intro p
      apply congrArg Discrete.mk
      exact Polynomial.derivative_map p.as f.hom

/-- The induced differentiation functor on the total polynomial category. -/
noncomputable abbrev polynomialDerivativeFunctor : PolynomialTotalCat.{u} ⥤ PolynomialTotalCat.{u} :=
  Grothendieck.map polynomialDerivativeNatTrans

/-! ### Formal power-series rings over varying commutative rings -/

/-- The discrete fiber of power-series elements over a commutative ring. -/
abbrev PowerSeriesFiber (R : CommRingCat.{u}) := Discrete (PowerSeries R)

/-- The power-series-element family over `CommRingCat`, using `PowerSeries.map`. -/
noncomputable def powerSeriesFamily : CommRingCat.{u} ⥤ Cat.{u, u} where
  obj R := Cat.of (PowerSeriesFiber R)
  map {R S} f :=
    (Discrete.functor (fun p : PowerSeries R =>
      (⟨PowerSeries.map f.hom p⟩ : PowerSeriesFiber S))).toCatHom
  map_id R := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro p Y f
      rcases p with ⟨p⟩
      rcases Y with ⟨Y⟩
      rcases f with ⟨⟨h⟩⟩
      cases h
      cat_disch
    · intro p
      exact congrArg Discrete.mk (by
        simpa using congr_fun (PowerSeries.map_id (R := R)) p.as)
  map_comp {R S T} f g := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro p Y f
      rcases p with ⟨p⟩
      rcases Y with ⟨Y⟩
      rcases f with ⟨⟨h⟩⟩
      cases h
      cat_disch
    · intro p
      exact congrArg Discrete.mk (by
        simpa using congrArg (fun h : PowerSeries R →+* PowerSeries T => h p.as)
          (PowerSeries.map_comp f.hom g.hom))

/-- The total category of power-series elements over varying commutative rings. -/
noncomputable abbrev PowerSeriesTotalCat := Grothendieck powerSeriesFamily

/-- Projection from power-series elements to their coefficient ring. -/
noncomputable abbrev powerSeriesBaseProjection : PowerSeriesTotalCat.{u} ⥤ CommRingCat.{u} :=
  Grothendieck.forget powerSeriesFamily

/-- Inclusion of the power-series fiber over a fixed commutative ring. -/
noncomputable abbrev powerSeriesFixedFiber (R : CommRingCat.{u}) :
    PowerSeriesFiber R ⥤ PowerSeriesTotalCat :=
  Grothendieck.ι powerSeriesFamily R

/-- The power-series base-change functor induced by a ring homomorphism. -/
noncomputable abbrev powerSeriesBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PowerSeriesFiber R ⥤ PowerSeriesFiber S :=
  (powerSeriesFamily.map f).toFunctor

/-- The canonical base-change object associated to a power series and a ring map. -/
noncomputable abbrev powerSeriesBaseChangeObject {R S : CommRingCat.{u}}
    (p : PowerSeriesFiber R) (f : R ⟶ S) : PowerSeriesFiber S :=
  (powerSeriesBaseChange f).obj p

/-- The canonical base-change morphism in the total power-series category. -/
noncomputable abbrev powerSeriesBaseChangeHom (X : PowerSeriesTotalCat.{u})
    {S : CommRingCat.{u}} (f : X.base ⟶ S) : X ⟶ Grothendieck.transport X f :=
  Grothendieck.toTransport X f

/-- Power-series base change is the canonical strongly co-Cartesian Grothendieck lift. -/
noncomputable instance powerSeriesBaseChangeHom_isStronglyCocartesian
    (X : PowerSeriesTotalCat.{u}) {S : CommRingCat.{u}} (f : X.base ⟶ S) :
    Functor.IsStronglyCocartesian powerSeriesBaseProjection f (powerSeriesBaseChangeHom X f) :=
  Grothendieck.isStronglyCocartesian_cocartesianLift X.fiber f

end LeanCategories.Algebra
