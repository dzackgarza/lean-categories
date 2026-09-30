/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Fixed
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

/-!
# The monoid of isometry classes of quadratic modules

The isomorphism classes of `QuadModuleCat R W` form a commutative monoid under the orthogonal
sum `(M, q) ⊥ (N, q') = (M × N, q ⊕ q')` (`QuadraticMap.prod`), with unit the zero module.
Isomorphisms in `QuadModuleCat R W` are exactly isometric linear equivalences
(`isIsomorphic_iff_equivalent`). The classes with finite free carrier form a submonoid
`finiteFreeClasses`; at `R = W = ℤ_p` it is Nikulin's semigroup `qu(ℤ_p)` (Nikulin, *Integral
symmetric bilinear forms and some of their applications*, §1.8).

Provenance: migrated from `dzackgarza/research`,
`computations/scripts/sterk-enriques-cusps/lean/Atoms.lean` (section `PadicSemigroup`, Sterk
graph node Pa1). There `qu(ℤ_p)` was modelled by forms on the chosen modules `Fin n → ℤ_[p]`,
with the orthogonal sum transported along `finSumFinEquiv`. Here the base ring and value module
are arbitrary, the carrier is any module in the universe of `R`, and the class set is the
quotient of `QuadModuleCat R W` by isomorphism, so the choice of representatives is not part of
the definition.

LC-12. *Needed*: `qu(R)` as the commutative monoid of isometry classes. *Searched*: the
formalization corpus and Mathlib for a symmetric monoidal structure on quadratic modules by
orthogonal sum; Mathlib has only the isometries `QuadraticMap.IsometryEquiv.prod`/`prodComm` and
the `Skeleton` monoid of a monoidal category (`CategoryTheory.Monoidal.Skeleton`). *Did instead*:
the monoid on isomorphism classes directly, from explicit isometric equivalences. *Optimal*:
the symmetric monoidal structure `⊥` on `QuadModuleCat R W`, whose skeleton monoid this is.
*Tracked*: TODO(LC-12) below and COMPLAINTS ("Orthogonal sum monoidal structure").
-/

open CategoryTheory

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]

namespace QuadModuleCat

theorem hom_ext {Q P : QuadModuleCat R W} {f g : Q ⟶ P}
    (h : underlyingMap f = underlyingMap g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply Subtype.ext
  apply Quiver.Hom.unop_inj
  exact ModuleCat.hom_ext h

@[simp]
theorem underlyingMap_comp {Q P S : QuadModuleCat R W} (f : Q ⟶ P) (g : P ⟶ S) :
    underlyingMap (f ≫ g) = underlyingMap g ∘ₗ underlyingMap f :=
  rfl

@[simp]
theorem underlyingMap_id (Q : QuadModuleCat R W) : underlyingMap (𝟙 Q) = LinearMap.id :=
  rfl

/-- An isometric linear equivalence is an isomorphism of quadratic modules. -/
def isoOfIsometryEquiv {Q P : QuadModuleCat R W} (e : Q.form.IsometryEquiv P.form) : Q ≅ P where
  hom := homMk e.toLinearEquiv.toLinearMap e.map_app
  inv := homMk e.symm.toLinearEquiv.toLinearMap e.symm.map_app
  hom_inv_id := hom_ext (LinearMap.ext fun x ↦ e.symm_apply_apply x)
  inv_hom_id := hom_ext (LinearMap.ext fun x ↦ e.apply_symm_apply x)

/-- An isomorphism of quadratic modules is an isometric linear equivalence. -/
def isometryEquivOfIso {Q P : QuadModuleCat R W} (e : Q ≅ P) : Q.form.IsometryEquiv P.form where
  toLinearEquiv := LinearEquiv.ofLinearMap (underlyingMap e.hom) (underlyingMap e.inv)
    (congr_arg underlyingMap e.inv_hom_id) (congr_arg underlyingMap e.hom_inv_id)
  map_app' := map_form e.hom

theorem isIsomorphic_iff_equivalent {Q P : QuadModuleCat R W} :
    IsIsomorphic Q P ↔ Q.form.Equivalent P.form :=
  ⟨fun ⟨e⟩ ↦ ⟨isometryEquivOfIso e⟩, fun ⟨e⟩ ↦ ⟨isoOfIsometryEquiv e⟩⟩

/-- The orthogonal sum of quadratic modules. -/
def orthogonalSum (Q P : QuadModuleCat R W) : QuadModuleCat R W :=
  ofQuadraticMap (Q.form.prod P.form)

/-- The zero quadratic module. -/
def zero : QuadModuleCat R W :=
  ofQuadraticMap (0 : QuadraticMap R PUnit.{u + 1} W)

/-- Associativity of the orthogonal sum. -/
def orthogonalSumAssoc (Q P S : QuadModuleCat R W) :
    (orthogonalSum (orthogonalSum Q P) S).form.IsometryEquiv
      (orthogonalSum Q (orthogonalSum P S)).form where
  toLinearEquiv := LinearEquiv.prodAssoc R Q.carrier P.carrier S.carrier
  map_app' _ := (add_assoc _ _ _).symm

/-- The zero module is a left unit for the orthogonal sum. -/
def orthogonalSumZero (Q : QuadModuleCat R W) :
    (orthogonalSum zero Q).form.IsometryEquiv Q.form where
  toLinearEquiv :=
    { toFun := Prod.snd
      invFun := fun x ↦ (PUnit.unit, x)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  map_app' _ := (zero_add _).symm

end QuadModuleCat

open QuadModuleCat

/-- Isometry classes of `W`-valued quadratic modules over `R`. -/
abbrev IsometryClass (R W : Type u) [CommRing R] [AddCommGroup W] [Module R W] : Type (u + 1) :=
  Quotient (isIsomorphicSetoid (QuadModuleCat R W))

namespace IsometryClass

/-- The class of a quadratic module. -/
def mk (Q : QuadModuleCat R W) : IsometryClass R W := Quotient.mk _ Q

theorem mk_eq_mk_iff {Q P : QuadModuleCat R W} : mk Q = mk P ↔ Q.form.Equivalent P.form :=
  Quotient.eq.trans isIsomorphic_iff_equivalent

instance : Zero (IsometryClass R W) := ⟨mk zero⟩

instance : Add (IsometryClass R W) where
  add := Quotient.map₂ orthogonalSum fun _ _ h₁ _ _ h₂ ↦
    isIsomorphic_iff_equivalent.mpr
      ((isIsomorphic_iff_equivalent.mp h₁).prod (isIsomorphic_iff_equivalent.mp h₂))

@[simp]
theorem mk_add_mk (Q P : QuadModuleCat R W) : mk Q + mk P = mk (orthogonalSum Q P) :=
  rfl

@[simp]
theorem zero_def : (0 : IsometryClass R W) = mk zero :=
  rfl

instance : AddCommMonoid (IsometryClass R W) where
  add_assoc := by
    rintro ⟨Q⟩ ⟨P⟩ ⟨S⟩
    exact mk_eq_mk_iff.mpr ⟨orthogonalSumAssoc Q P S⟩
  zero_add := by
    rintro ⟨Q⟩
    exact mk_eq_mk_iff.mpr ⟨orthogonalSumZero Q⟩
  add_zero := by
    rintro ⟨Q⟩
    exact mk_eq_mk_iff.mpr
      ⟨(QuadraticMap.IsometryEquiv.prodComm Q.form zero.form).trans (orthogonalSumZero Q)⟩
  add_comm := by
    rintro ⟨Q⟩ ⟨P⟩
    exact mk_eq_mk_iff.mpr ⟨QuadraticMap.IsometryEquiv.prodComm Q.form P.form⟩
  nsmul := nsmulRec

/-- The classes represented by a quadratic module on a finite free module. At `R = W = ℤ_p`
this is Nikulin's `qu(ℤ_p)`. -/
def finiteFreeClasses : AddSubmonoid (IsometryClass R W) where
  carrier := {c | ∃ Q : QuadModuleCat R W, mk Q = c ∧ Module.Free R Q.carrier ∧
    Module.Finite R Q.carrier}
  zero_mem' := ⟨zero, rfl, inferInstanceAs (Module.Free R PUnit),
    inferInstanceAs (Module.Finite R PUnit)⟩
  add_mem' := by
    rintro _ _ ⟨Q, rfl, hQ, hQ'⟩ ⟨P, rfl, hP, hP'⟩
    exact ⟨orthogonalSum Q P, rfl, inferInstanceAs (Module.Free R (Q.carrier × P.carrier)),
      inferInstanceAs (Module.Finite R (Q.carrier × P.carrier))⟩

end IsometryClass

-- TODO(LC-12): the symmetric monoidal structure `⊥` on `QuadModuleCat R W`, with
-- `IsometryClass R W` its skeleton monoid (`CategoryTheory.Monoidal.Skeleton`).

end LeanCategories.Modules.Quadratic.Valued
