/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

/-!
# TorTorsionClass: the torsion-class route to Tor of a torsion module

Card `E-HAT-3.A-6` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/TorTorsionClass.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/TorTorsionClass.lean`.
-/

/-
Copyright (c) 2026 The Qual Corpus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tor of a torsion module is torsion: the torsion-class route

`E-HAT-3.A-6` asks one to show that `Tor(A, B)` is always a torsion group.  The card's solution
proves this by writing `A` as a directed union of finitely generated subgroups and computing each
stage.  This file instead proves the same statement by the Serre-class argument: the torsion
abelian groups are closed under subobjects and quotients, and a left derived functor whose values
on projectives land in such a class takes all its values there.  The route needs no finitely
generated stage, no free resolution and no flatness.

## Provenance (port)

The two categorical lemmas and the tensor/torsion lemmas below are **ported**, not new.  They are
copied from the Tau Ceti project at commit `67e852853c5192ec69775bb7ef417fc199e4190e`
(`main`, Apache-2.0), with hypotheses and proof terms unchanged except where noted:

* `CategoryTheory.ObjectProperty.prop_homology`,
  `CategoryTheory.ObjectProperty.prop_leftDerived_obj`
  — `TauCeti/CategoryTheory/ObjectProperty/Homology.lean`.
* `AddCommGrpCat.isTorsion`, `AddCommGrpCat.prop_isTorsion_iff`, and the
  `IsClosedUnderSubobjects`/`IsClosedUnderQuotients` instances
  — `TauCeti/AlgebraicTopology/SerreClass/Torsion.lean` (only the two closure instances are
    ported; the `IsSerreClass` instance and the `isKilledBySomePower` refinement are not needed).
* `isAddTorsion_tensorProduct_left` — `TauCeti/LinearAlgebra/TensorProduct/Torsion.lean`.
* `isAddTorsion_Tor_left` — `TauCeti/AlgebraicTopology/SerreClass/TensorTor.lean`.

None of these files is a Lake dependency of this repository, so the reuse route here is
"copy or port the reference implementation, citing repository, file and commit" rather than an
import.

## What this does and does not cover

**This file is a supplement, not a card obligation.** `E-HAT-3.A-6` requires a correct sourced
solution; the fact below is not a *corrected* claim on that card, so `certify-card-corrections`
does not reach it, and the card is discharged by citing the upstream theorem with its hypotheses
(see `proofs/README.md` §7c). The file is kept because it is committed and it compiles.

It proves the torsion case of the first half of `E-HAT-3.A-6`: if the module `M` underlying the
first variable **is** torsion, then `Tor_n(M, N)` is a torsion group, for every `N` and over every
commutative ring.  That is not the card's statement, which quantifies over all `A`: the
remaining step is the reduction `Tor_n(A, B) ≅ Tor_n(T(A), B)` (via flatness of `A ⧸ T(A)` and the
long exact sequence of `Tor`), which is **not** scheduled work — see §7c.

It also does **not** prove the second half of the card (that `Tor(A, B)` contains an element of
order `n` iff both `A` and `B` do); that remains a separate obligation, and
`proofs/cards/TorTorsion.lean` certifies only its group-theoretic core.

The result is stated for Mathlib's `CategoryTheory.Tor`, which is the left derived functor of
`X ⊗ -`; nothing here identifies it with `Tor'` (the left derived functor of `- ⊗ Y`), and no such
identification is needed for this statement.
-/


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

universe u v u' v'

/-! ## A property closed under subobjects and quotients passes to homology and to left derived
functors -/

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]

/-- A property closed under subobjects and quotients passes from a term of a complex to homology
in the same degree, whenever that homology exists. -/
lemma prop_homology [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : ι) [K.HasHomology i] (h : P (K.X i)) :
    P (K.homology i) :=
  P.prop_of_epi (K.homologyπ i) (P.prop_of_mono (K.iCycles i) h)

variable [Abelian C]

/-- If an additive functor sends every projective object into a class closed under subobjects and
quotients, all its left derived functors take values in that class. -/
lemma prop_leftDerived_obj {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasProjectiveResolutions D] (F : D ⥤ C) [F.Additive]
    (hF : ∀ (Y : D) [Projective Y], P (F.obj Y)) (X : D) (n : ℕ) :
    P ((F.leftDerived n).obj X) := by
  let Q := projectiveResolution X
  exact P.prop_of_iso (Q.isoLeftDerivedObj F n).symm
    (P.prop_homology ((F.mapHomologicalComplex _).obj Q.complex) n (hF _))

end CategoryTheory.ObjectProperty

/-! ## The torsion abelian groups, as an object property -/

namespace AddCommGrpCat

/-- The torsion abelian groups, in which every element has finite order. -/
def isTorsion : ObjectProperty AddCommGrpCat.{u} := fun M => IsAddTorsion M

/-- An abelian group belongs to `isTorsion` exactly when it is a torsion group. -/
lemma prop_isTorsion_iff (M : AddCommGrpCat.{u}) : isTorsion M ↔ IsAddTorsion M := Iff.rfl

instance : isTorsion.{u}.IsClosedUnderSubobjects where
  prop_of_mono {M N} f _ hN := by
    rw [AddCommGrpCat.mono_iff_injective] at ‹Mono f›
    intro x
    obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hN (f x))
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    apply ‹Function.Injective ⇑f›
    show ⇑f (n • x) = ⇑f 0
    rw [map_nsmul, hx, map_zero]

instance : isTorsion.{u}.IsClosedUnderQuotients where
  prop_of_epi {M N} f _ hM := by
    rw [AddCommGrpCat.epi_iff_surjective] at ‹Epi f›
    exact IsAddTorsion.of_surjective ‹Function.Surjective ⇑f› hM

end AddCommGrpCat

/-! ## Tensoring a torsion module is torsion -/

section TensorTorsion

variable {R : Type*} [CommSemiring R]

/-- Tensoring a torsion commutative additive monoid on the left with any commutative additive
monoid gives a torsion monoid.  No flatness and no finite generation is required. -/
theorem isAddTorsion_tensorProduct_left {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] (h : IsAddTorsion A) : IsAddTorsion (A ⊗[R] B) := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨1, one_pos, by simp⟩
  | tmul x y => exact ((TensorProduct.mk R A B).flip y).toAddMonoidHom.isOfFinAddOrder (h x)
  | add x y ihx ihy => exact ihx.add ihy

end TensorTorsion

/-! ## Tor of a torsion module is torsion -/

section TorTorsion

variable {R : Type u} [CommRing R]

/-- **Every `Tor` group of a module whose underlying abelian group is torsion is torsion**, the
second variable being arbitrary.  Over any commutative ring. -/
theorem isAddTorsion_Tor_left {M N : ModuleCat.{u} R} (h : IsAddTorsion M) (n : ℕ) :
    IsAddTorsion (((Tor (ModuleCat.{u} R) n).obj M).obj N) := by
  let P := AddCommGrpCat.isTorsion.inverseImage (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
  apply (AddCommGrpCat.prop_isTorsion_iff (AddCommGrpCat.of _)).1
  exact P.prop_leftDerived_obj ((tensoringLeft (ModuleCat.{u} R)).obj M)
    (fun Y _ => (AddCommGrpCat.prop_isTorsion_iff _).2
      (isAddTorsion_tensorProduct_left (R := R) h)) N n

/-- The card's form, over `ℤ`: for abelian groups `A`, `B` with `A` torsion, `Tor(A, B)` is a
torsion group. -/
theorem isAddTorsion_tor_int {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (h : IsAddTorsion A) (n : ℕ) :
    IsAddTorsion (((Tor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ A)).obj
      (ModuleCat.of ℤ B)) :=
  isAddTorsion_Tor_left (h := h) n

end TorTorsion
