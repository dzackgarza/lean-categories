/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import LeanCategories.AlgebraicGeometry.Modules.GradedAlgebra.Localization
public import LeanCategories.AlgebraicGeometry.ProjectiveSpectrum.BaseChange

/-!
# The relative `Proj` of a graded quasi-coherent algebra

## Provenance and search record (lean-categories#22)

Ported from Tau Ceti's `TauCeti/AlgebraicGeometry/RelativeProj/Basic.lean`, together with the
layers it imports: `AlgebraicGeometry/Modules/GradedAlgebra/{Sections,Localization}.lean` (graded
section rings and their localization on basic opens),
`AlgebraicGeometry/ProjectiveSpectrum/{Basic,BaseChange}.lean` (`Proj.map`, `Proj.toSpecCoeff`,
`Proj.basicOpen` and the base-change square for `Proj`),
`AlgebraicGeometry/{AffineScheme,Modules/AffineGlobalSections,Modules/Quasicoherent/Colimits}.lean`,
`RingTheory/GradedAlgebra/{DirectSum,Homogeneous/Maps,HomogeneousLocalization/Basic,
HomogeneousLocalization/BaseChange}.lean`, `RingTheory/Localization/{TensorProduct,Tower}.lean`,
`Algebra/Category/ModuleCat/Monoidal/GradedRing.lean`,
`Algebra/Module/LocalizedModule/DirectSum.lean`, `Algebra/DirectSum/Internal.lean`,
`CategoryTheory/{EqToHom,GradedObject/MonObj}.lean` (The Tau Ceti contributors, Apache 2.0), commit
`ca32605ff53921fa0689dd312618b7cfaafa7e43`, namespaces renamed `TauCeti` → `LeanCategories`.
Every ported module carries the same provenance line. No statement changed: all of them elaborate
against the Mathlib pin `7692d7fbbf9cad52d465b18742a9838e5d0c84c5` as they stand, and the only
repairs are the exposure changes recorded next.

### Port repairs against this pin

None of the ported statements changed; six declarations gained `@[expose]`, and one private
lemma became public, so that the repository's `checkType` audit accepts the equation lemmas that
Lean generates for them. The audit re-checks each declaration's type from another module, and an
equation lemma for a definition whose body is not exposed fails that check when the statement
needs the body unfolded
(`DirectSum.piSubmodule` in `Algebra/DirectSum/Internal.lean`, needed by
`DirectSum.piSubmoduleEquiv.eq_1`) or when it quotes one of the private proof auxiliaries Lean
hoists out of the body (`CategoryTheory.Mon.mul` and `GradedObject.Monoidal.oneOfDegreeZero` in
`CategoryTheory/GradedObject/MonObj.lean`, `Proj.toSpecCoeff` and `Proj.baseChangeProjection` in
`ProjectiveSpectrum/BaseChange.lean`, `Away.baseChangeMap` in
`RingTheory/GradedAlgebra/HomogeneousLocalization/BaseChange.lean`). Exposure publishes the body,
and with it those auxiliaries; it widens what `rfl` may see, and changes no hypothesis, no
conclusion and no axiom.

### LC-09 search record (2026-11-14)

Formalization-corpus queries, with the hits that decided the route. `content:RelativeProj`
(TauCeti `AlgebraicGeometry/RelativeProj/{Basic,Affine,Map,Proper,TwistingSheaf}.lean`: the whole
construction, the hit ported here); `content:relativeProjToBase` and
`content:gradedSectionsGrading` (TauCeti `RelativeProj/{Map,Basic}.lean`: the same construction
with its functoriality, which is not part of this unit); `content:Proj.isPullback`,
`content:isBaseChange Proj` and `content:Proj gluing` (TauCeti
`ProjectiveSpectrum/BaseChange.lean`, `Descent/Proj.lean`, `Gluing/Pushout.lean`,
`Modules/Gluing.lean`: the base-change square for `Proj` this gluing rests on, ported, and Mathlib's
own `AlgebraicGeometry.RelativeGluing` with `Sites/SmallAffineZariski.lean` as the gluing engine,
reused rather than ported); `content:graded algebra sheaf sections localization` (TauCeti
`RelativeProj/Basic.lean` again); `content:graded quasicoherent` (Mathlib
`Algebra/Category/ModuleCat/Sheaf/Quasicoherent` and `Algebra/GradedMonoid`: the predicate only, no
construction); `content:projectivization graded algebra` (facebookresearch/atlas-lean
`AlgebraicGeometryI/code/PluckerGr24.lean`: the affine exterior-algebra case only).

The Hartshorne ledger already records CBirkbeck/AINTLIB's `relativeProjectiveScheme` as the
standard projective space `Proj O_S[T₀,…,T_d]` (`FC06-C02-U232`), not the general sheaf-relative
`Proj` (`FC06-C02-U231`), and no formalization other than Tau Ceti's was found for the latter.
Mathlib has `AlgebraicGeometry.Proj` and the relative gluing, and neither a relative `Proj` nor the
graded sections ring of a sheaf of graded algebras; what this unit adds over Mathlib is exactly the
assembly below.

## References

* `FOUNDATIONS.md`, Definition 36.6 (`def-relative-proj`): relative `Proj` by gluing the standard
  affine charts. The construction here is the gluing of
  [Stacks Project, Lemma 27.15.4, tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ) over the
  affine opens `U ⊆ X`, and is
  [Stacks Project, Definition 27.16.7, tag 01O0](https://stacks.math.columbia.edu/tag/01O0) once
  identified with the scheme representing the relative-`Proj` functor of
  [Section 27.16, tag 01NS](https://stacks.math.columbia.edu/tag/01NS); that identification is
  [Lemma 27.16.6, tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ) and is not made here.
* [Stacks Project, Lemma 27.16.2, tag 01NU](https://stacks.math.columbia.edu/tag/01NU): over an
  affine base the relative `Proj` is `Proj (Γ(S, 𝒜))`, which is
  `CategoryTheory.CommMon.relativeProjIsoProj` in `RelativeProj/Affine.lean`.
* R. Hartshorne, *Algebraic Geometry*, Section II.7, pp. 149–171: the hypothesis (+) of
  `FC06-C02-U230` and the construction `Proj S ⟶ X` with its twisting sheaves of
  `FC06-C02-U231`. The gluing below takes the weaker hypothesis of quasi-coherence in every
  degree; (+) is what the moduli description and the properness of `Proj S ⟶ X`
  (Proposition II.7.10, `FC06-C02-U235`) need, and neither is claimed in this unit.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §3.1.
* R. Hartshorne, *Algebraic Geometry*, Section II.7, before Proposition II.7.10.
-/

public section

open CategoryTheory Limits Opposite DirectSum

namespace CategoryTheory.CommMon

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules))

section BasicOpen

variable {U : X.Opens} (f : Γ(X, U))

variable [∀ n, (A.X n).IsQuasicoherent] (hU : IsAffineOpen U)
include hU

/-- For an affine open `U` of `X` and `f ∈ Γ(X, U)`, the irrelevant ideal of `⨁ n, Γ(Aₙ, D(f))` is
contained in the ideal generated by the image of the irrelevant ideal of `⨁ n, Γ(Aₙ, U)` under
restriction of sections, so that `Proj.map` gives `Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))`.
-/
theorem irrelevant_le_map_restrictGradedSectionsGradedHom
    (i : X.basicOpen f ⟶ U) :
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading (X.basicOpen f)) ≤
      (HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U)).map
        (A.restrictGradedSectionsGradedHom i) := by
  obtain rfl : i = homOfLE (X.basicOpen_le f) := Subsingleton.elim _ _
  let := A.algebraGradedSectionsBasicOpen f
  exact HomogeneousIdeal.irrelevant_le_map_of_isBaseChange _ _ _
    (A.isBaseChange_restrictGradedSections f hU)

/-- **The charts of the relative `Proj` are compatible with restriction.** For an affine open `U`
of `X` and `f ∈ Γ(X, U)`, the square

`Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))`, `Spec Γ(X, D(f)) ⟶ Spec Γ(X, U)`

formed by restriction of sections and the coefficient projections is cartesian. -/
theorem isPullback_proj_restrictGradedSections
    (i : X.basicOpen f ⟶ U) :
    IsPullback (Proj.map (A.restrictGradedSectionsGradedHom i)
        (A.irrelevant_le_map_restrictGradedSectionsGradedHom f hU i))
      (Proj.toSpecCoeff (A.gradedSectionsGrading (X.basicOpen f)))
      (Proj.toSpecCoeff (A.gradedSectionsGrading U)) (Spec.map (X.presheaf.map i.op)) := by
  obtain rfl : i = homOfLE (X.basicOpen_le f) := Subsingleton.elim _ _
  let := A.algebraGradedSectionsBasicOpen f
  -- the algebra structure of `Γ(X, D(f))` over `Γ(X, U)` is restriction of functions
  exact Proj.isPullback_map_of_isBaseChange _ _ _ (A.isBaseChange_restrictGradedSections f hU)

/-- The chart `Proj (⨁ n, Γ(Aₙ, D(f)))` of the relative `Proj` maps into the locus of the chart
`Proj (⨁ n, Γ(Aₙ, U))` where the image of `f` in degree zero is invertible. -/
theorem proj_map_restrictGradedSections_preimage_basicOpen_eq_top
    (i : X.basicOpen f ⟶ U) :
    Proj.map _ (A.irrelevant_le_map_restrictGradedSectionsGradedHom f hU i) ⁻¹ᵁ
      Proj.basicOpen _ (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f) = ⊤ := by
  have := Subsingleton.elim i (homOfLE (X.basicOpen_le f))
  subst this
  -- the restriction of `f` to `D(f)` is a unit, so it lies in no homogeneous prime
  have hunit : IsUnit (A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f))
      (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f)) := by
    rw [CommMon.restrictGradedSectionsGradedHom_apply, CommMon.restrictGradedSections_algebraMap]
    exact (X.toRingedSpace.isUnit_res_basicOpen f).map _
  rw [Proj.map_preimage_basicOpen, eq_top_iff]
  exact fun y _ ↦ (Proj.mem_basicOpen _ _ _).mpr fun h ↦
    y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hunit)

end BasicOpen

section Gluing

open Scheme.AffineZariskiSite

variable [∀ n, (A.X n).IsQuasicoherent]

/-- For an arrow `i : U ⟶ V` of the small affine Zariski site of `X`, the irrelevant ideal of
`⨁ n, Γ(Aₙ, U)` is contained in the ideal generated by the image of the irrelevant ideal of
`⨁ n, Γ(Aₙ, V)` under restriction of sections along `i`, so that `Proj.map` applies. This holds
because `U` is a basic open of the affine open `V`. -/
theorem
    irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U.toOpens) ≤
      (HomogeneousIdeal.irrelevant (A.gradedSectionsGrading V.toOpens)).map
        (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i)) := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨f, rfl⟩ := leOfHom i
  exact A.irrelevant_le_map_restrictGradedSectionsGradedHom f V.2 _

/-- The schemes `Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U` of `X`, with the morphisms
induced by restriction of sections to basic opens. -/
@[expose]
def relativeProjFunctor : X.AffineZariskiSite ⥤ Scheme.{u} where
  obj U := Proj (A.gradedSectionsGrading U.toOpens)
  map i := Proj.map _ (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i)
  map_id U := (Proj.map_congr (by
    rw [Subsingleton.elim ((toOpensFunctor X).map (𝟙 U)) (𝟙 _),
      CommMon.restrictGradedSectionsGradedHom_id]
    -- `(toOpensFunctor X).obj U` is `U.toOpens` by definition
    rfl) _ _).trans Proj.map_id
  map_comp i j := (Proj.map_congr
    (g := (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i)).comp
      (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map j)))
    (by rw [Functor.map_comp, CommMon.restrictGradedSectionsGradedHom_comp]) _ _).trans
      (Proj.map_comp _ _ _ _)

/-- The coefficient projections `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Spec Γ(X, U)`, natural in the affine
open `U`. -/
@[expose]
def relativeProjToSpec :
    A.relativeProjFunctor ⟶ toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec where
  app U := Proj.toSpecCoeff (A.gradedSectionsGrading U.toOpens)
  naturality U V i := by
    obtain ⟨U, hU⟩ := U
    obtain ⟨f, rfl⟩ := leOfHom i
    exact (A.isPullback_proj_restrictGradedSections f V.2 _).w

/-- The coefficient projections of the charts of the relative `Proj` form an equifibered natural
transformation: every naturality square is cartesian. -/
theorem equifibered_relativeProjToSpec :
    A.relativeProjToSpec.Equifibered := by
  intro U V i
  obtain ⟨U, hU⟩ := U
  obtain ⟨f, rfl⟩ := leOfHom i
  exact A.isPullback_proj_restrictGradedSections f V.2 _

/-- The relative gluing datum of the relative `Proj` of `A`: the schemes `Proj (⨁ n, Γ(Aₙ, U))`
over the affine opens `U` of `X`. -/
@[expose]
def relativeProjGluingData :
    (directedCover X).RelativeGluingData where
  functor := A.relativeProjFunctor
  natTrans := A.relativeProjToSpec ≫ (restrictIsoSpec X).inv
  equifibered :=
    A.equifibered_relativeProjToSpec.comp (NatTrans.Equifibered.of_isIso (restrictIsoSpec X).inv)

/-- The transition maps of the relative `Proj` gluing datum are the morphisms of projective spectra
induced by restriction of sections. -/
theorem relativeProjGluingData_functor_map
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    A.relativeProjGluingData.functor.map i =
      Proj.map (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i))
        (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i) :=
  (rfl)

/-- The structure morphisms of the relative `Proj` gluing datum are the coefficient projections
`Proj (⨁ n, Γ(Aₙ, U)) ⟶ Spec Γ(X, U)` followed by `Spec Γ(X, U) ≅ U`. -/
theorem relativeProjGluingData_natTrans_app
    (U : X.AffineZariskiSite) :
    A.relativeProjGluingData.natTrans.app U =
      Proj.toSpecCoeff (A.gradedSectionsGrading U.toOpens) ≫ U.2.isoSpec.inv :=
  (rfl)

/-- The gluing diagram of the relative `Proj` is locally directed. -/
instance isLocallyDirected_relativeProjGluingData :
    (A.relativeProjGluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The **relative `Proj`** `Proj_X(A)` of a graded algebra `A` on `X` with quasi-coherent
homogeneous components, glued from the schemes `Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U`
of `X`. -/
@[expose, stacks 01NS]
def relativeProj : Scheme.{u} :=
  A.relativeProjGluingData.glued

/-- The structure morphism `Proj_X(A) ⟶ X` of the relative `Proj`. -/
@[expose]
def relativeProjToBase : A.relativeProj ⟶ X :=
  A.relativeProjGluingData.toBase

/-- The open cover of the relative `Proj` by the schemes `Proj (⨁ n, Γ(Aₙ, U))` over the affine
opens `U` of `X`. -/
@[expose]
def relativeProjCover : A.relativeProj.OpenCover :=
  A.relativeProjGluingData.cover

/-- The charts of the relative `Proj` are open immersions. -/
instance isOpenImmersion_relativeProjCover_f
    (U : X.AffineZariskiSite) : IsOpenImmersion (A.relativeProjCover.f U) :=
  A.relativeProjCover.map_prop U

/-- The charts of the relative `Proj`, written as the coprojections of the gluing diagram, are open
immersions. -/
instance _root_.CategoryTheory.CommMon.isOpenImmersion_colimit_ι_relativeProjGluingData
    (U : X.AffineZariskiSite) : IsOpenImmersion (colimit.ι A.relativeProjGluingData.functor U) :=
  A.isOpenImmersion_relativeProjCover_f U

/-- The chart of the relative `Proj` over an affine open `U` is `Proj (⨁ n, Γ(Aₙ, U))`. -/
theorem relativeProjCover_X (U : X.AffineZariskiSite) :
    A.relativeProjCover.X U = Proj (A.gradedSectionsGrading U.toOpens) :=
  (rfl)

/-- Over an affine open `U`, the structure morphism of the relative `Proj` is the coefficient
projection `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Spec Γ(X, U)` followed by the chart `Spec Γ(X, U) ⟶ X`. -/
@[reassoc]
theorem relativeProjCover_f_relativeProjToBase
    (U : X.AffineZariskiSite) :
    A.relativeProjCover.f U ≫ A.relativeProjToBase =
      Proj.toSpecCoeff (A.gradedSectionsGrading U.toOpens) ≫ U.2.fromSpec := by
  -- the gluing datum's map to `U` is the coefficient projection followed by `U.2.isoSpec.inv`,
  -- and `U.2.isoSpec.inv ≫ U.ι = U.2.fromSpec` (`IsAffineOpen.isoSpec_inv_ι`) by definition
  exact (A.relativeProjGluingData.ι_toBase U).trans (Category.assoc _ _ _)

/-- The preimage of an affine open `U` under the structure morphism of the relative `Proj` is the
image of the chart `Proj (⨁ n, Γ(Aₙ, U))`. -/
theorem relativeProjToBase_preimage (U : X.AffineZariskiSite) :
    A.relativeProjToBase ⁻¹ᵁ U.toOpens = (A.relativeProjCover.f U).opensRange := by
  have h := A.relativeProjGluingData.toBase_preimage_eq_opensRange_ι U
  simp only [Scheme.Opens.opensRange_ι] at h
  exact h

/-- **Over an affine open `U` of `X`, the relative `Proj` is `Proj (⨁ n, Γ(Aₙ, U))`**: the chart
of the relative `Proj` over `U` is the base change of its structure morphism along `U ⟶ X`. -/
theorem isPullback_relativeProjCover (U : X.AffineZariskiSite) :
    IsPullback (Proj.toSpecCoeff (A.gradedSectionsGrading U.toOpens) ≫ U.2.isoSpec.inv)
      (A.relativeProjCover.f U) U.toOpens.ι A.relativeProjToBase :=
  A.relativeProjGluingData.isPullback_natTrans_ι_toBase U

end Gluing

end

end CategoryTheory.CommMon
