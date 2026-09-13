/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SpectrumHomotopyCategory
public import LeanCategories.Homological.SpectrumSuspension

/-!
# Mapping cones and cofibration sequences of spectra

Weibel, *An Introduction to Homological Algebra* (1994), Mapping Cones
10.9.16, §10.9, pp. 407--416 (FC05-C10-U116).

For a spectrum map `u : E ⟶ F`, take the topological mapping cone of each
level map and spectrify the resulting prespectrum.  This defines `cone(u)`.
The maps

`E ⟶ F ⟶ cone(u) ⟶ SE`

form the Puppe sequence.  A cofibration sequence is a spectrum triangle
isomorphic to a Puppe sequence.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- The subset collapsed in the reduced cone: the top endpoint and the
basepoint line. -/
def coneCollapsed (X : BasedTop.{u}) : Set (unitInterval × X.right) :=
  {p | p.1 = 1 ∨ p.2 = X.point}

/-- Equivalence relation defining the reduced cone on a based space. -/
def coneSetoid (X : BasedTop.{u}) : Setoid (unitInterval × X.right) where
  r p q := p = q ∨ (p ∈ coneCollapsed X ∧ q ∈ coneCollapsed X)
  iseqv := by
    refine ⟨fun p => Or.inl rfl, ?_, ?_⟩
    · intro p q h
      rcases h with rfl | ⟨hp, hq⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hq, hp⟩
    · intro p q r hpq hqr
      rcases hpq with rfl | ⟨hp, hq⟩
      · exact hqr
      rcases hqr with rfl | ⟨_, hr⟩
      · exact Or.inr ⟨hp, hq⟩
      · exact Or.inr ⟨hp, hr⟩

/-- Underlying quotient space of the reduced cone. -/
abbrev BasedCone (X : BasedTop.{u}) := Quotient (coneSetoid X)

/-- Basepoint of the reduced cone. -/
def conePoint (X : BasedTop.{u}) : BasedCone X :=
  Quotient.mk (coneSetoid X) (1, X.point)

/-- The reduced cone as a based topological space. -/
abbrev basedConeObj (X : BasedTop.{u}) : BasedTop.{u} :=
  Under.mk (TopCat.ofHom ⟨fun _ : PUnit => conePoint X, continuous_const⟩)

/-- Inclusion of the base `X ⟶ CX` at cylinder time zero. -/
def coneBase (X : BasedTop.{u}) : X ⟶ basedConeObj X :=
  Under.homMk
    (TopCat.ofHom
      ⟨fun x => Quotient.mk (coneSetoid X) (0, x),
        continuous_quotient_mk'.comp
          (Continuous.prodMk continuous_const continuous_id)⟩)
    (by
      apply TopCat.ext
      intro z
      rcases z with ⟨⟩
      apply Quotient.sound
      right
      constructor
      · exact Or.inr rfl
      · exact Or.inl rfl)

/-- A realization of the based topological mapping cone of a based map
`f : X ⟶ Y`, characterized as the pushout of `f` and the cone-base
inclusion `X ⟶ CX`. -/
structure BasedMappingConeRealization {X Y : BasedTop.{u}} (f : X ⟶ Y) where
  /-- The mapping-cone space. -/
  cone : BasedTop.{u}
  /-- Inclusion of the target. -/
  inTarget : Y ⟶ cone
  /-- Inclusion of the reduced cone on the source. -/
  inCone : basedConeObj X ⟶ cone
  /-- The two copies of `X` are glued by `f`. -/
  glue : f ≫ inTarget = coneBase X ≫ inCone
  /-- Universal map out of the pushout. -/
  desc : ∀ {Z : BasedTop.{u}} (g : Y ⟶ Z) (h : basedConeObj X ⟶ Z),
    f ≫ g = coneBase X ≫ h → (cone ⟶ Z)
  /-- The descended map restricts to `g` on `Y`. -/
  inTarget_desc : ∀ {Z : BasedTop.{u}} (g : Y ⟶ Z)
      (h : basedConeObj X ⟶ Z) (w : f ≫ g = coneBase X ≫ h),
    inTarget ≫ desc g h w = g
  /-- The descended map restricts to `h` on `CX`. -/
  inCone_desc : ∀ {Z : BasedTop.{u}} (g : Y ⟶ Z)
      (h : basedConeObj X ⟶ Z) (w : f ≫ g = coneBase X ≫ h),
    inCone ≫ desc g h w = h
  /-- The universal map is unique. -/
  uniq : ∀ {Z : BasedTop.{u}} (g : Y ⟶ Z) (h : basedConeObj X ⟶ Z)
      (w : f ≫ g = coneBase X ≫ h) (k : cone ⟶ Z),
    inTarget ≫ k = g → inCone ≫ k = h → k = desc g h w

/-- Levelwise mapping-cone prespectrum for a map of spectra. -/
structure SpectrumMappingConePrespectrumRealization
    {E F : Spectrum.{u}} (u : E ⟶ F) where
  /-- Prespectrum of levelwise mapping cones. -/
  prespectrum : Prespectrum.{u}
  /-- Chosen mapping-cone realization at each level. -/
  levelCone : ∀ n : ℕ, BasedMappingConeRealization (u.app n)
  /-- Identification of the prespectrum level with that mapping cone. -/
  levelIso : ∀ n : ℕ, prespectrum.space n ≅ (levelCone n).cone

/-- Weibel's mapping-cone spectrum `cone(u)`, obtained by spectrifying the
levelwise mapping-cone prespectrum. -/
structure SpectrumMappingConeRealization
    {E F : Spectrum.{u}} (u : E ⟶ F) where
  /-- Levelwise cone prespectrum. -/
  levelwise : SpectrumMappingConePrespectrumRealization u
  /-- Spectrification of that prespectrum. -/
  spectrification : SpectrificationRealization levelwise.prespectrum

/-- The mapping-cone spectrum attached to a chosen realization. -/
def spectrumMappingCone {E F : Spectrum.{u}} (u : E ⟶ F)
    (C : SpectrumMappingConeRealization u) : Spectrum.{u} :=
  C.spectrification.spectrum

/-- A spectrum triangle with a specified suspension realization of its first
object. -/
structure SpectrumCofibrationDiagram where
  E : Spectrum.{u}
  F : Spectrum.{u}
  G : Spectrum.{u}
  suspension : SpectrumSuspensionRealization E
  first : E ⟶ F
  second : F ⟶ G
  third : G ⟶ suspensionSpectrum E suspension

/-- Isomorphism of spectrum cofibration diagrams. -/
structure SpectrumCofibrationDiagram.Iso
    (T U : SpectrumCofibrationDiagram.{u}) where
  eE : T.E ≅ U.E
  eF : T.F ≅ U.F
  eG : T.G ≅ U.G
  eS : suspensionSpectrum T.E T.suspension ≅
    suspensionSpectrum U.E U.suspension
  first_comm : T.first ≫ eF.hom = eE.hom ≫ U.first
  second_comm : T.second ≫ eG.hom = eF.hom ≫ U.second
  third_comm : T.third ≫ eS.hom = eG.hom ≫ U.third

/-- Source data of the Puppe sequence
`E → F → cone(u) → SE`. -/
structure SpectrumPuppeRealization {E F : Spectrum.{u}} (u : E ⟶ F) where
  suspension : SpectrumSuspensionRealization E
  cone : SpectrumMappingConeRealization u
  inCone : F ⟶ spectrumMappingCone u cone
  connecting : spectrumMappingCone u cone ⟶ suspensionSpectrum E suspension

/-- The cofibration diagram underlying a Puppe realization. -/
def SpectrumPuppeRealization.diagram {E F : Spectrum.{u}} {u : E ⟶ F}
    (P : SpectrumPuppeRealization u) : SpectrumCofibrationDiagram.{u} where
  E := E
  F := F
  G := spectrumMappingCone u P.cone
  suspension := P.suspension
  first := u
  second := P.inCone
  third := P.connecting

/-- Weibel's definition: a cofibration sequence is any spectrum triangle
isomorphic to a Puppe sequence.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
def IsSpectrumCofibrationSequence (T : SpectrumCofibrationDiagram.{u}) : Prop :=
  ∃ (E F : Spectrum.{u}) (u : E ⟶ F) (P : SpectrumPuppeRealization u),
    Nonempty (SpectrumCofibrationDiagram.Iso T P.diagram)

end LeanCategories.Homological
