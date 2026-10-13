/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SpectrumHomotopyCategory
public import LeanCategories.Homological.SpectrumSuspension
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

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

open CategoryTheory CategoryTheory.Limits

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

/-- The based topological mapping cone of `f : X ⟶ Y`, formed as the
canonical pushout `Y ⊔_X CX` in based spaces.

This is the level object used in Weibel's mapping-cone prespectrum.  The
universal property belongs to the native pushout and is not reproved here.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
noncomputable def basedMappingCone {X Y : BasedTop.{u}} (f : X ⟶ Y) :
    BasedTop.{u} :=
  pushout f (coneBase X)

/-- The canonical inclusion of the target into its based mapping cone. -/
noncomputable def basedMappingConeInTarget {X Y : BasedTop.{u}} (f : X ⟶ Y) :
    Y ⟶ basedMappingCone f :=
  pushout.inl f (coneBase X)

/-- The canonical inclusion of the reduced cone into the based mapping cone. -/
noncomputable def basedMappingConeInCone {X Y : BasedTop.{u}} (f : X ⟶ Y) :
    basedConeObj X ⟶ basedMappingCone f :=
  pushout.inr f (coneBase X)

/-- Level `n` of the raw mapping-cone construction for a spectrum map `u`. -/
noncomputable def spectrumMappingConeLevel {E F : Spectrum.{u}} (u : E ⟶ F) (n : ℕ) :
    BasedTop.{u} :=
  basedMappingCone (u.app n)

/-- On the target summand, the prospective prespectrum structure map is
obtained from the suspension structure map of `F` and then included in the
next mapping-cone level.

This is recorded on suspension representatives only.  Its descent through the
mapping-cone/suspension quotients is a Sweep-IV well-definedness statement.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
noncomputable def mappingConeTargetStructureRepresentative
    {E F : Spectrum.{u}} (u : E ⟶ F) (n : ℕ)
    (p : unitInterval × (F.space n).right) :
    (spectrumMappingConeLevel u (n + 1)).right :=
  (basedMappingConeInTarget (u.app (n + 1))).right
    (((Prespectrum.ofSpectrumObj F).structureMap n).right
      (Quotient.mk (suspensionSetoid (F.space n)) p))

/-- On a cone representative `(t,x)`, with outer suspension coordinate `s`,
the prospective prespectrum structure map keeps the cone coordinate `t` and
applies the spectrum structure of `E` to the suspension representative
`(s,x)`.

The formula is deliberately recorded before quotient descent: proving that it
and `mappingConeTargetStructureRepresentative` glue to a continuous based map
is result-layer work, not part of Sweep III.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
noncomputable def mappingConeConeStructureRepresentative
    {E F : Spectrum.{u}} (u : E ⟶ F) (n : ℕ)
    (p : unitInterval × (unitInterval × (E.space n).right)) :
    (spectrumMappingConeLevel u (n + 1)).right :=
  let nextPoint :=
    ((Prespectrum.ofSpectrumObj E).structureMap n).right
      (Quotient.mk (suspensionSetoid (E.space n)) (p.1, p.2.2))
  (basedMappingConeInCone (u.app (n + 1))).right
    (Quotient.mk (coneSetoid (E.space (n + 1))) (p.2.1, nextPoint))

/-- On the target summand `F_n`, the prospective Puppe collapse
`cone(u)_n ⟶ S E_n` is the suspension basepoint. -/
def mappingConeCollapseTargetRepresentative
    {E F : Spectrum.{u}} (_u : E ⟶ F) (n : ℕ) (_y : (F.space n).right) :
    Suspension (E.space n) :=
  suspensionPoint (E.space n)

/-- On a cone representative `(t,x)`, the prospective Puppe collapse is the
corresponding suspension representative `[t,x]`.

Compatibility with the mapping-cone relation, continuity, and compatibility
with the prespectrum structure maps are Sweep-IV statements.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
def mappingConeCollapseConeRepresentative
    {E F : Spectrum.{u}} (_u : E ⟶ F) (n : ℕ)
    (p : unitInterval × (E.space n).right) : Suspension (E.space n) :=
  Quotient.mk (suspensionSetoid (E.space n)) p

/-- Proof-free raw data of Weibel's mapping-cone/Puppe construction.

The level mapping cones and the formulas on the two kinds of representatives
are canonical.  Sweep IV proves that the representative formulas descend to
the mapping-cone prespectrum, that spectrification produces the cone spectrum,
and that the collapse gives the Puppe map in the homotopy category.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
structure SpectrumMappingConeData {E F : Spectrum.{u}} (u : E ⟶ F) where
  /-- Canonical level mapping cones `CE_n ∪_{u_n} F_n`. -/
  level : ℕ → BasedTop.{u}
  /-- Inclusion of `F_n` into the level mapping cone. -/
  inTarget : ∀ n : ℕ, F.space n ⟶ level n
  /-- Inclusion of `CE_n` into the level mapping cone. -/
  inCone : ∀ n : ℕ, basedConeObj (E.space n) ⟶ level n
  /-- Formula for the prospective structure map on the target summand. -/
  targetStructureRepresentative : ∀ n : ℕ,
    unitInterval × (F.space n).right → (level (n + 1)).right
  /-- Formula for the prospective structure map on cone representatives. -/
  coneStructureRepresentative : ∀ n : ℕ,
    unitInterval × (unitInterval × (E.space n).right) → (level (n + 1)).right
  /-- Formula for the Puppe collapse on the target summand. -/
  collapseTargetRepresentative : ∀ n : ℕ,
    (F.space n).right → Suspension (E.space n)
  /-- Formula for the Puppe collapse on cone representatives. -/
  collapseConeRepresentative : ∀ n : ℕ,
    unitInterval × (E.space n).right → Suspension (E.space n)

/-- The canonical raw mapping-cone/Puppe data attached to a spectrum map. -/
noncomputable def spectrumMappingConeData {E F : Spectrum.{u}} (u : E ⟶ F) :
    SpectrumMappingConeData u where
  level := spectrumMappingConeLevel u
  inTarget := fun n => basedMappingConeInTarget (u.app n)
  inCone := fun n => basedMappingConeInCone (u.app n)
  targetStructureRepresentative := mappingConeTargetStructureRepresentative u
  coneStructureRepresentative := mappingConeConeStructureRepresentative u
  collapseTargetRepresentative := mappingConeCollapseTargetRepresentative u
  collapseConeRepresentative := mappingConeCollapseConeRepresentative u

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

/-- Auxiliary strict spectrum triangle.  The source definition of a
cofibration sequence lives in the homotopy category; this strict record is
retained only as result-layer realization data. -/
structure SpectrumCofibrationDiagram where
  E : Spectrum.{u}
  F : Spectrum.{u}
  G : Spectrum.{u}
  suspension : SpectrumSuspensionRealization E
  first : E ⟶ F
  second : F ⟶ G
  third : G ⟶ suspensionSpectrum E suspension

/-- Auxiliary strict isomorphism of spectrum cofibration diagrams. -/
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

/-- An object of `K(S_CW)` obtained from a spectrum together with its CW
property. -/
def cwHomotopyObject (H : SpectrumHomotopyTheory.{u}) (E : Spectrum.{u})
    (hE : IsCWSpectrum E) : SpectrumHomotopyCategory.CW H :=
  ⟨SpectrumHomotopyCategory.ofSpectrum H E, hE⟩

/-- A four-term triangle in Weibel's CW-spectrum homotopy category
`K(S_CW)`.  The fourth object records the suspension vertex explicitly; for a
Puppe triangle it is the image of `SE`.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
structure CWSpectrumCofibrationDiagram (H : SpectrumHomotopyTheory.{u}) where
  E : SpectrumHomotopyCategory.CW H
  F : SpectrumHomotopyCategory.CW H
  G : SpectrumHomotopyCategory.CW H
  suspension : SpectrumHomotopyCategory.CW H
  first : E ⟶ F
  second : F ⟶ G
  third : G ⟶ suspension

/-- Isomorphism of four-term triangles inside `K(S_CW)`.  The commutativity
conditions are part of the definition of diagram isomorphism; no instance is
constructed in Sweep III. -/
structure CWSpectrumCofibrationDiagram.Iso
    {H : SpectrumHomotopyTheory.{u}}
    (T U : CWSpectrumCofibrationDiagram H) where
  eE : T.E ≅ U.E
  eF : T.F ≅ U.F
  eG : T.G ≅ U.G
  eS : T.suspension ≅ U.suspension
  first_comm : T.first ≫ eF.hom = eE.hom ≫ U.first
  second_comm : T.second ≫ eG.hom = eF.hom ≫ U.second
  third_comm : T.third ≫ eS.hom = eG.hom ≫ U.third

/-- Result-layer bridge asserting that a strict Puppe realization has CW
vertices, so that it determines a triangle in `K(S_CW)`.

The CW assertions are fields rather than Sweep-III proof obligations. -/
structure CWSpectrumPuppeRealization (H : SpectrumHomotopyTheory.{u})
    {E F : Spectrum.{u}} (u : E ⟶ F) where
  puppe : SpectrumPuppeRealization u
  sourceCW : IsCWSpectrum E
  targetCW : IsCWSpectrum F
  coneCW : IsCWSpectrum (spectrumMappingCone u puppe.cone)
  suspensionCW : IsCWSpectrum (suspensionSpectrum E puppe.suspension)

/-- The Puppe triangle associated to a CW Puppe realization, now regarded in
`K(S_CW)` rather than in the strict spectrum category. -/
def CWSpectrumPuppeRealization.diagram
    {H : SpectrumHomotopyTheory.{u}} {E F : Spectrum.{u}} {u : E ⟶ F}
    (P : CWSpectrumPuppeRealization H u) : CWSpectrumCofibrationDiagram H :=
  let q := SpectrumHomotopyCategory.quotientFunctor H
  { E := cwHomotopyObject H E P.sourceCW
    F := cwHomotopyObject H F P.targetCW
    G := cwHomotopyObject H (spectrumMappingCone u P.puppe.cone) P.coneCW
    suspension :=
      cwHomotopyObject H (suspensionSpectrum E P.puppe.suspension) P.suspensionCW
    first := ObjectProperty.homMk (q.map u)
    second := ObjectProperty.homMk (q.map P.puppe.inCone)
    third := ObjectProperty.homMk (q.map P.puppe.connecting) }

/-- Weibel's definition: a cofibration sequence is a triangle in
`K(S_CW)` isomorphic there to a Puppe sequence.

Source: Weibel, Mapping Cones 10.9.16 (FC05-C10-U116). -/
def IsSpectrumCofibrationSequence (H : SpectrumHomotopyTheory.{u})
    (T : CWSpectrumCofibrationDiagram H) : Prop :=
  ∃ (E F : Spectrum.{u}) (u : E ⟶ F) (P : CWSpectrumPuppeRealization H u),
    Nonempty (CWSpectrumCofibrationDiagram.Iso T P.diagram)

end LeanCategories.Homological
