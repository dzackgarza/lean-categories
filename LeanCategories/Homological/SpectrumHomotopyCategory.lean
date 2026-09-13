/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CWSpectrum

/-!
# Homotopy category of spectra

Weibel, *An Introduction to Homological Algebra* (1994), Definition 10.9.10,
§10.9, pp. 407--416 (FC05-C10-U110).

The cylinder of a spectrum is obtained by spectrifying the prespectrum whose
levels are based cylinders.  Two maps are homotopic when they extend to a map
from this cylinder.  Homotopy classes form the morphisms `[E,F]` of the
homotopy category `K(S)`, and `K(S_CW)` is its full subcategory on CW spectra.

The source facts that cylinder homotopy is an equivalence relation and is
compatible with composition are recorded as the intrinsic realization data
needed to form the quotient category; no later additive or Whitehead theorem
is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- The basepoint line collapsed in the based cylinder `I_+ ∧ X`. -/
def cylinderCollapsed (X : BasedTop.{u}) : Set (unitInterval × X.right) :=
  {p | p.2 = X.point}

/-- The equivalence relation defining the based cylinder: all points on the
basepoint line are identified. -/
def cylinderSetoid (X : BasedTop.{u}) : Setoid (unitInterval × X.right) where
  r p q := p = q ∨ (p ∈ cylinderCollapsed X ∧ q ∈ cylinderCollapsed X)
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

/-- Underlying topological cylinder quotient. -/
abbrev BasedCylinder (X : BasedTop.{u}) := Quotient (cylinderSetoid X)

/-- The basepoint of the based cylinder. -/
def cylinderPoint (X : BasedTop.{u}) : BasedCylinder X :=
  Quotient.mk (cylinderSetoid X) (0, X.point)

/-- The based cylinder of a based space. -/
abbrev basedCylinderObj (X : BasedTop.{u}) : BasedTop.{u} :=
  Under.mk (TopCat.ofHom ⟨fun _ : PUnit => cylinderPoint X, continuous_const⟩)

/-- Endpoint inclusion `X ⟶ Cyl(X)` at `t`.  It is based because the whole
basepoint line is collapsed. -/
def cylinderEndpoint (X : BasedTop.{u}) (t : unitInterval) :
    X ⟶ basedCylinderObj X :=
  Under.homMk
    (TopCat.ofHom
      ⟨fun x => Quotient.mk (cylinderSetoid X) (t, x),
        continuous_quotient_mk'.comp
          (Continuous.prodMk continuous_const continuous_id)⟩)
    (by
      apply TopCat.ext
      intro z
      rcases z with ⟨⟩
      apply Quotient.sound
      right
      exact ⟨rfl, rfl⟩)

/-- A source-faithful realization of the cylinder spectrum of `E`.

The prespectrum is levelwise the based cylinder of `E_n`, and its
spectrification is the cylinder spectrum.  The two endpoint maps are the maps
used to define homotopy.

Source: Weibel, Definition 10.9.10 (FC05-C10-U110). -/
structure SpectrumCylinderRealization (E : Spectrum.{u}) where
  /-- The levelwise cylinder prespectrum. -/
  prespectrum : Prespectrum.{u}
  /-- Each level is the based cylinder of the corresponding spectrum level. -/
  levelIso : ∀ n : ℕ, prespectrum.space n ≅ basedCylinderObj (E.space n)
  /-- Spectrification of the cylinder prespectrum. -/
  spectrification : SpectrificationRealization prespectrum
  /-- Inclusion of the `0` endpoint. -/
  front : E ⟶ spectrification.spectrum
  /-- Inclusion of the `1` endpoint. -/
  back : E ⟶ spectrification.spectrum

/-- Homotopy through a chosen cylinder realization. -/
def SpectrumHomotopicWith {E F : Spectrum.{u}}
    (C : SpectrumCylinderRealization E) (f g : E ⟶ F) : Prop :=
  ∃ H : C.spectrification.spectrum ⟶ F,
    C.front ≫ H = f ∧ C.back ≫ H = g

/-- The intrinsic quotient data needed to form Weibel's homotopy category.

The setoid field is exactly cylinder homotopy, and `comp_respects` records the
standard compatibility with composition.  These are the laws required for
homotopy classes to be categorical morphisms. -/
structure SpectrumHomotopyTheory where
  /-- Chosen source cylinder for each spectrum. -/
  cylinder : ∀ E : Spectrum.{u}, SpectrumCylinderRealization E
  /-- Homotopy as an equivalence relation on each map set. -/
  homotopySetoid : ∀ E F : Spectrum.{u}, Setoid (E ⟶ F)
  /-- The equivalence relation is precisely cylinder homotopy. -/
  rel_iff : ∀ {E F : Spectrum.{u}} (f g : E ⟶ F),
    (homotopySetoid E F).r f g ↔
      SpectrumHomotopicWith (cylinder E) f g
  /-- Composition respects homotopy in both variables. -/
  comp_respects : ∀ {E F G : Spectrum.{u}}
      {f f' : E ⟶ F} {g g' : F ⟶ G},
    (homotopySetoid E F).r f f' →
      (homotopySetoid F G).r g g' →
        (homotopySetoid E G).r (f ≫ g) (f' ≫ g')

/-- Weibel's homotopy class set `[E,F]`. -/
def SpectrumHomotopyClass (H : SpectrumHomotopyTheory.{u})
    (E F : Spectrum.{u}) :=
  Quotient (H.homotopySetoid E F)

/-- Object wrapper for the homotopy category `K(S)`. -/
structure SpectrumHomotopyCategory (H : SpectrumHomotopyTheory.{u}) where
  /-- Underlying spectrum. -/
  spectrum : Spectrum.{u}

namespace SpectrumHomotopyCategory

variable (H : SpectrumHomotopyTheory.{u})

/-- A spectrum as an object of its homotopy category. -/
def ofSpectrum (E : Spectrum.{u}) : SpectrumHomotopyCategory H := ⟨E⟩

instance : Category (SpectrumHomotopyCategory H) where
  Hom X Y := SpectrumHomotopyClass H X.spectrum Y.spectrum
  id X := Quotient.mk _ (𝟙 X.spectrum)
  comp := fun {X Y Z} f g =>
    Quotient.liftOn₂ f g
      (fun f g => Quotient.mk _ (f ≫ g))
      (by
        intro f f' g g' hf hg
        exact Quotient.sound (H.comp_respects hf hg))
  id_comp := by
    intro X Y f
    refine Quotient.inductionOn f ?_
    intro f
    change Quotient.mk _ ((𝟙 X.spectrum) ≫ f) = Quotient.mk _ f
    rw [Category.id_comp]
  comp_id := by
    intro X Y f
    refine Quotient.inductionOn f ?_
    intro f
    change Quotient.mk _ (f ≫ 𝟙 Y.spectrum) = Quotient.mk _ f
    rw [Category.comp_id]
  assoc := by
    intro W X Y Z f g h
    refine Quotient.inductionOn₃ f g h ?_
    intro f g h
    change Quotient.mk _ ((f ≫ g) ≫ h) =
      Quotient.mk _ (f ≫ g ≫ h)
    rw [Category.assoc]

/-- The canonical functor `S ⥤ K(S)` sending a spectrum map to its homotopy
class. -/
def quotientFunctor : Spectrum.{u} ⥤ SpectrumHomotopyCategory H where
  obj := ofSpectrum H
  map f := Quotient.mk _ f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The CW-spectrum property transported to objects of `K(S)`. -/
def isCWProperty : ObjectProperty (SpectrumHomotopyCategory H) :=
  fun E => IsCWSpectrum E.spectrum

/-- Weibel's full subcategory `K(S_CW)` of the homotopy category on CW
spectra. -/
abbrev CW := (isCWProperty H).FullSubcategory

/-- Inclusion `K(S_CW) ⥤ K(S)`. -/
abbrev CW.inclusion : CW H ⥤ SpectrumHomotopyCategory H :=
  ObjectProperty.ι (isCWProperty H)

end SpectrumHomotopyCategory

end LeanCategories.Homological
