/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Spectrification
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# CW spectra

Weibel, *An Introduction to Homological Algebra* (1994), §10.9,
pp. 407--416 (FC05-C10-U106).

A CW spectrum is a spectrum isomorphic to the spectrification `Ω^∞D` of a
CW prespectrum `D`.  The category `S_CW` is the corresponding full
subcategory of the category of spectra.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

universe u

/-- A spectrum is a CW spectrum when it is represented by the
spectrification of a CW prespectrum.

Source: Weibel, §10.9, p. 410 (FC05-C10-U106). -/
def IsCWSpectrum (E : Spectrum.{u}) : Prop :=
  ∃ (D : Prespectrum.{u}) (_hD : D.IsCW)
      (S : SpectrificationRealization D), Nonempty (S.spectrum ≅ E)

/-- The object property of CW spectra. -/
def cwSpectrumProperty : ObjectProperty Spectrum.{u} :=
  IsCWSpectrum

/-- Weibel's full subcategory `S_CW` of spectra on the CW spectra.

Source: Weibel, §10.9, p. 410 (FC05-C10-U106). -/
abbrev CWSpectrum := cwSpectrumProperty.FullSubcategory

/-- The inclusion `S_CW ⥤ S`. -/
abbrev CWSpectrum.inclusion : CWSpectrum.{u} ⥤ Spectrum.{u} :=
  ObjectProperty.ι cwSpectrumProperty

end LeanCategories.Homological
