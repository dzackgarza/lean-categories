/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SpectrumHomotopyCategory

/-!
# Homotopy-commutative diagrams of spectra

Weibel, *An Introduction to Homological Algebra* (1994), §10.9,
pp. 407--416 (FC05-C10-U117).

A diagram of spectra is homotopy commutative when its competing composites
become equal in the homotopy category `K(S)`.  The definitions below expose
that criterion for a parallel pair and, in particular, for a square.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

universe u

/-- Two parallel spectrum maps commute up to homotopy when they determine the
same morphism in `K(S)`.

Source: Weibel, §10.9, p. 413 (FC05-C10-U117). -/
def SpectrumMapsHomotopic
    (H : SpectrumHomotopyTheory.{u})
    {E F : Spectrum.{u}} (f g : E ⟶ F) : Prop :=
  (SpectrumHomotopyCategory.quotientFunctor H).map f =
    (SpectrumHomotopyCategory.quotientFunctor H).map g

/-- A square of spectra, without imposing strict commutativity. -/
structure SpectrumSquare where
  nw : Spectrum.{u}
  ne : Spectrum.{u}
  sw : Spectrum.{u}
  se : Spectrum.{u}
  north : nw ⟶ ne
  west : nw ⟶ sw
  east : ne ⟶ se
  south : sw ⟶ se

/-- A square is homotopy commutative exactly when its two composites are equal
in the homotopy category.

Source: Weibel, §10.9, p. 413 (FC05-C10-U117). -/
def SpectrumSquare.IsHomotopyCommutative
    (H : SpectrumHomotopyTheory.{u}) (S : SpectrumSquare.{u}) : Prop :=
  SpectrumMapsHomotopic H (S.north ≫ S.east) (S.west ≫ S.south)

end LeanCategories.Homological
