/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Spectrum
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Stable homotopy groups and the stable homotopy category

Weibel, *An Introduction to Homological Algebra*, Definition 10.9.4, pp. 408--409
(FC05-C10-U103).

For an integer `n`, the stable homotopy group of a spectrum `E` is
`π_{n+i}(E_i)` for any sufficiently large `i`; the spectrum structure homeomorphisms identify the
choices.  We make the definition canonical by taking `i = max(0, 2-n)`, so `n+i ≥ 2`.  Weak
homotopy equivalences are exactly the spectrum maps inducing bijections on every stable homotopy
group, and the stable homotopy category is the Gabriel--Zisman localization at those maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology Topology.Homotopy

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- A canonical sufficiently large level at which to read the `n`th stable homotopy group.
It is `max(0,2-n)`, expressed using `Int.toNat`, so the ordinary homotopy degree is always at
least two.

Source: Weibel, Definition 10.9.4 (FC05-C10-U103). -/
def stableHomotopyLevel (n : ℤ) : ℕ :=
  Int.toNat (2 - n)

/-- The ordinary homotopy degree used at `stableHomotopyLevel n`. -/
def stableHomotopyDegree (n : ℤ) : ℕ :=
  Int.toNat (n + stableHomotopyLevel n)

/-- Postcomposition sends a generalized based loop to a generalized based loop. -/
def basedGenLoopMap {X Y : BasedTop.{u}} (f : X ⟶ Y) (N : Type*)
    (p : GenLoop N X.right X.point) : GenLoop N Y.right Y.point :=
  ⟨f.right.hom.comp p.1, by
    intro z hz
    change f.right (p z) = Y.point
    calc
      f.right (p z) = f.right X.point := congrArg f.right (p.2 z hz)
      _ = Y.point := BasedTop.map_point f⟩

/-- Postcomposition by a based map preserves homotopy relative to the cube boundary. -/
theorem basedGenLoopMap_homotopic {X Y : BasedTop.{u}} (f : X ⟶ Y) {N : Type*}
    {p q : GenLoop N X.right X.point} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (basedGenLoopMap f N p) (basedGenLoopMap f N q) := by
  change (f.right.hom.comp p.1).HomotopicRel (f.right.hom.comp q.1) (Cube.boundary N)
  exact h.comp_continuousMap f.right.hom

/-- The map on homotopy groups induced by a based map. -/
def basedHomotopyGroupMap {X Y : BasedTop.{u}} (f : X ⟶ Y) (N : Type*) :
    HomotopyGroup N X.right X.point → HomotopyGroup N Y.right Y.point :=
  Quotient.map (basedGenLoopMap f N) (fun _ _ h => basedGenLoopMap_homotopic f h)

/-- The `n`th stable homotopy group of a spectrum, evaluated at the canonical sufficiently large
level `stableHomotopyLevel n`.

Source: Weibel, Definition 10.9.4 (FC05-C10-U103). -/
abbrev stableHomotopyGroup (E : Spectrum.{u}) (n : ℤ) : Type u :=
  HomotopyGroup.Pi (stableHomotopyDegree n)
    (E.space (stableHomotopyLevel n)).right (E.space (stableHomotopyLevel n)).point

/-- The map on the `n`th stable homotopy group induced by a spectrum map. -/
def stableHomotopyGroupMap {E F : Spectrum.{u}} (f : E ⟶ F) (n : ℤ) :
    stableHomotopyGroup E n → stableHomotopyGroup F n :=
  basedHomotopyGroupMap (f.app (stableHomotopyLevel n)) (Fin (stableHomotopyDegree n))

/-- Weak homotopy equivalences of spectra are precisely the maps inducing isomorphisms (equivalently
bijections on the underlying types) on all stable homotopy groups.

Source: Weibel, Definition 10.9.4 (FC05-C10-U103). -/
def spectrumWeakEquivalence : MorphismProperty Spectrum.{u} :=
  fun _ _ f => ∀ n : ℤ, Function.Bijective (stableHomotopyGroupMap f n)

/-- The stable homotopy category (Weibel's topological derived category)
`D(S) = W̃⁻¹ S`, obtained by formally inverting weak homotopy equivalences.

Source: Weibel, Definition 10.9.4 (FC05-C10-U103). -/
abbrev StableHomotopyCategory : Type (u + 1) :=
  spectrumWeakEquivalence.Localization

/-- The canonical localization functor from spectra to the stable homotopy category.

Source: Weibel, Definition 10.9.4 (FC05-C10-U103). -/
def stableHomotopyLocalization : Spectrum.{u} ⥤ StableHomotopyCategory.{u} :=
  spectrumWeakEquivalence.Q

end LeanCategories.Homological
