/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.TwoElementaryRootSquare
public import LeanCategories.Lattices.Valued.Standard

/-!
# Probe for the `(−2)`/`(−4)` rule

AEGS **printed p. 10**: *"The lattices `L^±_En` and `L^±_dP` are even 2-elementary. For such
lattices the roots are the `(−2)`-vectors and the `(−4)`-vectors with `div(α) = 2`."*

The probes below do not restate that as a hypothesis — they use it. Two consequences are decided,
both of which would be false for a general even lattice:

* no negative reflective root has square `−8`;
* in the `(−4)` case every pairing off the root is even, which is what makes the root reflective in
  an ambient lattice (`isReflectiveRoot_iff_two_dvd_pairing`).

That neither holds without two-elementary is not a conjecture: the even lattice with Gram matrix
`((−6,3),(3,−6))` has `e₁` of square `−6`, and `−6 ∣ 2⟨e₁,y⟩` for every `y`, so `e₁` is a reflective
root of square `−6`. Its divisibility is `3`, so that lattice is not 2-elementary — the
hypothesis is
doing real work, not phrasing.

The evenness and 2-elementary hypotheses are carried, not discharged: they are the published
properties of the paper's lattices, not something this file proves about them.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- No negative reflective root of an even 2-elementary lattice has square `−8`. -/
example
    (hev : ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
      (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing y y)
    (h2e : ∀ x : hyperbolicPlaneFiniteLattice.obj.obj.carrier, x ≠ 0 →
      ∃ (y₁ y₂ : hyperbolicPlaneFiniteLattice.obj.obj.carrier) (c₁ c₂ : ℤ),
        c₁ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₁ +
          c₂ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₂ = 2)
    {x : hyperbolicPlaneFiniteLattice.obj.obj.carrier}
    (hx : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj x)
    (hneg : hyperbolicPlaneFiniteLattice.obj.obj.pairing x x < 0) :
    ¬ (hyperbolicPlaneFiniteLattice.obj.obj.pairing x x = -8) := by
  have h := pairing_eq_neg_two_or_neg_four_of_two_elementary hev h2e hx hneg
  omega

/-- In the `(−4)` case the pairings off the root are all even. -/
example
    (hev : ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
      (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing y y)
    (h2e : ∀ x : hyperbolicPlaneFiniteLattice.obj.obj.carrier, x ≠ 0 →
      ∃ (y₁ y₂ : hyperbolicPlaneFiniteLattice.obj.obj.carrier) (c₁ c₂ : ℤ),
        c₁ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₁ +
          c₂ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₂ = 2)
    {x : hyperbolicPlaneFiniteLattice.obj.obj.carrier}
    (hx : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj x)
    (hneg : hyperbolicPlaneFiniteLattice.obj.obj.pairing x x < 0)
    (h4 : hyperbolicPlaneFiniteLattice.obj.obj.pairing x x = -4) :
    ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
      (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing x y := by
  have h := pairing_eq_neg_two_or_neg_four_of_two_elementary hev h2e hx hneg
  rcases h with h2 | ⟨h4', hdvd⟩
  · omega
  · exact hdvd

/-- The `∀`-form is the hypothesis the folding chamber theorems take as `hsq`. -/
example
    (hev : ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
      (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing y y)
    (h2e : ∀ x : hyperbolicPlaneFiniteLattice.obj.obj.carrier, x ≠ 0 →
      ∃ (y₁ y₂ : hyperbolicPlaneFiniteLattice.obj.obj.carrier) (c₁ c₂ : ℤ),
        c₁ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₁ +
          c₂ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₂ = 2)
    (ρ : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
    (hρ : ρ ∈ negativeReflectiveRoots hyperbolicPlaneFiniteLattice) :
    hyperbolicPlaneFiniteLattice.obj.obj.pairing ρ ρ = -2 ∨
      (hyperbolicPlaneFiniteLattice.obj.obj.pairing ρ ρ = -4 ∧
        ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
          (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing ρ y) :=
  square_criterion_of_two_elementary hev h2e ρ hρ

/-- The divisibility hypothesis is free at a `(−2)`-vector. -/
example {x : hyperbolicPlaneFiniteLattice.obj.obj.carrier}
    (h : hyperbolicPlaneFiniteLattice.obj.obj.pairing x x = -2) :
    ∃ (y₁ y₂ : hyperbolicPlaneFiniteLattice.obj.obj.carrier) (c₁ c₂ : ℤ),
      c₁ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₁ +
        c₂ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₂ = 2 :=
  div_two_of_square_neg_two h

/-- And the rule needs it only at the vector in question. -/
example
    (hev : ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
      (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing y y)
    {x : hyperbolicPlaneFiniteLattice.obj.obj.carrier}
    (hdiv : ∃ (y₁ y₂ : hyperbolicPlaneFiniteLattice.obj.obj.carrier) (c₁ c₂ : ℤ),
      c₁ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₁ +
        c₂ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₂ = 2)
    (hx : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj x)
    (hneg : hyperbolicPlaneFiniteLattice.obj.obj.pairing x x < 0) :
    hyperbolicPlaneFiniteLattice.obj.obj.pairing x x = -2 ∨
      (hyperbolicPlaneFiniteLattice.obj.obj.pairing x x = -4 ∧
        ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
          (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing x y) :=
  pairing_eq_neg_two_or_neg_four_of_div_at hev hdiv hx hneg

end LeanCategories.Lattices.Valued
