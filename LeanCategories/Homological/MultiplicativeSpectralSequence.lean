/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Multiplicative spectral sequences

Weibel, *An Introduction to Homological Algebra*, Multiplicative Structures 5.2.13, p. 127
(FC05-C05-U014), together with the published corrections to p. 127 lines 14 and 16.

The correction replaces the printed sign `(-1)^p₁` by `(-1)^(p₁+q₁)` and does not claim that the
Leibniz identity propagates automatically to later pages.  Accordingly, a multiplicative structure
below contains a product on every page, the corrected Leibniz identity on every page, and the
condition that each next-page product is the product induced on homology and transported through
the spectral-sequence page isomorphism.  No page-propagation theorem is asserted here.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

variable (C : Type u) [Category.{v, u} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-- A bigraded product on page `r` of a homological spectral sequence, corresponding to the
product `E^r_{p₁q₁} × E^r_{p₂q₂} → E^r_{p₁+p₂,q₁+q₂}` in Weibel 5.2.13, p. 127. -/
abbrev SpectralSequencePageProduct {r₀ : ℤ}
    (E : SpectralSequence C (fun r => ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) r₀)
    (r : ℤ) (hr : r₀ ≤ r) :=
  ∀ i j : ℤ × ℤ,
    (E.page r hr).X i ⊗ (E.page r hr).X j ⟶ (E.page r hr).X (i + j)

/-- The next-page product is induced from the current page product: the current product restricts
to cycles, descends through the homology quotients, and the resulting homology product agrees with
the next-page product after transport by `E.iso`.  This spells out the word *induced* in Weibel's
published correction to Multiplicative Structures 5.2.13, p. 127 line 16. -/
def SpectralSequencePageProduct.IsInduced {r₀ r : ℤ}
    (E : SpectralSequence C (fun s => ComplexShape.up' (⟨-s, s - 1⟩ : ℤ × ℤ)) r₀)
    (hr : r₀ ≤ r) (mul : SpectralSequencePageProduct C E r hr)
    (mulNext : SpectralSequencePageProduct C E (r + 1) (by omega)) : Prop :=
  ∀ i j : ℤ × ℤ,
    ∃ cyclesMul : (E.page r hr).cycles i ⊗ (E.page r hr).cycles j ⟶
        (E.page r hr).cycles (i + j),
    ∃ homologyMul : (E.page r hr).homology i ⊗ (E.page r hr).homology j ⟶
        (E.page r hr).homology (i + j),
      ((E.page r hr).iCycles i ⊗ₘ (E.page r hr).iCycles j) ≫ mul i j =
          cyclesMul ≫ (E.page r hr).iCycles (i + j) ∧
      ((E.page r hr).homologyπ i ⊗ₘ (E.page r hr).homologyπ j) ≫ homologyMul =
          cyclesMul ≫ (E.page r hr).homologyπ (i + j) ∧
      (((E.iso r (r + 1) i (by omega) hr).inv ⊗ₘ
            (E.iso r (r + 1) j (by omega) hr).inv) ≫
          homologyMul ≫ (E.iso r (r + 1) (i + j) (by omega) hr).hom) =
        mulNext i j

/-- A multiplicative structure on a homological spectral sequence in the corrected sense of
Weibel, *An Introduction to Homological Algebra*, Multiplicative Structures 5.2.13, p. 127 and
its published corrections.  Products are explicitly required on every page, each next-page
product is induced from the preceding page, and the corrected Leibniz sign is
`(-1)^(p₁+q₁)`. -/
structure MultiplicativeSpectralSequenceStructure {r₀ : ℤ}
    (E : SpectralSequence C (fun r => ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) r₀) where
  /-- The bigraded product on each page; Weibel 5.2.13, display (*), p. 127. -/
  mul (r : ℤ) (hr : r₀ ≤ r) : SpectralSequencePageProduct C E r hr
  /-- The corrected Leibniz identity from Weibel 5.2.13, display (**), p. 127; the published
  correction changes the exponent from `p₁` to the total degree `p₁+q₁`. -/
  leibniz (r : ℤ) (hr : r₀ ≤ r) (i j : ℤ × ℤ) :
    mul r hr i j ≫
        (E.page r hr).d (i + j) ((i + j) + (⟨-r, r - 1⟩ : ℤ × ℤ)) =
      ((E.page r hr).d i (i + (⟨-r, r - 1⟩ : ℤ × ℤ)) ⊗ₘ 𝟙 ((E.page r hr).X j)) ≫
          mul r hr (i + (⟨-r, r - 1⟩ : ℤ × ℤ)) j ≫
          eqToHom (congrArg ((E.page r hr).X) (show
            (i + (⟨-r, r - 1⟩ : ℤ × ℤ)) + j =
                (i + j) + (⟨-r, r - 1⟩ : ℤ × ℤ) by
              ext <;> simp [add_assoc, add_left_comm, add_comm])) +
        (i.1 + i.2).negOnePow •
          ((𝟙 ((E.page r hr).X i) ⊗ₘ
              (E.page r hr).d j (j + (⟨-r, r - 1⟩ : ℤ × ℤ))) ≫
            mul r hr i (j + (⟨-r, r - 1⟩ : ℤ × ℤ)) ≫
            eqToHom (congrArg ((E.page r hr).X) (show
              i + (j + (⟨-r, r - 1⟩ : ℤ × ℤ)) =
                  (i + j) + (⟨-r, r - 1⟩ : ℤ × ℤ) by
                ext <;> simp [add_assoc])))
  /-- Each later page carries the product induced from the preceding page, as required by the
  published correction to Weibel 5.2.13, p. 127 line 16. -/
  induced (r : ℤ) (hr : r₀ ≤ r) :
    SpectralSequencePageProduct.IsInduced C E hr (mul r hr) (mul (r + 1) (by omega))

end LeanCategories.Homological
