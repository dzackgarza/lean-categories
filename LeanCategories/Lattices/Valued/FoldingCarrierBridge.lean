/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfSigns

/-!
# The carrier bridge from `M^σ` to its ambient lattice (`#116`)

`invariantFixedLattice g` is `formedSublattice L.obj (involutionFixedSubmodule g)`, whose carrier is
definitionally `↥(involutionFixedSubmodule g)`. Definitionally — but Lean will not insert a coercion
from one to the other: writing `(ρ : L.obj.obj.carrier)` for `ρ` at `M^σ`'s carrier fails with

  ρ has type ↑(invariantFixedLattice g).obj.obj.carrier
    but is expected to have type ↑L.obj.obj.carrier

because the ascription triggers a coercion *search* rather than a definitional check. That is why
the ambient-sign composition of `FoldingInvariantChamberOfAmbientSigns` could not even be stated.

This file supplies the bridge explicitly, as a function rather than a coercion:

* `invariantFixedLattice_carrier_eq` — the carrier is the fixed submodule (by `rfl`);
* `invariantCarrierToAmbient` — the map `M^σ → L` it induces, defined through
  `show ↥(involutionFixedSubmodule g) from ρ`, which does elaborate;
* its laws: additive, `ℤ`-linear, and the value on a folded wall family.

With these, statements about the roots of `M^σ` can be phrased in `L` without a coercion.

No source to cite: this is the carrier bookkeeping of the development, not a paper statement. It is
the item recorded as open in `results/issue-116-report.md` ("the carrier of `M^σ` must be presented
in a form that is syntactically the subtype it is definitionally equal to").

## LC-09 record

`rg "invariantCarrierToAmbient|carrier_bridge|carrier_eq"` over the repository gives nothing; the
report's
carrier obstruction is recorded as a failure, never as a definition. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The carrier of the invariant lattice is the fixed submodule** — definitionally, by `rfl`. -/
theorem invariantFixedLattice_carrier_eq (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] :
    (invariantFixedLattice (L := L) g).obj.obj.carrier = ↥(involutionFixedSubmodule g) := rfl

/-- **The bridge from `M^σ` to its ambient lattice**, i.e. the coercion of the fixed submodule read
on the invariant lattice's carrier. It *is* Mathlib's
`Submodule.subtype (involutionFixedSubmodule g)` — the carrier of `M^σ` is definitionally `↥P`, by
`invariantFixedLattice_carrier_eq` — with the
`show ↥P from ρ` spelling because the ascription `(ρ : ↥P)` triggers a coercion *search*, while
`show` triggers a *definitional check*, and only the latter elaborates.

It is **not** `FoldingFixedPartBridge.invariantToAmbient` (the same coercion's `ℝ`-linear extension
to `TensorProduct ℤ ℝ ↥P`); the two names must stay distinct, and this one is the element-level form
the statements about roots use. -/
noncomputable def invariantCarrierToAmbient (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] :
    (invariantFixedLattice (L := L) g).obj.obj.carrier → L.obj.obj.carrier :=
  fun ρ => ((show ↥(involutionFixedSubmodule g) from ρ) : L.obj.obj.carrier)

@[simp] theorem invariantCarrierToAmbient_apply (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (ρ : (invariantFixedLattice (L := L) g).obj.obj.carrier) :
    invariantCarrierToAmbient (L := L) g ρ
      = ((show ↥(involutionFixedSubmodule g) from ρ) : L.obj.obj.carrier) := rfl

/-- The bridge is additive. -/
theorem invariantCarrierToAmbient_add (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (x y : (invariantFixedLattice (L := L) g).obj.obj.carrier) :
    invariantCarrierToAmbient (L := L) g (x + y)
      = invariantCarrierToAmbient (L := L) g x + invariantCarrierToAmbient (L := L) g y := rfl

/-- The bridge commutes with integer multiples. -/
theorem invariantCarrierToAmbient_zsmul (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (k : ℤ) (x : (invariantFixedLattice (L := L) g).obj.obj.carrier) :
    invariantCarrierToAmbient (L := L) g (k • x)
      = k • invariantCarrierToAmbient (L := L) g x := rfl

/-- The bridge sends the folded wall family to the folded vectors: this is what lets a statement
about `M^σ`'s roots be phrased in `L`. -/
theorem invariantCarrierToAmbient_foldedWallFamily (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (i : Fin n) :
    invariantCarrierToAmbient (L := L) g (foldedWallFamily (L := L) g hg R i)
      = foldedVector g (R i) := rfl

end LeanCategories.Lattices.Valued
