/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.ModularGroupPresentation

/-!
# The `GL(2, ℤ)` presentation's completeness (lean-categories#89, item 2)

Item 2's remaining clause is `LeanCategories.ForMathlib.Gl2zPresentationComplete`, the injectivity
of `gl2zToGroup`. It is *not* part of lean-categories#179 (which owns `Sl2zPresentationComplete`),
and this module and its successors are its home.

What is here is step 1 — the `GL` presentation's map factors through the `SL` one on the `SL` part:

* `gl2zToGroup_comp_sl2zInGl`:
  `gl2zToGroup.comp sl2zInGl = toGL.comp sl2zToGroup`;
* `sl2zToGroup_eq_one_of_gl2zToGroup_sl2zInGl`: an `SL` element that dies in `GL` already
  dies in `SL`.

What remains for `Gl2zPresentationComplete`, none of it new mathematics and none of it #179's:

2. the generator-inverting endomorphism `sl2zInv` of the `SL` presentation together with the
   conjugation identity `e * i a * e⁻¹ = i (sl2zInv a)` in the `GL` presentation, which is the only
   place where the relators `e S e⁻¹ S` and `e T e⁻¹ T` have to be used;
3. the normal form `∀ q, ∃ a, ∃ ε, sl2zInGl a * e ^ ε = q`;
4. the assembly, using the uniqueness in `gl2z_isComplement`, which yields
   `Sl2zPresentationComplete → Gl2zPresentationComplete`.

So the clause waits on item 1 only through `Function.Injective sl2zToGroup`; everything else it
needs is the two steps above, and #179 does not deliver them.
-/

@[expose] public section

open scoped MatrixGroups Pointwise

open Matrix Matrix.SpecialLinearGroup

namespace LeanCategories.ForMathlib

open ModularGroup

/-- The `GL(2, ℤ)` presentation's map to `GL(2, ℤ)` factors through the `SL(2, ℤ)` presentation on
the `SL` part. -/
theorem gl2zToGroup_comp_sl2zInGl :
    gl2zToGroup.comp sl2zInGl = SpecialLinearGroup.toGL.comp sl2zToGroup := by
  refine PresentedGroup.ext fun i => ?_
  have h : i = 0 ∨ i = 1 := by
    fin_cases i <;> simp
  rcases h with rfl | rfl
  · simp [sl2zInGl_of, sl2zToGroup_of, gl2zToGroup_of, sl2zGenVal_zero, sl2zGenValInGl_zero,
      gl2zGenVal_zero]
  · simp [sl2zInGl_of, sl2zToGroup_of, gl2zToGroup_of, sl2zGenVal_one, sl2zGenValInGl_one,
      gl2zGenVal_one]

/-- An `SL(2, ℤ)` element of the `GL(2, ℤ)` presentation that dies there already dies in
`SL(2, ℤ)`: the two kernels agree on the `SL` part. -/
theorem sl2zToGroup_eq_one_of_gl2zToGroup_sl2zInGl {a : PresentedGroup sl2zRelators}
    (h : gl2zToGroup (sl2zInGl a) = 1) : sl2zToGroup a = 1 := by
  have h' : SpecialLinearGroup.toGL (sl2zToGroup a) = 1 := by
    rw [← MonoidHom.comp_apply, ← gl2zToGroup_comp_sl2zInGl, MonoidHom.comp_apply]
    exact h
  refine SpecialLinearGroup.toGL_injective ?_
  rw [h', map_one]

end LeanCategories.ForMathlib
