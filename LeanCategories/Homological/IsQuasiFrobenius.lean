/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Quasi-Frobenius rings

Weibel, *An Introduction to Homological Algebra*, Definition 4.2.3 (p. 95):

> A ring `R` is *quasi-Frobenius* if it is (left and right) noetherian and
> `R` is an injective (left and right) `R`-module.

Left injective: `Module.Injective R R`.
Right injective: `Module.Injective Rᵐᵒᵖ R`, where the right module structure on `R`
is given by `Semiring.toOppositeModule` (i.e. `rᵐᵒᵖ • x = x * r`).
-/

@[expose] public section

namespace LeanCategories.Homological

/-- A ring `R` is *quasi-Frobenius* if it is both left and right Noetherian,
and is an injective module over itself on both sides (Weibel, Definition 4.2.3). -/
def IsQuasiFrobenius (R : Type*) [Ring R] : Prop :=
  IsNoetherianRing R ∧ IsNoetherianRing Rᵐᵒᵖ ∧
    Module.Injective R R ∧ Module.Injective Rᵐᵒᵖ R

namespace IsQuasiFrobenius

/-- Every division ring is quasi-Frobenius:
- `IsSemisimpleRing R` holds for any division ring,
  giving `IsNoetherianRing R` and `IsNoetherianRing Rᵐᵒᵖ`
  (via `IsSemisimpleRing.isNoetherianRing` in `RingTheory.FiniteLength`).
- All modules over a semisimple ring are injective,
  yielding `Module.Injective R R` and `Module.Injective Rᵐᵒᵖ R`
  via `Module.injective_of_isSemisimpleRing`. -/
theorem of_divisionRing (R : Type*) [DivisionRing R] : IsQuasiFrobenius R :=
  ⟨inferInstance, inferInstance,
    Module.injective_of_isSemisimpleRing R R,
    Module.injective_of_isSemisimpleRing Rᵐᵒᵖ R⟩

end IsQuasiFrobenius

end LeanCategories.Homological
