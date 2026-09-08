/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Augmentation of monoid algebras

The coefficient-sum augmentation of a monoid algebra, and its kernel ideal.
This realizes Dummit--Foote FC01-C07-U057 at the more general monoid-algebra
owner supplied by the Sweep-II reference implementation.

The augmentation definition and singleton formula are ported from
`TauCetiProject/TauCeti` commit
`d6214142a5e6403ba4f977246f1fc16418d561e4`,
`TauCeti/Algebra/MonoidAlgebra/Exactness.lean` (Apache-2.0).
The kernel-generation theorem in that reference belongs to Sweep IV.
-/

@[expose] public section

namespace MonoidAlgebra

universe u v

variable (R : Type u) [Ring R]

/-- The coefficient-sum augmentation of a monoid algebra. It sends every
standard basis element to `1` and acts identically on coefficients.

Ported from TauCeti at commit
`d6214142a5e6403ba4f977246f1fc16418d561e4`. -/
noncomputable def augmentation (K : Type v) [Monoid K] : MonoidAlgebra R K →+* R :=
  liftNCRingHom (.id R) 1 fun _ _ ↦ Commute.one_right _

/-- The coefficient-sum augmentation sends a singleton to its coefficient. -/
@[simp]
theorem augmentation_single {K : Type v} [Monoid K] (k : K) (r : R) :
    augmentation R K (single k r) = r := by
  simp [augmentation]

/-- The augmentation ideal is the kernel of the coefficient-sum augmentation. -/
noncomputable def augmentationIdeal (K : Type v) [Monoid K] : Ideal (MonoidAlgebra R K) :=
  RingHom.ker (augmentation R K)

@[simp]
theorem mem_augmentationIdeal {K : Type v} [Monoid K] (x : MonoidAlgebra R K) :
    x ∈ augmentationIdeal R K ↔ augmentation R K x = 0 :=
  RingHom.mem_ker

end MonoidAlgebra
