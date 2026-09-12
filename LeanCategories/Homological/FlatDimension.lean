/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.NoncommutativeTensor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Data.ENat.Lattice

/-!
# Flat dimension over an associative ring

Weibel, *An Introduction to Homological Algebra* (1994), Definition 4.1.1,
§4.1, pp. 91--94 (FC05-C04-U001).

For a right `R`-module `A`, its flat dimension is the minimum length of a flat
resolution, or infinity if no finite flat resolution exists.  Projective and
injective dimensions are already owned by Mathlib; this file supplies the missing
flat-resolution definition at Weibel's arbitrary-associative-ring generality.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe u v

/-- A flat resolution of a right module over an arbitrary associative ring. -/
structure FlatResolution (R : Type u) [Ring R] (A : ModuleCat.{v} Rᵐᵒᵖ) where
  /-- The resolving chain complex. -/
  complex : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ
  /-- Every term is flat. -/
  flat : ∀ n, IsFlatRightModule R (complex.X n)
  /-- Homology objects of the resolution exist. -/
  [hasHomology : ∀ i, complex.HasHomology i]
  /-- Augmentation to the module concentrated in degree zero. -/
  π : complex ⟶ (ChainComplex.single₀ (ModuleCat.{v} Rᵐᵒᵖ)).obj A
  /-- The augmentation is a quasi-isomorphism. -/
  quasiIso : QuasiIso π := by infer_instance

attribute [instance] FlatResolution.hasHomology FlatResolution.quasiIso

namespace FlatResolution

/-- A flat resolution has length at most `n` when all terms above degree `n` vanish. -/
def HasLengthLE {R : Type u} [Ring R] {A : ModuleCat.{v} Rᵐᵒᵖ}
    (P : FlatResolution R A) (n : ℕ) : Prop :=
  ∀ i, n < i → IsZero (P.complex.X i)

end FlatResolution

/-- A right module has flat dimension at most `n` when it admits a flat resolution
of length at most `n`. -/
def HasFlatDimensionLE (R : Type u) [Ring R] (A : ModuleCat.{v} Rᵐᵒᵖ) (n : ℕ) : Prop :=
  Nonempty {P : FlatResolution R A // P.HasLengthLE n}

/-- The flat dimension of a right `R`-module: the minimum finite flat-resolution
length, or `⊤` when no finite flat resolution exists. -/
noncomputable def flatDimension (R : Type u) [Ring R]
    (A : ModuleCat.{v} Rᵐᵒᵖ) : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∃ n : ℕ, d = n ∧ HasFlatDimensionLE R A n}

end LeanCategories.Homological
