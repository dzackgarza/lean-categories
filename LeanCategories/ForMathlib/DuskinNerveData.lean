/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary

/-!
# Definition-level Duskin nerve data

Definition-level realization of Kerodon Construction 2.3.1.1, tag 009U.

For a bicategory B, the n-simplices of the Duskin nerve are the strictly
unitary lax functors from the locally discrete bicategory attached to [n]
into B. Reindexing along an ordinal map is precomposition.

Current Mathlib supplies all carriers needed for that prescription:
ordinary ordinal functors lift to pseudofunctors between locally discrete
bicategories, pseudofunctors have underlying lax functors, and lax functors
compose. What is not packaged proof-freely is the assertion that the
precomposition again carries the required strictly unitary structure together
with the functoriality laws needed to install an actual simplicial set.

Sweep III therefore records the exact reindexing graph. No target simplex is
selected, and no simplicial identity or SSet structure is proved.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Bicategory
open scoped Simplicial

namespace LeanCategories.ForMathlib

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

/-- Kerodon's n-simplex carrier for the Duskin nerve. -/
abbrev DuskinSimplexData (n : ℕ) :=
  StrictlyUnitaryLaxFunctor
    (LocallyDiscrete (SimplexCategory.toCat.obj ⦋n⦌)) B

/-- The lax functor induced by an ordinal map, viewed between locally
discrete bicategories. -/
def duskinOrdinalLaxFunctorData {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    LocallyDiscrete (SimplexCategory.toCat.obj ⦋m⦌) ⥤ᴸ
      LocallyDiscrete (SimplexCategory.toCat.obj ⦋n⦌) :=
  ((SimplexCategory.toCat.map φ).toFunctor.toPseudofunctor).toLax

/-- Exact graph of Duskin reindexing by precomposition.

The target simplex tau is related to sigma along φ when the underlying lax
functor of tau is exactly the lax composite of φ with sigma. Existence and
uniqueness of such a strictly unitary lift are result-layer coherence facts. -/
def IsDuskinReindexData {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (sigma : DuskinSimplexData B n) (tau : DuskinSimplexData B m) : Prop :=
  tau.toLaxFunctor =
    LaxFunctor.comp (duskinOrdinalLaxFunctorData φ) sigma.toLaxFunctor

end LeanCategories.ForMathlib
