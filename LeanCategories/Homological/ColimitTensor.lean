/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Tensor products and filtered colimits

Card `E-HAT-3.A-6` and `E-HAT-3.A-2` of the qualifying-exam corpus.  Source:
Hatcher, *Algebraic Topology*, Section 3.A, Exercise 4 (commutation with
direct limits).  Certificate: new-qual-site `proofs/cards/ColimitTensor.lean`
at main `16c09abaa4`.

Hatcher, §3.A exercise 4: `⊗` and `Tor` commute with direct limits.  This
module certifies the `⊗` half for abelian groups, in the form the two cards
use.

The reusable Mathlib fact is the instance `PreservesColimits (tensorLeft A)`
for a closed monoidal category, applied to `ModuleCat ℤ`: `tensorLeft B` is
`B ⊗ -` and preserves colimits, so for any functor `F : J ⥤ ModuleCat ℤ` the
canonical comparison `B ⊗ colim F → colim (B ⊗ F ·)` is an isomorphism.
Nothing here re-implements tensoring or colimits.

The `Tor` half — that `Tor(colim A_α, B) ≅ colim Tor(A_α, B)` — is *not*
certified: it needs Hatcher's Lemma 3A.2 (the comparison theorem, that any
free resolution computes `Tor`), which is not formalized, together with this
colimit fact.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): `tensorLeft_preserves_colimits` (0 corpus hits),
`tensorLeft_colim_iso` (0 corpus hits); local Mathlib has the underlying
instance through `ModuleCat`'s closed monoidal structure.  Route: glue over
Mathlib's instance; the comparison iso is written here.
-/

open CategoryTheory Limits MonoidalCategory

namespace LeanCategories.Homological.ColimitTensor

variable {J : Type*} [Category J] [HasColimitsOfShape J (ModuleCat ℤ)]

/-- Exercise 4 of §3.A, first half, at abelian groups: `B ⊗ -` preserves
colimits. -/
theorem tensorLeft_preserves_colimits (B : ModuleCat ℤ) : PreservesColimits (tensorLeft B) :=
  inferInstance

/-- Exercise 4 of §3.A, first half, at abelian groups: for any functor `F : J ⥤ ModuleCat ℤ`
and any `B`, the tensor product commutes with the colimit,
`B ⊗ colim F ≅ colim (B ⊗ F ·)`.

The witness of colimit preservation is `Nonempty (IsColimit _)`
(`PreservesColimit.preserves`), so it is extracted with `Classical.choice`; the
comparison is the canonical map between two colimit cocones,
`IsColimit.coconePointUniqueUpToIso`.  Both are Mathlib's. -/
noncomputable def tensorLeft_colim_iso (F : J ⥤ ModuleCat ℤ) (B : ModuleCat ℤ) :
    (tensorLeft B).obj (colimit F) ≅ colimit (F ⋙ tensorLeft B) :=
  IsColimit.coconePointUniqueUpToIso
    (Classical.choice (PreservesColimit.preserves (colimit.isColimit F)))
    (colimit.isColimit (F ⋙ tensorLeft B))

end LeanCategories.Homological.ColimitTensor
