/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.MonCat.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

@[expose] public section

/-!
# The two underlying sets of a ring agree (#53 §9)

A ring reaches sets along its multiplicative port
`Ring → Mon → Semigrp → Magma → Set` and along its additive port
`Ring → AddCommGrp → AddGrp → Grp → Mon → Semigrp → Magma → Set` (the additive group read
multiplicatively by `AddGrpCat.toGrp`). The two ports are different structure — they carry
different operations — but after every operation is forgotten they give the same set and the same
functions: the comparison is the identity natural isomorphism. This is the coherence datum that
identifies the two routes for set-level methods such as cardinality, and only for those.
-/

open CategoryTheory

namespace LeanCategories.Algebra

universe u

/-- The underlying set of a ring, through its multiplicative monoid. -/
abbrev ringCarrierMultiplicative : RingCat.{u} ⥤ Type u :=
  forget₂ RingCat SemiRingCat ⋙ forget₂ SemiRingCat MonCat ⋙ forget₂ MonCat Semigrp ⋙
    forget₂ Semigrp MagmaCat ⋙ forget MagmaCat

/-- The underlying set of a ring, through its additive group read multiplicatively. -/
abbrev ringCarrierAdditive : RingCat.{u} ⥤ Type u :=
  forget₂ RingCat AddCommGrpCat ⋙ forget₂ AddCommGrpCat AddGrpCat ⋙ AddGrpCat.toGrp ⋙
    forget₂ GrpCat MonCat ⋙ forget₂ MonCat Semigrp ⋙ forget₂ Semigrp MagmaCat ⋙ forget MagmaCat

/-- The two underlying sets of a ring are identified by the identity natural isomorphism. -/
def ringCarrierComparison : ringCarrierMultiplicative.{u} ≅ ringCarrierAdditive.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end LeanCategories.Algebra
