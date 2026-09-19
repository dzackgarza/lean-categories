/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Induced

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

noncomputable abbrev inducedRepresentationData
    {k : Type u} [CommRing k] {G : Type v} [Group G]
    (H : Subgroup G) (V : Rep k H) : Rep k G :=
  Rep.ind H.subtype V

end LeanCategories.Algebra
