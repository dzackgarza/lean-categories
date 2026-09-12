/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Central and universal central extensions

Weibel, *An Introduction to Homological Algebra*, §6.9, pp. 198--202
(FC05-C06-U106).

Mathlib already owns short exact group extensions as `GroupExtension`.  This file adds exactly the
two predicates used by Weibel: centrality of the kernel and the initiality condition among central
extensions over the same quotient group.
-/

@[expose] public section

namespace GroupExtension

universe u

variable {N E G : Type u} [Group N] [Group E] [Group G]

/-- A group extension is central when the image of its kernel inclusion lies in the center of the
middle group.

Source: Weibel, §6.9, pp. 198--202 (FC05-C06-U106). -/
def IsCentral (S : GroupExtension N E G) : Prop :=
  S.inl.range ≤ Subgroup.center E

/-- A central extension is universal when it admits a unique homomorphism over `G` to every
central extension of `G`.

The target kernel and middle group are allowed to vary.  The equation
`T.rightHom.comp f = S.rightHom` is precisely the requirement that `f` lie over the identity of
`G`.

Source: Weibel, §6.9, pp. 198--202 (FC05-C06-U106). -/
def IsUniversalCentral (S : GroupExtension N E G) : Prop :=
  S.IsCentral ∧
    ∀ (N' E' : Type u) [Group N'] [Group E'] (T : GroupExtension N' E' G),
      T.IsCentral → ∃! f : E →* E', T.rightHom.comp f = S.rightHom

end GroupExtension
