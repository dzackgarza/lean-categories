/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import LeanCategories.Modules.AugmentedObjects

/-!
# Tangent framings: `O_X^{⊕n} ⟶ T_X` as an isomorphism of sheaves of modules

FOUNDATIONS.md Remark 13.12, and the tangent-sheaf clause of the acceptance conditions of
dzackgarza/lean-categories#62.

A framing of a bundle is a chosen isomorphism of sheaves of `O_X`-modules

`O_X^{⊕n} ⟶ T_X`,

equivalently a bundle isomorphism `X × k^n ⟶ T X`. It is the length-zero free-resolution case of the
general construction in `LeanCategories.Modules.AugmentedObjects`, read in the category
`SheafOfModules R` of sheaves of `O_X`-modules over a ringed site: the selected augmented object is
`O_X^{⊕n} --φ--> T_X` alone, and `IsFraming` of it is exactly `IsIso φ` because no chosen term above
degree zero remains. Applying global sections afterwards produces a module map, but that map is a
consequence of the sheaf datum and not the definition, which is why the definition is stated here
in `SheafOfModules R` rather than in `ModuleCat`.

`FreeSheaf` is Mathlib's `SheafOfModules.free`, the coproduct of `n` copies of the structure sheaf.
The tangent sheaf `T_X` itself is *data* here: no tangent sheaf of a manifold or scheme is
constructed in this file, so the nontrivial specimen "the tangent sheaf of `X` is free of rank `n`"
does not exist here; `isTangentFraming_free` is the trivial, parallelizable instance.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories.Modules

universe u v

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  (R : Sheaf J RingCat.{u})

/-- The free sheaf of `O_X`-modules of rank `n`, written `O_X^{⊕n}`: the coproduct of `n` copies of
the structure sheaf in `SheafOfModules R`. -/
noncomputable abbrev FreeSheaf (n : ℕ) : SheafOfModules.{u} R :=
  SheafOfModules.free (ULift.{u} (Fin n))

/-- A **tangent framing** of a sheaf of `O_X`-modules `T` (FOUNDATIONS Remark 13.12): a chosen
isomorphism of sheaves of `O_X`-modules `O_X^{⊕n} ⟶ T`.

This is the framing condition of the general construction read at `SheafOfModules R`; it is a
statement in the category of sheaves of modules, not about the module of global sections and not
about a chosen trivialization of a total space. -/
def IsTangentFraming {n : ℕ} (T : SheafOfModules.{u} R)
    (φ : FreeSheaf (J := J) R n ⟶ T) : Prop :=
  IsIso φ

/-- The parallelizable case: where the tangent sheaf is the free sheaf `O_X^{⊕n}` itself, the
identity is a chosen trivialization, hence a tangent framing. -/
theorem isTangentFraming_free (n : ℕ) :
    IsTangentFraming R (FreeSheaf (J := J) R n) (𝟙 _) := by
  change IsIso (𝟙 (FreeSheaf (J := J) R n))
  infer_instance

/-- A tangent framing is an isomorphism of `O_X`-module sheaves; this is the whole content of the
condition, and it mentions no sections. -/
theorem tangentFraming_iff_isIso {n : ℕ} (T : SheafOfModules.{u} R)
    (φ : FreeSheaf (J := J) R n ⟶ T) :
    IsTangentFraming R T φ ↔ IsIso φ := Iff.rfl

end Site

end LeanCategories.Modules
