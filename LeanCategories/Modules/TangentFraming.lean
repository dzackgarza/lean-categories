/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Polynomial.Derivation
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

The one tangent object realized here is the **affine line** `𝔸¹_R`, whose tangent module is the
module `Derivation R R[X] R[X]` of vector fields: it is free of rank one, so it carries a framing
(`affineLineTangent_isFraming`). What is still missing is the sheaf-level dictionary: no tangent
sheaf of a manifold or of an arbitrary scheme is constructed here, and the affine framing above is
stated through `ModuleCat`, not through the tilde equivalence between `R[X]`-modules and sheaves of
modules on `Spec R[X]`.
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

section AffineLine

open Polynomial LeanCategories.Modules.AugmentedGradedObject

variable (R : Type u) [CommRing R]

/-- The tangent module of the affine line `𝔸¹_R`: the module of `R`-derivations `R[X] ⟶ R[X]`, i.e.
the module of vector fields on `𝔸¹_R`. -/
abbrev AffineLineTangent := Derivation R R[X] R[X]

/-- The tangent module of the affine line is free of rank one: a derivation of `R[X]` is determined
by its value at `X` (`Polynomial.derivation_ext`), and `Polynomial.mkDerivation` inverts evaluation
(`Polynomial.mkDerivation_X`). -/
noncomputable def affineLineTangentEquiv : AffineLineTangent R ≃ₗ[R[X]] R[X] where
  toFun D := D Polynomial.X
  invFun a := Polynomial.mkDerivation R a
  map_add' D D' := rfl
  map_smul' b D := by simp
  left_inv D := Polynomial.derivation_ext (by simp)
  right_inv a := by simp

/-- The framing of the tangent module of the affine line: the free module of rank one mapped onto
the derivations by the comparison above. -/
noncomputable def affineLineTangentIso :
    ModuleCat.of R[X] R[X] ≅ ModuleCat.of R[X] (AffineLineTangent R) :=
  (LinearEquiv.toModuleIso (affineLineTangentEquiv R)).symm

/-- The affine line is parallelizable: its tangent module carries a framing in the module case. -/
theorem affineLineTangent_isFraming :
    (oneTerm R[X] (ModuleCat.of R[X] R[X]) (ModuleCat.of R[X] (AffineLineTangent R))
      (affineLineTangentIso R).hom).IsFraming :=
  (oneTerm_isFraming_iff (R := R[X]) _).mpr (affineLineTangentIso R).isIso_hom

end AffineLine

end LeanCategories.Modules
