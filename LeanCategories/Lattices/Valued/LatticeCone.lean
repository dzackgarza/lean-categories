/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PositiveConeReflections
public import LeanCategories.Lattices.Valued.RootSystem
public import LeanCategories.Lattices.Valued.Signature

/-!
# The positive cone, `O⁺` and the reflection group of an integral lattice

The real-form statements of `PositiveCone` and `PositiveConeReflections` are stated for a real
quadratic form. This file attaches the real form itself to an integral lattice `M`: the quadratic
form `realFormQuadratic M` on `M ⊗ ℝ`, whose signature is `integralSignature M` by definition
(`realFormQuadratic_sigPos`, `realFormQuadratic_sigNeg`, `realFormQuadratic_sigRadical`).

Not yet here: `O(M) → O(M ⊗ ℝ)` and with it `O⁺(M)` as a preimage, `W(M) ≤ O⁺(M)`, and
normality of `W(M)` in `O(M)`. The obstruction is mechanical, not mathematical: the group laws
for the isometry-valued homomorphism compare `Q.IsometryEquiv Q`-applications with `LinearEquiv`
applications, and the coercion between them is an instance projection, which definitional
comparison at reducible transparency does not unfold.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

section RealForm

variable (L : FiniteProjectiveLatticeCat ℤ ℤ)

/-- The **real form** of an integral lattice: its scalar extension to `ℝ`. -/
noncomputable def realForm : FiniteFormCat ℝ ℝ :=
  (finiteProjectiveToFiniteForm ℝ ℝ).obj ((baseChangeFiniteIntegral ℤ ℝ).obj L)

/-- The quadratic form of the real form of an integral lattice. -/
noncomputable def realFormQuadratic : QuadraticForm ℝ (realForm L).obj.carrier :=
  finiteFormQuadraticForm ℝ (realForm L)

theorem realFormQuadratic_sigPos : sigPos (realFormQuadratic L) = (integralSignature L).1 := rfl

theorem realFormQuadratic_sigNeg : sigNeg (realFormQuadratic L) = (integralSignature L).2.1 := rfl

theorem realFormQuadratic_sigRadical :
    Module.finrank ℝ (realFormQuadratic L).radical = (integralSignature L).2.2 := rfl

theorem realFormQuadratic_apply (x : (realForm L).obj.carrier) :
    realFormQuadratic L x = (realForm L).obj.pairing x x := rfl

/-- Isometry equivalences with the same underlying linear equivalence are equal. -/
theorem isometryEquiv_ext {W : Type u} [AddCommGroup W] [Module ℝ W] {Q : QuadraticForm ℝ W}
    {f g : Q.IsometryEquiv Q} (h : (f : W ≃ₗ[ℝ] W) = (g : W ≃ₗ[ℝ] W)) : f = g := by
  cases f
  cases g
  simp_all

/-- **Scalar extension to `ℝ` as a homomorphism `O(M) → O(M ⊗ ℝ)`.** A pairing-preserving linear
equivalence of the real form preserves its quadratic form, so the base change of an isometry of `M`
is an isometry equivalence of `Q`. -/
noncomputable def realFormOrthogonalHom :
    OrthogonalGroup L.obj →* (realFormQuadratic L).IsometryEquiv (realFormQuadratic L) where
  toFun g :=
    QuadraticMap.IsometryEquiv.mk (orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj g).1
      (fun x => (orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj g).2 x x)
  map_one' := by
    apply isometryEquiv_ext
    change ((orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj
      (1 : OrthogonalGroup L.obj)).1 : (realForm L).obj.carrier ≃ₗ[ℝ] _) = (1 : _ ≃ₗ[ℝ] _)
    rw [congrArg Subtype.val (map_one (orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj))]
    rfl
  map_mul' g h := by
    apply isometryEquiv_ext
    change ((orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj (g * h)).1 :
        (realForm L).obj.carrier ≃ₗ[ℝ] _)
      = ((orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj g).1 : _ ≃ₗ[ℝ] _)
        * ((orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj h).1 : _ ≃ₗ[ℝ] _)
    rw [congrArg Subtype.val (map_mul (orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj) g h)]
    rfl

theorem realFormOrthogonalHom_apply (g : OrthogonalGroup L.obj) (x : (realForm L).obj.carrier) :
    realFormOrthogonalHom L g x = (orthogonalGroupBaseChangeHom (R := ℤ) (S := ℝ) L.obj g).1 x :=
  rfl

section Cone

/-- The real form of a finite projective integral lattice is finite-dimensional over `ℝ`. -/
instance realFormFiniteDimensional : FiniteDimensional ℝ (realForm L).obj.carrier :=
  haveI : Module.Finite ℝ (realForm L).obj.carrier := (realForm L).property.1
  inferInstance

/-- **`O⁺(M)`**: the preimage in `O(M)` of the positive-cone stabilizer of `M ⊗ ℝ`, i.e. the
isometries of `M` whose base change preserves each sheet of the positive cone of the real form. -/
noncomputable def latticePositiveConeStabilizer (hpos : (integralSignature L).1 = 1)
    (t : (realForm L).obj.carrier) (ht : 0 < realFormQuadratic L t) :
    Subgroup (OrthogonalGroup L.obj) :=
  MonoidHom.ker
    ((positiveConeSign (realFormQuadratic L) hpos t ht).comp (realFormOrthogonalHom L))

/-- `O⁺(M)` is exactly the preimage of the positive-cone stabilizer of `M ⊗ ℝ`. -/
theorem mem_latticePositiveConeStabilizer_iff (hpos : (integralSignature L).1 = 1)
    (t : (realForm L).obj.carrier) (ht : 0 < realFormQuadratic L t) (g : OrthogonalGroup L.obj) :
    g ∈ latticePositiveConeStabilizer L hpos t ht ↔
      realFormOrthogonalHom L g ∈ positiveConeStabilizer (realFormQuadratic L) hpos t ht :=
  Iff.rfl

/-- **`O⁺(M)` has index at most two in `O(M)`.** -/
theorem latticePositiveConeStabilizer_index_le_two (hpos : (integralSignature L).1 = 1)
    {t : (realForm L).obj.carrier} (ht : 0 < realFormQuadratic L t) :
    (latticePositiveConeStabilizer L hpos t ht).index ≤ 2 := by
  classical
  rw [latticePositiveConeStabilizer, Subgroup.index_ker]
  calc Nat.card ↥(MonoidHom.range
        ((positiveConeSign (realFormQuadratic L) hpos t ht).comp (realFormOrthogonalHom L)))
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- `O⁺(M)` has finite index in `O(M)`. -/
theorem latticePositiveConeStabilizer_finiteIndex (hpos : (integralSignature L).1 = 1)
    {t : (realForm L).obj.carrier} (ht : 0 < realFormQuadratic L t) :
    (latticePositiveConeStabilizer L hpos t ht).FiniteIndex where
  index_ne_zero := by
    classical
    rw [latticePositiveConeStabilizer, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

end Cone

end RealForm

end LeanCategories.Lattices.Valued
