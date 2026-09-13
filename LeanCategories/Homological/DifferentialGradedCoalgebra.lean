/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.PrimitiveCoalgebraElements
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Graded and differential graded coalgebras

Weibel, *An Introduction to Homological Algebra* (1994), Definitions and
construction 9.10.8, pp. 362--368 (FC05-C09-U162).

The source uses the diagonal coalgebra on an exterior algebra, graded
coalgebras, and DG-coalgebras whose coproduct and counit are chain maps.  It
also observes that primitive elements form a subcomplex.  The definitions
below record exactly that layer.  The induced coalgebra structure on homology
is result-level and is not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped BigOperators TensorProduct

universe u v

variable (k : Type u) [CommRing k]

/-- Pure homogeneous tensors of total degree `n` in the tensor square of a
graded module. -/
def gradedCoalgebraTensorGenerators
    {H : Type v} [AddCommGroup H] [Module k H]
    (𝓗 : ℤ → Submodule k H) (n : ℤ) : Set (H ⊗[k] H) :=
  {z | ∃ (p q : ℤ) (x y : H), p + q = n ∧ x ∈ 𝓗 p ∧ y ∈ 𝓗 q ∧ z = x ⊗ₜ[k] y}

/-- The total-degree-`n` piece of the tensor square of a graded module. -/
def gradedCoalgebraTensorDegree
    {H : Type v} [AddCommGroup H] [Module k H]
    (𝓗 : ℤ → Submodule k H) (n : ℤ) : Submodule k (H ⊗[k] H) :=
  Submodule.span k (gradedCoalgebraTensorGenerators k 𝓗 n)

/-- A coalgebra structure compatible with an integer grading. -/
structure GradedCoalgebra
    (H : Type v) [AddCommGroup H] [Module k H] [Coalgebra k H]
    (𝓗 : ℤ → Submodule k H) where
  /-- Comultiplication preserves total degree. -/
  comul_mem : ∀ (n : ℤ) {x : H}, x ∈ 𝓗 n →
    Coalgebra.comul (R := k) x ∈ gradedCoalgebraTensorDegree k 𝓗 n
  /-- The counit is concentrated in degree zero. -/
  counit_zero : ∀ (n : ℤ) {x : H}, x ∈ 𝓗 n → n ≠ 0 →
    Coalgebra.counit (R := k) x = 0

/-- A differential graded coalgebra.  The supplied tensor differential is the
usual signed tensor differential on homogeneous pure tensors, and the final
two fields say that comultiplication and counit are chain maps. -/
structure DifferentialGradedCoalgebra
    (H : Type v) [AddCommGroup H] [Module k H] [Coalgebra k H]
    (𝓗 : ℤ → Submodule k H) (G : GradedCoalgebra k H 𝓗) where
  /-- The degree `-1` differential. -/
  d : H →ₗ[k] H
  /-- `d²=0`. -/
  d_sq : d.comp d = 0
  /-- The differential lowers internal degree by one. -/
  d_mem : ∀ (n : ℤ) {x : H}, x ∈ 𝓗 n → d x ∈ 𝓗 (n - 1)
  /-- Differential on the tensor-square complex. -/
  tensorDifferential : (H ⊗[k] H) →ₗ[k] (H ⊗[k] H)
  /-- On homogeneous pure tensors the tensor differential is
  `d(x⊗y)=dx⊗y+(-1)^|x|x⊗dy`. -/
  tensorDifferential_tmul : ∀ (p q : ℤ) {x y : H},
    x ∈ 𝓗 p → y ∈ 𝓗 q →
      tensorDifferential (x ⊗ₜ[k] y) =
        d x ⊗ₜ[k] y + ((p.negOnePow : ℤˣ) : ℤ) • (x ⊗ₜ[k] d y)
  /-- The coproduct is a chain map. -/
  comul_chain : tensorDifferential.comp (Coalgebra.comul (R := k)) =
    (Coalgebra.comul (R := k)).comp d
  /-- The counit is a chain map to the complex concentrated in degree zero. -/
  counit_chain : (Coalgebra.counit (R := k)).comp d = 0

/-- A realization of the diagonal coalgebra structure on an exterior algebra.
The displayed formula on generators is the source construction
`v ↦ v⊗1+1⊗v`. -/
structure ExteriorDiagonalCoalgebraRealization
    (V : Type v) [AddCommGroup V] [Module k V] where
  coalgebra : Coalgebra k (ExteriorAlgebra k V)
  comul_generator : letI := coalgebra; ∀ v : V,
    Coalgebra.comul (R := k) (ExteriorAlgebra.ι k v) =
      ExteriorAlgebra.ι k v ⊗ₜ[k] 1 + 1 ⊗ₜ[k] ExteriorAlgebra.ι k v
  counit_generator : letI := coalgebra; ∀ v : V,
    Coalgebra.counit (R := k) (ExteriorAlgebra.ι k v) = 0

variable {k}
variable {H : Type v} [AddCommGroup H] [Module k H] [Coalgebra k H] [One H]
variable (𝓗 : ℤ → Submodule k H)
variable (G : GradedCoalgebra k H 𝓗)
variable (D : DifferentialGradedCoalgebra k H 𝓗 G)

/-- Degree `n` primitive elements of a graded coalgebra. -/
def gradedPrimitiveDegree (n : ℤ) : Submodule k H :=
  𝓗 n ⊓ primitiveCoalgebraSubmodule k H

/-- Restriction of the DG differential to primitive homogeneous pieces, given
a proof that primitive elements are preserved. -/
def primitiveDifferential
    (h : ∀ (n : ℤ) {x : H}, x ∈ gradedPrimitiveDegree 𝓗 n →
      D.d x ∈ gradedPrimitiveDegree 𝓗 (n - 1))
    (n : ℤ) :
    ModuleCat.of k ↥(gradedPrimitiveDegree 𝓗 n) ⟶
      ModuleCat.of k ↥(gradedPrimitiveDegree 𝓗 (n - 1)) :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨D.d x, h n x.2⟩
      map_add' := fun _ _ => by ext; exact D.d.map_add _ _
      map_smul' := fun _ _ => by ext; exact D.d.map_smul _ _ }

/-- A realization of the primitive-element chain subcomplex of a DG-coalgebra.
Preservation of primitive elements by `d` is supplied explicitly; once it is
known, the differential is the literal restriction of the DG differential.

Source: Weibel, Definitions/construction 9.10.8, pp. 362--368
(FC05-C09-U162). -/
structure PrimitiveSubcomplexRealization where
  preserves : ∀ (n : ℤ) {x : H}, x ∈ gradedPrimitiveDegree 𝓗 n →
    D.d x ∈ gradedPrimitiveDegree 𝓗 (n - 1)
  complex : ChainComplex (ModuleCat k) ℤ
  degreeIso : ∀ n : ℤ,
    complex.X n ≅ ModuleCat.of k ↥(gradedPrimitiveDegree 𝓗 n)
  differential : ∀ n : ℤ,
    (degreeIso n).hom ≫ primitiveDifferential 𝓗 G D preserves n =
      complex.d n (n - 1) ≫ (degreeIso (n - 1)).hom

end LeanCategories.Homological
