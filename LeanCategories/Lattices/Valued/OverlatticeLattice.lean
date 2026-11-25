/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Gluing

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R}

/-!
# An integral overlattice is an integral lattice

`Overlattice R L` (`Gluing.lean`) is a submodule `M.carrier ≤ RationalSpan R L` between the
integral image of `L` and its metric dual, with `IsIntegralSubmodule`: every pairing of two of its
vectors lands in `R`. What the gluing construction never built is the lattice that `M` *is*: an
`IntegralLatticeCat R` whose carrier is `M.carrier` and whose form is the restriction of
`rationalizedForm R L`. Without it there is no `A_M = M^∨/M`, which is why #26's result 3
(`A_M ≅ Γ^⊥/Γ`) could not be stated.

The construction is in two steps. `Overlattice.pairing` reads `rationalizedForm R L x y`, an element
of `R`'s image in `Frac(R)`, back in `R` — possible because `algebraMap R (Frac R)` is injective, so
the witness integrality gives is unique — and `Overlattice.lattice` assembles the
`IntegralLatticeCat` from it. The one thing an overlattice does not supply by itself is
`Module.Projective R ↥M.carrier`, which `Overlattice.lattice` takes as an instance argument;
`Overlattice.projective_of_pid` discharges it over a principal ideal domain from finiteness of `L`
and torsion-freeness of the carrier, which is where a `ℤ`-basis of `M` comes from
(`Overlattice.exists_basis_gram`).

## Provenance

No Mathlib statement turns a submodule of a rational span into a lattice object, and TauCeti's
lattices are not objects of this site either: `TauCeti.IntegralLattice V` is a submodule of a fixed
`ℚ`-vector space with no projectivity field, so the overlattice *is* a lattice there for free and
nothing needed porting. The gap here is the `Module.Projective` field of `LatticeCat`'s object
property (`Basic.lean:39`), and the answers are this repository's own `Overlattice` API.
-/

namespace Overlattice

variable (M : Overlattice R L)

/-! ## The integral pairing of an overlattice -/

/-- The ambient form restricted to an integral overlattice, read back in `R`. The witness is the
one `IsIntegralSubmodule` supplies, and it is unique because `algebraMap R (Frac R)` is
injective. -/
noncomputable def pairing (x y : ↥M.carrier) : R :=
  (Submodule.mem_one.mp (M.2.2 x.2 y.1 y.2)).choose

/-- The defining property of the overlattice pairing: it is the ambient rationalized form. -/
theorem algebraMap_pairing (x y : ↥M.carrier) :
    algebraMap R (FractionRing R) (M.pairing x y) =
      rationalizedForm R L (x : RationalSpan R L) (y : RationalSpan R L) :=
  (Submodule.mem_one.mp (M.2.2 x.2 y.1 y.2)).choose_spec

theorem pairing_add_left (x x' y : ↥M.carrier) :
    M.pairing (x + x') y = M.pairing x y + M.pairing x' y := by
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [map_add, M.algebraMap_pairing, M.algebraMap_pairing, M.algebraMap_pairing,
    show ((x + x' : ↥M.carrier) : RationalSpan R L) = (x : RationalSpan R L) + (x' : _) from rfl,
    LinearMap.map_add, LinearMap.add_apply]

theorem pairing_add_right (x y y' : ↥M.carrier) :
    M.pairing x (y + y') = M.pairing x y + M.pairing x y' := by
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [map_add, M.algebraMap_pairing, M.algebraMap_pairing, M.algebraMap_pairing,
    show ((y + y' : ↥M.carrier) : RationalSpan R L) = (y : RationalSpan R L) + (y' : _) from rfl,
    LinearMap.map_add]

theorem pairing_smul_left (c : R) (x y : ↥M.carrier) :
    M.pairing (c • x) y = c * M.pairing x y := by
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [map_mul, M.algebraMap_pairing, M.algebraMap_pairing,
    show ((c • x : ↥M.carrier) : RationalSpan R L) = c • (x : RationalSpan R L) from rfl,
    LinearMap.BilinForm.smul_left_of_tower, Algebra.smul_def]

theorem pairing_smul_right (c : R) (x y : ↥M.carrier) :
    M.pairing x (c • y) = c * M.pairing x y := by
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [map_mul, M.algebraMap_pairing, M.algebraMap_pairing,
    show ((c • y : ↥M.carrier) : RationalSpan R L) = c • (y : RationalSpan R L) from rfl,
    LinearMap.BilinForm.smul_right_of_tower, Algebra.smul_def]

theorem pairing_comm (x y : ↥M.carrier) : M.pairing x y = M.pairing y x := by
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [M.algebraMap_pairing, M.algebraMap_pairing, rationalizedForm_isSymmetric]

/-- The integral pairing of an overlattice, as an `R`-bilinear map. -/
noncomputable def bilinMap : LinearMap.BilinMap R ↥M.carrier R :=
  LinearMap.mk₂ R M.pairing (fun x x' y => M.pairing_add_left x x' y)
    (fun c x y => by rw [M.pairing_smul_left, smul_eq_mul])
    (fun x y y' => M.pairing_add_right x y y')
    (fun c x y => by rw [M.pairing_smul_right, smul_eq_mul])

/-- The bilinear form of an overlattice. -/
noncomputable abbrev bilinForm : LinearMap.BilinForm R ↥M.carrier := M.bilinMap

/-! ## The lattice object -/

/-- The `R`-valued bilinear form of an overlattice as a `BilinModuleCat` object on the
overlattice's own carrier. -/
noncomputable def bilinObject : BilinModuleCat R R :=
  BilinModuleCat.ofBilinMap (W := R) (M := ↥M.carrier) M.bilinMap

@[simp] theorem bilinObject_pairing (x y : ↥M.carrier) :
    M.bilinObject.pairing x y = M.pairing x y := rfl

theorem bilinObject_isSymmetric : M.bilinObject.IsSymmetric := M.pairing_comm

/-- **An integral overlattice is an integral lattice.** The carrier is the overlattice's own
submodule, the form is the restriction of the ambient rationalized form read in `R`, and the only
input an overlattice does not supply is projectivity of its carrier. -/
noncomputable def lattice [Module.Projective R ↥M.carrier] : IntegralLatticeCat R :=
  ⟨M.bilinObject, ‹Module.Projective R ↥M.carrier›, M.bilinObject_isSymmetric⟩

@[simp] theorem lattice_pairing [Module.Projective R ↥M.carrier] (x y : ↥M.carrier) :
    (M.lattice).obj.pairing x y = M.pairing x y := rfl

/-! ## Projectivity: finiteness and torsion-freeness

`M.carrier` is a submodule of the metric dual of `L`, so it is finite as soon as `L` is, and it is
torsion-free because it sits inside a `Frac(R)`-module. Over a principal ideal domain those two
give freeness by `Module.free_of_finite_type_torsion_free'`, hence projectivity. -/

theorem le_dualSubmodule : M.carrier ≤ (rationalizedForm R L).dualSubmodule M.carrier := M.2.2

/-- The ambient metric dual of an overlattice: the vectors pairing integrally with all of `M`. -/
noncomputable def dualSubmodule : Submodule R (RationalSpan R L) :=
  (rationalizedForm R L).dualSubmodule M.carrier

theorem carrier_le_dualSubmodule : M.carrier ≤ M.dualSubmodule := M.le_dualSubmodule

theorem dualSubmodule_le_metricDual : M.dualSubmodule ≤ metricDual R L := by
  intro x hx
  rw [metricDual, LinearMap.BilinForm.mem_dualSubmodule]
  rintro y ⟨l, rfl⟩
  exact hx _ (M.2.1 (LinearMap.mem_range_self (toRationalSpan R L) l))

theorem isTorsionFree_carrier : Module.IsTorsionFree R ↥M.carrier := by
  haveI hA : Module.IsTorsionFree R (RationalSpan R L) :=
    Module.IsTorsionFree.trans_faithfulSMul R (FractionRing R) (RationalSpan R L)
  refine ⟨fun r hr x y h => ?_⟩
  exact Subtype.ext (hA.isSMulRegular hr (congrArg Subtype.val h))

/-- A submodule of the metric dual of a lattice is a finite module: it is the pullback of a
submodule of the metric dual, which is Noetherian as soon as it is finite. -/
theorem finite_of_le_metricDual [IsNoetherian R (metricDual R L)]
    {P : Submodule R (RationalSpan R L)} (hP : P ≤ metricDual R L) : Module.Finite R ↥P :=
  Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hP)

theorem moduleFinite_carrier [IsNoetherianRing R] [Module.Finite R L.obj.carrier]
    (hL : IsFractionFieldPerfect R L) : Module.Finite R ↥M.carrier := by
  haveI : Module.Finite R L.obj.valueDual := inferInstance
  haveI : Module.Finite R (metricDual R L) :=
    Module.Finite.equiv (rieszMetricDualEquiv R L hL)
  haveI : IsNoetherian R (metricDual R L) :=
    isNoetherian_of_isNoetherianRing_of_finite R (metricDual R L)
  exact finite_of_le_metricDual M.le_metricDual

/-- A finitely generated torsion-free module over a principal ideal domain is free: the PID
instance of `Module.free_of_finite_type_torsion_free'`, applied with its two instances named so
that it can be used where instance search does not reach. -/
theorem free_of_finite_torsionFree [IsPrincipalIdealRing R]
    (hFin : Module.Finite R ↥M.carrier) (hTF : Module.IsTorsionFree R ↥M.carrier) :
    Module.Free R ↥M.carrier :=
  @Module.free_of_finite_type_torsion_free' R _ ↥M.carrier _ _ _ _ hFin hTF

/-- **Over a principal ideal domain, an overlattice of a finite lattice is a projective lattice.**
Finiteness comes from the metric dual, torsion-freeness from the rational span, and freeness from
`Module.free_of_finite_type_torsion_free'`. -/
theorem projective_of_pid [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R L.obj.carrier] (hL : IsFractionFieldPerfect R L) :
    Module.Projective R ↥M.carrier :=
  @Module.Projective.of_free R _ ↥M.carrier _ _
    (M.free_of_finite_torsionFree (M.moduleFinite_carrier hL) M.isTorsionFree_carrier)

/-- **The lattice of an overlattice over a principal ideal domain**, with projectivity
discharged. -/
noncomputable def latticeOfPID [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R L.obj.carrier] (hL : IsFractionFieldPerfect R L) : IntegralLatticeCat R :=
  letI := M.projective_of_pid hL
  M.lattice

@[simp] theorem latticeOfPID_pairing [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R L.obj.carrier] (hL : IsFractionFieldPerfect R L) (x y : ↥M.carrier) :
    (M.latticeOfPID hL).obj.pairing x y = M.pairing x y := rfl

/-! ## The basis and the Gram matrix

Over a PID the carrier is free of finite rank, so it has a basis; in that basis the Gram matrix of
the overlattice's form has entries `M.pairing (b i) (b j)`, i.e. exactly the ambient
`rationalizedForm R L` values read back in `R` by `algebraMap_pairing`. -/

/-- **A `Fin n`-basis of an overlattice's carrier**, from
`Module.basisOfFiniteTypeTorsionFree'`, with its Gram matrix. The basis is a basis of `M` inside
`Frac(R) ⊗ L`; it is obtained abstractly (the Smith-normal-form machinery of Mathlib's
`FreeModule/PID.lean` produces it from no data about `M`), not by extracting vectors from the
ambient space. -/
theorem exists_basis_gram [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R L.obj.carrier] (hL : IsFractionFieldPerfect R L) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) R ↥M.carrier),
      ∀ i j, LinearMap.BilinForm.toMatrix b M.bilinForm i j = M.pairing (b i) (b j) := by
  obtain ⟨n, b⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ ↥M.carrier _ _ _ _
    (M.moduleFinite_carrier hL) M.isTorsionFree_carrier
  exact ⟨n, b, fun i j => LinearMap.BilinForm.toMatrix_apply b M.bilinForm i j⟩

end Overlattice

end LeanCategories.Lattices.Valued
