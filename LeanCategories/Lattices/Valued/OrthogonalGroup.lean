/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Sublattice
public import LeanCategories.Modules.Bilinear.Valued.OrthogonalGroup

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- The orthogonal group `O(L)`. -/
abbrev OrthogonalGroup (L : IntegralLatticeCat R) :=
  BilinModuleCat.OrthogonalGroup L.obj

/-- The automorphism group of `L` in the category of integral lattices. -/
abbrev LatticeAutomorphismGroup (L : IntegralLatticeCat R) := CategoryTheory.Aut L

/-- The canonical identification `Aut(L) ≃ O(L)`. -/
noncomputable def latticeAutEquivOrthogonalGroup (L : IntegralLatticeCat R) :
    LatticeAutomorphismGroup L ≃* OrthogonalGroup L :=
  { toFun := fun e ↦
      ⟨BilinModuleCat.linearEquivOfIso ((isLattice R R).ι.mapIso e),
        BilinModuleCat.linearEquivOfIso_pairing ((isLattice R R).ι.mapIso e)⟩
    invFun := fun g ↦
      (isLattice R R).fullyFaithfulι.preimageIso
        (BilinModuleCat.OrthogonalGroup.toIso g)
    left_inv := by
      intro e
      apply CategoryTheory.Aut.ext
      apply (isLattice R R).fullyFaithfulι.map_injective
      rfl
    right_inv := by
      intro g
      apply Subtype.ext
      ext x
      rfl
    map_mul' := by
      intro e f
      apply Subtype.ext
      ext x
      rfl }

/-- The orbit of a sublattice carrier under `O(L)`. -/
abbrev submoduleOrbit (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) :=
  MulAction.orbit (OrthogonalGroup L) P

/-- The subgroup of `O(L)` that preserves a sublattice carrier. -/
abbrev submoduleStabilizer (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) :=
  MulAction.stabilizer (OrthogonalGroup L) P

/-- Orthogonal-group elements carry orthogonal complements to orthogonal complements. -/
theorem smul_orthogonalSubmodule (L : IntegralLatticeCat R)
    (g : OrthogonalGroup L) (P : Submodule R L.obj.carrier) :
    g • orthogonalSubmodule L P = orthogonalSubmodule L (g • P) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    rw [mem_orthogonalSubmodule_iff]
    rintro _ ⟨p, hp, rfl⟩
    calc
      L.obj.pairing (g.1 p) (g.1 y) = L.obj.pairing p y :=
        g.property p y
      _ = 0 := (mem_orthogonalSubmodule_iff L P y).mp hy p hp
  · intro x hx
    refine ⟨g⁻¹.1 x, ?_, ?_⟩
    · apply (mem_orthogonalSubmodule_iff L P _).mpr
      intro p hp
      have hgp : g.1 p ∈ g • P := ⟨p, hp, rfl⟩
      have horth := (mem_orthogonalSubmodule_iff L (g • P) x).mp hx
        (g.1 p) hgp
      calc
        L.obj.pairing p (g⁻¹.1 x) =
            L.obj.pairing (g.1 p) (g.1 (g⁻¹.1 x)) :=
          (g.property p (g⁻¹.1 x)).symm
        _ = L.obj.pairing (g.1 p) x := by
          congr 1
          exact smul_inv_smul g x
        _ = 0 := horth
    · simp

/-- Every isometry that preserves a sublattice also preserves its orthogonal complement. -/
theorem submoduleStabilizer_le_orthogonalSubmoduleStabilizer
    (L : IntegralLatticeCat R) (P : Submodule R L.obj.carrier) :
    submoduleStabilizer L P ≤
      submoduleStabilizer L (orthogonalSubmodule L P) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [smul_orthogonalSubmodule, hg]

/-- Orthogonal-group elements carry saturation to saturation. -/
theorem smul_saturation [IsDomain R] (L : IntegralLatticeCat R)
    (g : OrthogonalGroup L) (P : Submodule R L.obj.carrier) :
    g • saturation P = saturation (g • P) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨a, ha, ?_⟩
    exact ⟨a • y, hay, by simp⟩
  · intro x hx
    obtain ⟨a, ha, hax⟩ := hx
    rcases hax with ⟨y, hy, hay⟩
    refine ⟨g⁻¹.1 x, ?_, by simp⟩
    refine ⟨a, ha, ?_⟩
    have hyx : y = a • g⁻¹.1 x := by
      apply g.1.injective
      calc
        g.1 y = a • x := hay
        _ = g.1 (a • g⁻¹.1 x) := by simp
    rw [← hyx]
    exact hy

/-- Primitivity is invariant under the orthogonal-group action. -/
theorem isPrimitiveSubmodule_smul_iff [IsDomain R]
    (L : IntegralLatticeCat R) (g : OrthogonalGroup L)
    (P : Submodule R L.obj.carrier) :
    IsPrimitiveSubmodule (g • P) ↔ IsPrimitiveSubmodule P := by
  rw [isPrimitiveSubmodule_iff_saturation_eq,
    isPrimitiveSubmodule_iff_saturation_eq, ← smul_saturation]
  constructor
  · intro h
    have h' := congrArg (fun Q ↦ g⁻¹ • Q) h
    change g⁻¹ • (g • saturation P) = g⁻¹ • (g • P) at h'
    simpa only [inv_smul_smul] using h'
  · exact congrArg (fun Q ↦ g • Q)

end LeanCategories.Lattices.Valued
