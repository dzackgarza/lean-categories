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

end LeanCategories.Lattices.Valued
