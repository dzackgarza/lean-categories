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
      ⟨BilinModuleCat.linearEquivOfIso ((isLattice R R).ι.mapIso e.asIso),
        (by
          intro x y
          exact BilinModuleCat.linearEquivOfIso_pairing ((isLattice R R).ι.mapIso e.asIso) x y)⟩
    invFun := fun g ↦
      .of ((isLattice R R).fullyFaithfulι.preimageIso
        (BilinModuleCat.OrthogonalGroup.toIso g))
    left_inv := by
      intro e
      apply CategoryTheory.Aut.ext
      apply CategoryTheory.Iso.ext
      apply (isLattice R R).fullyFaithfulι.map_injective
      rw [CategoryTheory.Functor.FullyFaithful.preimageIso_hom]
      rw [CategoryTheory.Functor.FullyFaithful.map_preimage]
      ext x
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

/-! ## The orthogonal-sum map of orthogonal groups

For lattices `L₁`, `L₂`, the orthogonal sum of isometries is a group morphism
`O(L₁) × O(L₂) →* O(L₁ ⊕ L₂)`, injective because the two components are recovered by evaluating
on the two summands. The general statement — for a pairing that is the sum of two coordinate
pairings, with no nondegeneracy, symmetry or finiteness hypothesis — is
`BilinModuleCat.prodCongrHom` in `Modules/Bilinear/Valued/OrthogonalSum.lean`; the declarations
here are its instantiation at `orthogonalSumBilinMap`, whose pairing is
`orthogonalSum_pairing` (`Lattices/Valued/Constructions.lean`).
-/

section OrthogonalSum

variable {W : Type u} [AddCommGroup W] [Module R W]

/-- The orthogonal-sum map `O(L₁) × O(L₂) →* O(L₁ ⊕ L₂)` of lattices over `R`: the
block-diagonal isometry built from the two factors. -/
noncomputable def orthogonalSumGroupHom (L₁ L₂ : LatticeCat R W) :
    BilinModuleCat.OrthogonalGroup L₁.obj × BilinModuleCat.OrthogonalGroup L₂.obj →*
      BilinModuleCat.OrthogonalGroup (orthogonalSum L₁ L₂).obj :=
  BilinModuleCat.prodCongrHom (orthogonalSumBilinMap L₁.obj L₂.obj) (fun _ _ => rfl)

/-- The orthogonal-sum map of lattices is injective. -/
theorem orthogonalSumGroupHom_injective (L₁ L₂ : LatticeCat R W) :
    Function.Injective (orthogonalSumGroupHom L₁ L₂) :=
  BilinModuleCat.prodCongrHom_injective _ _

end OrthogonalSum

/-- The orthogonal-sum map `O(L₁) × O(L₂) →* O(L₁ ⊕ L₂)` of integral lattices. -/
noncomputable def integralOrthogonalSumGroupHom (L₁ L₂ : IntegralLatticeCat R) :
    OrthogonalGroup L₁ × OrthogonalGroup L₂ →* OrthogonalGroup (orthogonalSum L₁ L₂) :=
  BilinModuleCat.prodCongrHom (orthogonalSumBilinMap L₁.obj L₂.obj) (fun _ _ => rfl)

/-- The orthogonal-sum map of integral lattices is injective: an element of `O(L₁ ⊕ L₂)` that is
block diagonal in the two summands is determined by its two blocks. -/
theorem integralOrthogonalSumGroupHom_injective (L₁ L₂ : IntegralLatticeCat R) :
    Function.Injective (integralOrthogonalSumGroupHom L₁ L₂) :=
  BilinModuleCat.prodCongrHom_injective _ _

/-! ## Products of subgroups of orthogonal groups

For subgroups `P₁ ≤ O(L₁)` and `P₂ ≤ O(L₂)`, the product `P₁ × P₂` is a subgroup of
`O(L₁) × O(L₂)`; its image under the orthogonal-sum map is a subgroup of `O(L₁ ⊕ L₂)`, and the map
restricts to a group isomorphism `P₁ × P₂ ≃* (P₁ × P₂).map` onto it. This is the consumer item
"products of subgroups of lattice orthogonal groups" of lean-categories#91.
-/

/-- The image of a product of subgroups of `O(L₁)` and `O(L₂)` in `O(L₁ ⊕ L₂)`. -/
noncomputable def orthogonalSumSubgroup (L₁ L₂ : IntegralLatticeCat R)
    (P₁ : Subgroup (OrthogonalGroup L₁)) (P₂ : Subgroup (OrthogonalGroup L₂)) :
    Subgroup (OrthogonalGroup (orthogonalSum L₁ L₂)) :=
  (P₁.prod P₂).map (integralOrthogonalSumGroupHom L₁ L₂)

/-- Membership in the product subgroup: an element is the image of a pair of elements of the two
factor subgroups. -/
theorem mem_orthogonalSumSubgroup (L₁ L₂ : IntegralLatticeCat R)
    (P₁ : Subgroup (OrthogonalGroup L₁)) (P₂ : Subgroup (OrthogonalGroup L₂))
    (g : OrthogonalGroup (orthogonalSum L₁ L₂)) :
    g ∈ orthogonalSumSubgroup L₁ L₂ P₁ P₂ ↔
      ∃ g₁ ∈ P₁, ∃ g₂ ∈ P₂, integralOrthogonalSumGroupHom L₁ L₂ (g₁, g₂) = g := by
  rw [orthogonalSumSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨g₁, g₂⟩, hg, hfg⟩
    exact ⟨g₁, (Subgroup.mem_prod.mp hg).1, g₂, (Subgroup.mem_prod.mp hg).2, hfg⟩
  · rintro ⟨g₁, h₁, g₂, h₂, hfg⟩
    exact ⟨(g₁, g₂), Subgroup.mem_prod.mpr ⟨h₁, h₂⟩, hfg⟩

/-- The product `P₁ × P₂` of the two factor subgroups is isomorphic to its image in
`O(L₁ ⊕ L₂)`: the orthogonal-sum map is injective, so it restricts to a bijection onto the image
and the product structure is that of `P₁ × P₂`. -/
noncomputable def orthogonalSumSubgroupMulEquiv (L₁ L₂ : IntegralLatticeCat R)
    (P₁ : Subgroup (OrthogonalGroup L₁)) (P₂ : Subgroup (OrthogonalGroup L₂)) :
    P₁.prod P₂ ≃* orthogonalSumSubgroup L₁ L₂ P₁ P₂ :=
  Subgroup.equivMapOfInjective _ _ (integralOrthogonalSumGroupHom_injective L₁ L₂)

/-- The restricted isomorphism is the orthogonal-sum map on elements. -/
@[simp]
theorem orthogonalSumSubgroupMulEquiv_apply (L₁ L₂ : IntegralLatticeCat R)
    (P₁ : Subgroup (OrthogonalGroup L₁)) (P₂ : Subgroup (OrthogonalGroup L₂))
    (g : P₁.prod P₂) :
    (orthogonalSumSubgroupMulEquiv L₁ L₂ P₁ P₂ g : OrthogonalGroup (orthogonalSum L₁ L₂)) =
      integralOrthogonalSumGroupHom L₁ L₂ (g : OrthogonalGroup L₁ × OrthogonalGroup L₂) :=
  rfl

end LeanCategories.Lattices.Valued
