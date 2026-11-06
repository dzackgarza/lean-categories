/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantAction
public import LeanCategories.Lattices.Valued.Sublattice
public import LeanCategories.Modules.Bilinear.Valued.Isometry
public import Mathlib.GroupTheory.Index
public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Catalogue.Semantics.Lattices.Valued.CatalogueRegistration

/-!
# The `(L, Γ)` cusp category (#113)

Stage 1 of the lattice pipeline: for an integral lattice `L` and a **finite-index** subgroup
`Γ ⊆ O(L)`, the cusps of `Γ` are the `Γ`-orbits of primitive isotropic sublattices of `L`, by rank:
rank 1 gives the 0-cusps and rank 2 the 1-cusps.

`Modules.Bilinear.Valued.BilinModuleCat.IsFiniteIndexEmbedding` is a bare predicate about a single
embedding. What the class needs is a subgroup of the orthogonal group that carries its finiteness
witness as data, which is `FiniteIndexSubgroup` below, built on Mathlib's `Subgroup.FiniteIndex`.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] {W : Type u} [AddCommGroup W] [Module R W]

/-- A subgroup of `O(L)` together with the witness that it has finite index. The index is a field,
not a separate hypothesis: a consumer of a cusp that does not know the index is finite cannot state
the finiteness results the class exists for. -/
structure FiniteIndexSubgroup (L : IntegralLatticeCat R) where
  /-- The subgroup of the orthogonal group. -/
  toSubgroup : Subgroup (OrthogonalGroup L)
  /-- Its index in `O(L)` is finite. -/
  finiteIndex : toSubgroup.FiniteIndex

namespace FiniteIndexSubgroup

variable {L : IntegralLatticeCat R}

instance : Coe (FiniteIndexSubgroup L) (Subgroup (OrthogonalGroup L)) :=
  ⟨FiniteIndexSubgroup.toSubgroup⟩

@[simp] theorem coe_mk (H : Subgroup (OrthogonalGroup L)) (h : H.FiniteIndex) :
    (⟨H, h⟩ : FiniteIndexSubgroup L).toSubgroup = H := rfl

/-- The whole orthogonal group has finite index in itself: the canonical example. -/
def top (L : IntegralLatticeCat R) : FiniteIndexSubgroup L where
  toSubgroup := ⊤
  finiteIndex := inferInstance

end FiniteIndexSubgroup

/-- A submodule is isotropic when the restricted form vanishes on it. -/
def IsIsotropicSubmodule (L : IntegralLatticeCat R)
    (N : Submodule R L.obj.carrier) : Prop :=
  ∀ x ∈ N, ∀ y ∈ N, LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.asBilinForm
    L.obj x y = 0

/-- A primitive isotropic sublattice of rank `k`: an isotropic submodule of rank `k` that is a
direct summand of the carrier, which is primitivity at module level. Rank 1 gives 0-cusps and rank 2
gives 1-cusps. -/
structure PrimitiveIsotropic (L : IntegralLatticeCat R) (k : ℕ) where
  /-- The underlying submodule. -/
  toSubmodule : Submodule R L.obj.carrier
  /-- The restricted form vanishes. -/
  isotropic : IsIsotropicSubmodule L toSubmodule
  /-- Its rank. -/
  finrank_eq : Module.finrank R toSubmodule = k
  /-- Primitivity: it is a direct summand of the carrier. -/
  complemented : ∃ N' : Submodule R L.obj.carrier, IsCompl toSubmodule N'

namespace PrimitiveIsotropic

variable {L : IntegralLatticeCat R} {k : ℕ}

instance : CoeOut (PrimitiveIsotropic L k) (Submodule R L.obj.carrier) :=
  ⟨PrimitiveIsotropic.toSubmodule⟩

/-- Two primitive isotropic sublattices of the same rank are equal when their submodules are. -/
@[ext] theorem ext {N M : PrimitiveIsotropic L k} (h : N.toSubmodule = M.toSubmodule) : N = M := by
  cases N; cases M; congr

end PrimitiveIsotropic

/-- An object of the cusp category: an integral lattice together with a finite-index subgroup of its
orthogonal group. -/
structure CuspObject where
  /-- The lattice `L`. -/
  lattice : IntegralLatticeCat R
  /-- The finite-index subgroup `Γ ⊆ O(L)`. -/
  gamma : FiniteIndexSubgroup lattice

/-- A morphism of the cusp category: an isometric embedding `L₁ ⟶ L₂` that carries `Γ₁` into `Γ₂`,
i.e. for every `γ ∈ Γ₁` there is `δ ∈ Γ₂` with `f ∘ γ = δ ∘ f`. -/
structure CuspMorphism (X Y : CuspObject (R := R)) where
  /-- The underlying lattice morphism. -/
  hom : X.lattice ⟶ Y.lattice
  /-- Equivariance: every `γ ∈ Γ₁` is matched by some `δ ∈ Γ₂` with `f ∘ γ = δ ∘ f`. -/
  equivariant : ∀ γ ∈ X.gamma.toSubgroup, ∃ δ ∈ Y.gamma.toSubgroup,
    (OrthogonalGroup.asLatticeIso γ).hom ≫ hom = hom ≫ (OrthogonalGroup.asLatticeIso δ).hom

/-- The two spellings of the form agree definitionally: `asBilinForm` is the form of the underlying
formed module. This lets `g.property`, which is stated in `L.obj.pairing`, act on goals stated in
`L.obj.asBilinForm`. -/
theorem IntegralLatticeCat.asBilinForm_apply (L : IntegralLatticeCat R) (a b : L.obj.carrier) :
    L.obj.asBilinForm a b = L.obj.pairing a b := rfl

/-- The action of `O(L)` on submodules, written as `Submodule.map` along the underlying linear
equivalence. This is the form in which the structure of a lattice is preserved. -/
theorem OrthogonalGroup.smul_submodule_eq_map {L : IntegralLatticeCat R} (g : OrthogonalGroup L)
    (P : Submodule R L.obj.carrier) :
    g • P = P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) := rfl

/-- `O(L)` acts on primitive isotropic sublattices of rank `k`: the image of such a sublattice under
an isometry is one again, and the image of a complement is a complement. -/
noncomputable def PrimitiveIsotropic.act {L : IntegralLatticeCat R} {k : ℕ}
    (g : OrthogonalGroup L) (N : PrimitiveIsotropic L k) : PrimitiveIsotropic L k where
  toSubmodule := g • N.toSubmodule
  isotropic := by
    intro x hx y hy
    simp only [OrthogonalGroup.smul_submodule_eq_map, Submodule.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    change L.obj.asBilinForm (g.1 a) (g.1 b) = 0
    rw [IntegralLatticeCat.asBilinForm_apply, g.property, ← IntegralLatticeCat.asBilinForm_apply]
    exact N.isotropic a ha b hb
  finrank_eq := by
    change Module.finrank R ↥(N.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) = k
    rw [LinearEquiv.finrank_map_eq, N.finrank_eq]
  complemented := by
    obtain ⟨q, hq⟩ := N.complemented
    refine ⟨g • q, ?_⟩
    change IsCompl (N.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier))
      (q.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier))
    exact (Submodule.orderIsoMapComap
      (g.1 : L.obj.carrier ≃ₗ[R] L.obj.carrier)).isCompl_iff.mp hq

/-- `O(L)` acts on the primitive isotropic sublattices of rank `k`. -/
noncomputable instance primitiveIsotropicSMul {L : IntegralLatticeCat R} {k : ℕ} :
    SMul (OrthogonalGroup L) (PrimitiveIsotropic L k) :=
  ⟨fun g N => PrimitiveIsotropic.act g N⟩

noncomputable instance primitiveIsotropicMulAction {L : IntegralLatticeCat R} {k : ℕ} :
    MulAction (OrthogonalGroup L) (PrimitiveIsotropic L k) where
  one_smul N := by
    apply PrimitiveIsotropic.ext
    exact one_smul (OrthogonalGroup L) N.toSubmodule
  mul_smul g h N := by
    apply PrimitiveIsotropic.ext
    exact mul_smul g h N.toSubmodule

/-- A subgroup `H ⊆ O(L)`, in particular the finite-index `Γ`, acts on primitive isotropic
sublattices by restriction of scalars along `H → O(L)`. -/
noncomputable instance primitiveIsotropicSubgroupMulAction {L : IntegralLatticeCat R}
    (H : Subgroup (OrthogonalGroup L)) {k : ℕ} : MulAction H (PrimitiveIsotropic L k) :=
  MulAction.compHom (PrimitiveIsotropic L k) (Subgroup.subtype H)

/-- The `Γ`-orbits of primitive isotropic sublattices of rank `k`: `k = 1` gives the 0-cusps,
`k = 2` the 1-cusps. -/
noncomputable def CuspOrbits (L : IntegralLatticeCat R) (Γ : FiniteIndexSubgroup L) (k : ℕ) :
    Type u :=
  MulAction.orbitRel.Quotient Γ.toSubgroup (PrimitiveIsotropic L k)

/-- The `Γ`-orbit of a primitive isotropic sublattice of rank `k`. -/
noncomputable def CuspOrbits.mk {L : IntegralLatticeCat R} (Γ : FiniteIndexSubgroup L) {k : ℕ}
    (N : PrimitiveIsotropic L k) : CuspOrbits L Γ k :=
  Quotient.mk (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropic L k)) N

/-- Incidence between a rank-1 orbit and a rank-2 orbit: some representative line is nested in some
representative plane. -/
noncomputable def CuspIncidence (X : CuspObject (R := R)) : CuspOrbits X.lattice X.gamma 1 →
    CuspOrbits X.lattice X.gamma 2 → Prop :=
  fun c₁ c₂ => ∃ v : PrimitiveIsotropic X.lattice 1,
    CuspOrbits.mk X.gamma v = c₁ ∧ ∃ P : PrimitiveIsotropic X.lattice 2,
      CuspOrbits.mk X.gamma P = c₂ ∧ v.toSubmodule ≤ P.toSubmodule

namespace CuspMorphism

variable {X Y Z : CuspObject (R := R)}

/-- The identity morphism is equivariant for `γ ↦ γ`. -/
def id (X : CuspObject (R := R)) : CuspMorphism X X where
  hom := 𝟙 X.lattice
  equivariant := by
    intro γ hγ
    exact ⟨γ, hγ, by simp⟩

/-- Composition of equivariant embeddings is equivariant: the witnesses compose. -/
def comp (f : CuspMorphism X Y) (g : CuspMorphism Y Z) : CuspMorphism X Z where
  hom := f.hom ≫ g.hom
  equivariant := by
    intro γ hγ
    obtain ⟨δ, hδ, hf⟩ := f.equivariant γ hγ
    obtain ⟨ε, hε, hg⟩ := g.equivariant δ hδ
    exact ⟨ε, hε, by rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]⟩

end CuspMorphism

/-- Two cusp morphisms are equal when their underlying lattice morphisms are: the equivariance
field is a proposition. -/
@[ext] theorem CuspMorphism.ext {X Y : CuspObject (R := R)} {f g : CuspMorphism X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; congr

/-- The cusp category: objects `(L, Γ)`, morphisms `Γ`-equivariant isometric embeddings. -/
instance : Category (CuspObject (R := R)) where
  Hom X Y := CuspMorphism X Y
  id X := CuspMorphism.id X
  comp f g := CuspMorphism.comp f g
  id_comp := by intro X Y f; ext; simp [CuspMorphism.id, CuspMorphism.comp]
  comp_id := by intro X Y f; ext; simp [CuspMorphism.id, CuspMorphism.comp]
  assoc := by intro W X Y Z f g h; ext; simp [CuspMorphism.comp, Category.assoc]

/-- The cusp category as an object of the catalogue. -/
noncomputable def cuspCategory (R : Type u) [CommRing R] : ObjCat.{u + 1, u} :=
  Cat.of (CuspObject (R := R))

/-- The canonical cusp object at a lattice: the pair with `Γ = O(L)`. -/
noncomputable def canonicalCusp (L : IntegralLatticeCat R) : CuspObject (R := R) where
  lattice := L
  gamma := FiniteIndexSubgroup.top L

/-- The identity cusp morphism as a morphism of the registered category. -/
def cuspIdentity (X : CuspObject (R := R)) : X ⟶ X := CuspMorphism.id X

end LeanCategories.Lattices.Valued

namespace CasCatalogue

noncomputable section

namespace CategoryId
/-- The cusp category of the lattice pipeline (#113). -/
def cusps : CategoryId := ⟨"cat.cusps"⟩
end CategoryId

/-- The category expression of the cusp category. -/
def CuspsExpr : CategoryExpr := .atom CategoryId.cusps

/-- Its realization. -/
noncomputable def cuspsRealization (R : Type u) [CommRing R] :
    CategoryRealization CuspsExpr
      (LeanCategories.Lattices.Valued.cuspCategory (R := R)) := {}

normalized_registry .category
  { id := CategoryId.cusps, name := "Cusps"
    declaration := `LeanCategories.Lattices.Valued.cuspCategory
    expression := CuspsExpr
    realization := `CasCatalogue.cuspsRealization }

normalized_registry .object
  { id := ⟨"obj.cusps.canonical"⟩, category := CategoryId.cusps, name := "Cusp"
    declaration := `LeanCategories.Lattices.Valued.canonicalCusp }

normalized_registry .morphism
  { id := ⟨"mor.cusps.identity"⟩, category := CategoryId.cusps, name := "id"
    declaration := `LeanCategories.Lattices.Valued.cuspIdentity }

end

end CasCatalogue
