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
open LeanCategories.Modules.Bilinear.Valued

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

/-- A primitive isotropic sublattice of rank `k`: an isotropic submodule of rank `k` that is
primitive, i.e. whose quotient is torsion-free, which is Nikulin's condition. Rank 1 gives 0-cusps
and rank 2 gives 1-cusps. -/
structure PrimitiveIsotropic (L : IntegralLatticeCat R) (k : ℕ) where
  /-- The underlying submodule. -/
  toSubmodule : Submodule R L.obj.carrier
  /-- The restricted form vanishes. -/
  isotropic : IsIsotropicSubmodule L toSubmodule
  /-- Its rank. -/
  finrank_eq : Module.finrank R toSubmodule = k
  /-- Primitivity: the quotient by it is torsion-free. -/
  primitive : IsPrimitiveSubmodule toSubmodule

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
  /-- It is a primitive embedding: injective, with torsion-free cokernel. Without this the image of
  a primitive isotropic sublattice need not be one (`x ↦ 2x` on `ℤ` with the zero form kills
  primitivity), so the orbit map exists only for primitive morphisms. -/
  primitive : BilinModuleCat.IsPrimitiveEmbedding hom.hom
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
  primitive := by
    change IsPrimitiveSubmodule
      (N.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier))
    exact (IsPrimitiveSubmodule.map_equiv_iff
      (g.1 : L.obj.carrier ≃ₗ[R] L.obj.carrier) N.toSubmodule).mpr N.primitive

/-- The image of a primitive isotropic sublattice under a primitive embedding: isotropy holds
because the map preserves the form, the rank because it is injective, and primitivity by
`IsPrimitiveSubmodule.map_of_primitiveEmbedding`. -/
noncomputable def PrimitiveIsotropic.map {L M : IntegralLatticeCat R} {k : ℕ} (f : L ⟶ M)
    (hf : BilinModuleCat.IsPrimitiveEmbedding f.hom) (N : PrimitiveIsotropic L k) :
    PrimitiveIsotropic M k where
  toSubmodule := N.toSubmodule.map (BilinModuleCat.underlyingMap f.hom)
  isotropic := by
    intro x hx y hy
    simp only [Submodule.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [IntegralLatticeCat.asBilinForm_apply (L := M),
      BilinModuleCat.map_pairing, ← IntegralLatticeCat.asBilinForm_apply (L := L)]
    exact N.isotropic a ha b hb
  finrank_eq := by
    rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
      (BilinModuleCat.underlyingMap f.hom) hf.1 N.toSubmodule), N.finrank_eq]
  primitive := IsPrimitiveSubmodule.map_of_primitiveEmbedding
    (BilinModuleCat.underlyingMap f.hom) hf.1 hf.2 N.primitive

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

/-- The finite-index subgroup `Γ ⊆ O(L)` acts on primitive isotropic sublattices, by restriction of
scalars along `Γ → O(L)`. The instance is keyed on `FiniteIndexSubgroup` rather than on a bare
`Subgroup`: `Subgroup (OrthogonalGroup ?L)` forces the elaborator to unfold `orthogonalSubgroup` to
compare instances, which does not terminate in practice. -/
noncomputable instance primitiveIsotropicGammaMulAction {L : IntegralLatticeCat R}
    (Γ : FiniteIndexSubgroup L) {k : ℕ} : MulAction Γ.toSubgroup (PrimitiveIsotropic L k) :=
  MulAction.compHom (PrimitiveIsotropic L k) (Subgroup.subtype Γ.toSubgroup)

/-- The `Γ`-orbit relation on primitive isotropic sublattices of rank `k`. Naming it keeps the
`MulAction` instance search out of every later statement. -/
noncomputable def cuspOrbitRel (L : IntegralLatticeCat R) (Γ : FiniteIndexSubgroup L) (k : ℕ) :
    Setoid (PrimitiveIsotropic L k) :=
  MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropic L k)

/-- The `Γ`-orbits of primitive isotropic sublattices of rank `k`: `k = 1` gives the 0-cusps,
`k = 2` the 1-cusps. -/
noncomputable abbrev CuspOrbits (L : IntegralLatticeCat R) (Γ : FiniteIndexSubgroup L) (k : ℕ) :
    Type u :=
  Quotient (cuspOrbitRel L Γ k)

/-- The `Γ`-orbit of a primitive isotropic sublattice of rank `k`. -/
noncomputable abbrev CuspOrbits.mk {L : IntegralLatticeCat R} (Γ : FiniteIndexSubgroup L) {k : ℕ}
    (N : PrimitiveIsotropic L k) : CuspOrbits L Γ k :=
  Quotient.mk (cuspOrbitRel L Γ k) N

/-- Incidence between a rank-1 orbit and a rank-2 orbit: some representative line is nested in some
representative plane. -/
noncomputable def CuspIncidence (X : CuspObject (R := R)) : CuspOrbits X.lattice X.gamma 1 →
    CuspOrbits X.lattice X.gamma 2 → Prop :=
  fun c₁ c₂ => ∃ v : PrimitiveIsotropic X.lattice 1,
    CuspOrbits.mk X.gamma v = c₁ ∧ ∃ P : PrimitiveIsotropic X.lattice 2,
      CuspOrbits.mk X.gamma P = c₂ ∧ v.toSubmodule ≤ P.toSubmodule

/-- A morphism of lattices intertwining two orthogonal-group elements carries the image of the
`γ`-translate to the `δ`-translate: this is what makes the orbit map well defined. -/
theorem PrimitiveIsotropic.map_smul {L M : IntegralLatticeCat R} {k : ℕ} (f : L ⟶ M)
    (hf : BilinModuleCat.IsPrimitiveEmbedding f.hom) (γ : OrthogonalGroup L)
    (δ : OrthogonalGroup M)
    (h : (OrthogonalGroup.asLatticeIso γ).hom ≫ f = f ≫ (OrthogonalGroup.asLatticeIso δ).hom)
    (N : PrimitiveIsotropic L k) :
    PrimitiveIsotropic.map f hf (γ • N) = δ • PrimitiveIsotropic.map f hf N := by
  have h' : (BilinModuleCat.underlyingMap f.hom).comp
        (γ.1 : L.obj.carrier →ₗ[R] L.obj.carrier) =
      (δ.1 : M.obj.carrier →ₗ[R] M.obj.carrier).comp
        (BilinModuleCat.underlyingMap f.hom) := by
    have h2 := congrArg (fun t : L ⟶ M => BilinModuleCat.underlyingMap t.hom) h
    simpa only [ObjectProperty.FullSubcategory.comp_hom,
      BilinModuleCat.underlyingMap_comp,
      OrthogonalGroup.underlyingMap_asLatticeIso_hom] using h2
  apply PrimitiveIsotropic.ext
  change (γ • N).toSubmodule.map (BilinModuleCat.underlyingMap f.hom) =
    (δ • PrimitiveIsotropic.map f hf N).toSubmodule
  rw [show (γ • N).toSubmodule =
        N.toSubmodule.map (γ.1 : L.obj.carrier →ₗ[R] L.obj.carrier) from rfl,
      show (δ • PrimitiveIsotropic.map f hf N).toSubmodule =
        (N.toSubmodule.map (BilinModuleCat.underlyingMap f.hom)).map
          (δ.1 : M.obj.carrier →ₗ[R] M.obj.carrier) from rfl,
      ← Submodule.map_comp, ← Submodule.map_comp, h']

/-- The image of a `Γ`-orbit is a `Γ'`-orbit: the well-definedness of the orbit map, which is
exactly the equivariance of the cusp morphism. -/
theorem PrimitiveIsotropic.map_orbitRel {X Y : CuspObject (R := R)} {k : ℕ}
    (f : CuspMorphism X Y) {N N' : PrimitiveIsotropic X.lattice k}
    (hrel : cuspOrbitRel X.lattice X.gamma k N N') :
    cuspOrbitRel Y.lattice Y.gamma k (PrimitiveIsotropic.map f.hom f.primitive N)
      (PrimitiveIsotropic.map f.hom f.primitive N') := by
  obtain ⟨γ, hγ⟩ := hrel
  obtain ⟨δ, hδ, heq⟩ := f.equivariant γ γ.2
  have hmap : PrimitiveIsotropic.map f.hom f.primitive N =
      (⟨δ, hδ⟩ : ↥Y.gamma.toSubgroup) • PrimitiveIsotropic.map f.hom f.primitive N' := by
    have h2 := PrimitiveIsotropic.map_smul (L := X.lattice) (M := Y.lattice) f.hom f.primitive
      (γ : OrthogonalGroup X.lattice) δ heq N'
    have hN : N = (γ : OrthogonalGroup X.lattice) • N' := hγ.symm
    rw [← hN] at h2
    exact h2
  exact ⟨⟨δ, hδ⟩, hmap.symm⟩

/-- The induced map on `Γ`-orbits of primitive isotropic sublattices of rank `k`. -/
noncomputable def CuspOrbits.map {X Y : CuspObject (R := R)} (f : CuspMorphism X Y) (k : ℕ) :
    CuspOrbits X.lattice X.gamma k → CuspOrbits Y.lattice Y.gamma k :=
  have hwell : ∀ a b : PrimitiveIsotropic X.lattice k,
      cuspOrbitRel X.lattice X.gamma k a b →
      cuspOrbitRel Y.lattice Y.gamma k (PrimitiveIsotropic.map f.hom f.primitive a)
        (PrimitiveIsotropic.map f.hom f.primitive b) :=
    fun _ _ hh => PrimitiveIsotropic.map_orbitRel f hh
  @Quotient.map _ _ (cuspOrbitRel X.lattice X.gamma k) (cuspOrbitRel Y.lattice Y.gamma k)
    (fun N => PrimitiveIsotropic.map f.hom f.primitive N) hwell

/-- The orbit map sends the class of a representative to the class of its image. -/
theorem CuspOrbits.map_mk {X Y : CuspObject (R := R)} (f : CuspMorphism X Y) (k : ℕ)
    (N : PrimitiveIsotropic X.lattice k) :
    CuspOrbits.map f k (CuspOrbits.mk X.gamma N) =
      CuspOrbits.mk Y.gamma (PrimitiveIsotropic.map f.hom f.primitive N) :=
  @Quotient.map_mk _ _ (cuspOrbitRel X.lattice X.gamma k) (cuspOrbitRel Y.lattice Y.gamma k)
    (fun N => PrimitiveIsotropic.map f.hom f.primitive N)
    (fun _ _ hh => PrimitiveIsotropic.map_orbitRel f hh) N

namespace CuspMorphism

variable {X Y Z : CuspObject (R := R)}

/-- The identity morphism is equivariant for `γ ↦ γ`. -/
def id (X : CuspObject (R := R)) : CuspMorphism X X where
  hom := 𝟙 X.lattice
  primitive := by
    rw [ObjectProperty.FullSubcategory.id_hom]
    exact isPrimitiveEmbedding_id X.lattice.obj
  equivariant := by
    intro γ hγ
    exact ⟨γ, hγ, by simp⟩

/-- Composition of equivariant embeddings is equivariant: the witnesses compose. -/
def comp (f : CuspMorphism X Y) (g : CuspMorphism Y Z) : CuspMorphism X Z where
  hom := f.hom ≫ g.hom
  primitive := by
    rw [ObjectProperty.FullSubcategory.comp_hom]
    exact isPrimitiveEmbedding_comp f.hom.hom g.hom.hom f.primitive g.primitive
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
  obtain ⟨fh, fp, fe⟩ := f
  obtain ⟨gh, gp, ge⟩ := g
  obtain rfl := h
  rfl

/-- The cusp category: objects `(L, Γ)`, morphisms `Γ`-equivariant isometric embeddings. -/
instance : Category (CuspObject (R := R)) where
  Hom X Y := CuspMorphism X Y
  id X := CuspMorphism.id X
  comp f g := CuspMorphism.comp f g
  id_comp := by intro X Y f; ext; simp [CuspMorphism.id, CuspMorphism.comp]
  comp_id := by intro X Y f; ext; simp [CuspMorphism.id, CuspMorphism.comp]
  assoc := by intro W X Y Z f g h; ext; simp [CuspMorphism.comp, Category.assoc]

/-- The orbit map of the identity is the identity on classes. -/
theorem CuspOrbits.map_id_apply {X : CuspObject (R := R)} (k : ℕ)
    (c : CuspOrbits X.lattice X.gamma k) : CuspOrbits.map (𝟙 X) k c = c := by
  refine Quotient.inductionOn c ?_
  intro N
  erw [CuspOrbits.map_mk]
  congr 1
  apply PrimitiveIsotropic.ext
  change N.toSubmodule.map LinearMap.id = N.toSubmodule
  rw [Submodule.map_id]

/-- The orbit map of a composite is the composite of the orbit maps. -/
theorem CuspOrbits.map_comp_apply {X Y Z : CuspObject (R := R)} (f : CuspMorphism X Y)
    (g : CuspMorphism Y Z) (k : ℕ) (c : CuspOrbits X.lattice X.gamma k) :
    CuspOrbits.map (CuspMorphism.comp f g) k c = CuspOrbits.map g k (CuspOrbits.map f k c) := by
  refine Quotient.inductionOn c ?_
  intro N
  erw [CuspOrbits.map_mk]
  congr 1
  apply PrimitiveIsotropic.ext
  change Submodule.map ((BilinModuleCat.underlyingMap g.hom.hom).comp
      (BilinModuleCat.underlyingMap f.hom.hom)) N.toSubmodule
    = Submodule.map (BilinModuleCat.underlyingMap g.hom.hom)
        (Submodule.map (BilinModuleCat.underlyingMap f.hom.hom) N.toSubmodule)
  rw [Submodule.map_comp]

/-- The orbit functor: `(L, Γ) ↦ Γ`-orbits of primitive isotropic sublattices of rank `k`. `k = 1`
gives the 0-cusps and `k = 2` the 1-cusps; cusps are an invariant of primitive embeddings, which is
why the morphism class carries `IsPrimitiveEmbedding`. -/
noncomputable def cuspOrbitFunctor (k : ℕ) : CuspObject (R := R) ⥤ Type u where
  obj X := CuspOrbits X.lattice X.gamma k
  map f := ↾(CuspOrbits.map f k)
  map_id X := by
    ext c
    simp only [CategoryTheory.ConcreteCategory.hom_ofHom]
    exact CuspOrbits.map_id_apply k c
  map_comp f g := by
    ext c
    simp only [CategoryTheory.ConcreteCategory.hom_ofHom]
    exact CuspOrbits.map_comp_apply f g k c

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

namespace FunctorId
/-- The Γ-orbit functor of the cusp category (#113). -/
def cuspsOrbits : FunctorId := ⟨"fun.cusps.orbits"⟩
end FunctorId

/-- The expression of the orbit functor: from the cusp category to `Sets`. -/
def CuspsOrbitsExpr : FunctorExpr CuspsExpr Foundation.Sets :=
  .atomic FunctorId.cuspsOrbits

/-- The orbit functor to `Sets`, as a functor of the registered categories: `(L, Γ) ↦ Γ`-orbits
of primitive isotropic sublattices of rank `k`. -/
noncomputable def cuspsOrbits (R : Type u) [CommRing R] (k : ℕ) :
    LeanCategories.Lattices.Valued.cuspCategory (R := R) ⥤
      LeanCategories.Foundation.Mathlib.Sets.{u} :=
  LeanCategories.Lattices.Valued.cuspOrbitFunctor k

/-- Its realization, over the cusp and `Sets` category realizations. -/
noncomputable def cuspsOrbitsRealization (R : Type u) [CommRing R] (k : ℕ) :
    FunctorRealization CuspsOrbitsExpr
      (LeanCategories.Lattices.Valued.cuspCategory (R := R))
      LeanCategories.Foundation.Mathlib.Sets.{u} (cuspsOrbits R k) :=
  { sourceRealization := cuspsRealization R
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

normalized_registry .functor
  { id := FunctorId.cuspsOrbits, source := CuspsExpr, target := Foundation.Sets
    declaration := `CasCatalogue.cuspsOrbits
    realization := `CasCatalogue.cuspsOrbitsRealization
    expression := CuspsOrbitsExpr }

end

end CasCatalogue
