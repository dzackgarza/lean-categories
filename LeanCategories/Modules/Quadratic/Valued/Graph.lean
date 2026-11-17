/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Witt
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Graphs of anti-isometries in an orthogonal sum of quadratic modules

For an `R`-module `M₁` with a quadratic map `q₁ : M₁ → W`, an `R`-module `M₂` with
`q₂ : M₂ → W`, a submodule `H ≤ M₁` and a linear map `γ : H → M₂`, the *graph*
`Γ_γ = {(x, γ x) | x ∈ H}` is a submodule of the product `M₁ × M₂`
(`quadraticGraph`). The product carries the orthogonal sum `q₁ ⊕ q₂ = QuadraticMap.prod q₁ q₂`
of Mathlib, whose value on a pair is `q₁ x + q₂ y`.

The two results here are the two directions of the statement that *the graph of an
anti-isometry is an isotropic subgroup, and every isotropic subgroup is such a graph*:

* `isTotallyIsotropic_quadraticGraph_iff` — `Γ_γ` is totally isotropic for `q₁ ⊕ q₂` exactly
  when `γ` reverses quadratic values, `q₂ (γ x) = -q₁ x` for every `x ∈ H`. Both directions are
  read off from the single value of `q₁ ⊕ q₂` on a pair `(x, γ x)`; no coordinate expansion of
  the polarization is needed, and no isotropy of the polarization is assumed separately —
  for a linear `γ` the polarization condition follows from the value condition.
* `exists_quadraticGraph_eq_of_isTotallyIsotropic` — conversely, a totally isotropic submodule
  whose two coordinate projections are injective *is* the graph of a linear map `γ : H → M₂`
  that (i) is injective, and (ii) reverses quadratic values. Injectivity of the two projections
  is what makes the submodule a graph: the first makes the projection onto the first factor
  an isomorphism onto its image, and the second is exactly injectivity of `γ`.

## Source

V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
Math. USSR Izv. 14 (1980), §1.5, p. 111. For even lattices `S` and `K`, a subgroup
`H ⊆ A_S` and a monomorphism `γ : H → A_K` with `q_K ∘ γ = -q_S|H`, the pushout
`Γ_γ ⊆ A_S ⊕ A_K` of `γ` is isotropic for `q_S ⊕ q_K`; conversely, the total isotropy of the
subgroup `H_M = M/(S ⊕ K) ⊆ A_S ⊕ A_K` and the injectivity of the two projections
`p_S : H_M → A_S`, `p_K : H_M → A_K` present it as the pushout of
`γ_{S,K}^M = p_K ∘ p_S⁻¹ : H_{M,S} → H_{M,K}`, and "the isotropy of `H_M` shows that
`q_K ∘ γ_{S,K}^M = -q_S`" (p. 111). The results below are that pair of statements for
quadratic maps over an arbitrary commutative ring.

## Port provenance

Ported, with the carriers replaced, from `TauCetiProject/TauCeti` (Apache 2.0, © The Tau Ceti
contributors), `TauCeti/LinearAlgebra/FiniteBilinearModule/Orthogonal/Graph.lean`:
`TauCeti.FiniteQuadraticModule.isIsotropic_graph_iff` (a homomorphism's graph is isotropic
exactly when it reverses quadratic values) and
`TauCeti.FiniteQuadraticModule.exists_isometry_neg_mem_iff_of_isLagrangian` (a Lagrangian
meeting both factors trivially is the graph of such an isometry). Mathlib's
`QuadraticMap.prod`, `QuadraticMap.prod_apply`, `QuadraticMap.polar` and `LinearMap.prod` are
used directly.

The port replaces TauCeti's `FiniteQuadraticModule` — a finite abelian group with an
`AddSubgroup` lattice of subgroups, `AddMonoidHom.graph`, and `AddEquiv` — by this repository's
`QuadModuleCat` over a commutative ring, with `Submodule` and `LinearMap`. Two hypotheses of
the reference do not survive: neither finiteness, nor the Lagrangian condition `H = H^⊥`, is
needed. TauCeti uses the Lagrangian condition and a cardinality count (`#H² = #A·#B`, then
`Nat.bijective_iff_injective_and_card`) to turn its two injective projections into bijections;
over a module that count is unnecessary, because a submodule whose projection to the first
factor is injective is already the graph of a linear map on its image. Consequently the
statement below is Nikulin's §1.5 (isotropy plus injective projections), not §1.6's
Lagrangian one — which is what the two-lattice gluing needs, since a gluing subgroup that is
not a metabolizer is exactly the case the F_Co pipeline consumes.

## LC-09 search record

Queries over the formalization corpus (`scripts/formalization_corpus.py search`):

* `isIsotropic_graph_iff` — 2 files: the TauCeti hit above, and
  `TauCeti/Geometry/Symplectic/Lagrangian/Constructions.lean`
  (`isIsotropic_graph_iff` for symplectic forms, bilinear not quadratic: not applicable).
* `discriminantGroupOrthogonalSumEquiv`, `graph of an isometry orthogonal sum discriminant`,
  `QuadraticMap.prod IsometryEquiv neg`, `isotropic subgroup overlattice discriminant
  q|H^perp/H`, `IsTotallyIsotropic graph anti-isometry`.

The closest Mathlib declarations used directly are `QuadraticMap.prod`,
`QuadraticMap.prod_apply`, `QuadraticMap.polar`, `QuadraticForm.Isometry.inl/inr` and
`LinearMap.prod`; Mathlib has no statement that a graph is isotropic iff the map reverses the
quadratic form, and no converse characterising an isotropic submodule as a graph.
-/

@[expose] public section

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

namespace QuadModuleCat

/-- The quadratic map of `ofQuadraticMap q` is `q`. -/
@[simp]
theorem form_ofQuadraticMap {M : Type u} [AddCommGroup M] [Module R M]
    (q : QuadraticMap R M W) :
    (QuadModuleCat.ofQuadraticMap q).form = q :=
  rfl

/-- Total isotropy of `ofQuadraticMap q` on a submodule of the carriers: the quadratic map
vanishes on its elements. -/
theorem isTotallyIsotropic_ofQuadraticMap_iff {M : Type u} [AddCommGroup M] [Module R M]
    (q : QuadraticMap R M W) (P : Submodule R M) :
    (QuadModuleCat.ofQuadraticMap q).IsTotallyIsotropic P ↔ ∀ x ∈ P, q x = 0 :=
  ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

end QuadModuleCat

/-- The graph of a linear map `γ : H → M₂` out of a submodule `H ≤ M₁`, as a submodule of the
product `M₁ × M₂`. -/
def quadraticGraph (H : Submodule R M₁) (γ : H →ₗ[R] M₂) : Submodule R (M₁ × M₂) :=
  LinearMap.range (LinearMap.prod H.subtype γ)

theorem mem_quadraticGraph_iff {H : Submodule R M₁} {γ : H →ₗ[R] M₂} {x : M₁} {y : M₂} :
    (x, y) ∈ quadraticGraph H γ ↔ ∃ hx : x ∈ H, γ ⟨x, hx⟩ = y := by
  constructor
  · rintro ⟨z, hz⟩
    rw [LinearMap.prod_apply] at hz
    obtain rfl : (z : M₁) = x := congrArg Prod.fst hz
    refine ⟨z.2, ?_⟩
    simpa using congrArg Prod.snd hz
  · rintro ⟨hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [LinearMap.prod_apply]
    exact Prod.ext rfl hxy

theorem quadraticGraph_apply {H : Submodule R M₁} {γ : H →ₗ[R] M₂} (x : H) :
    ((x : M₁), γ x) ∈ quadraticGraph H γ :=
  mem_quadraticGraph_iff.mpr ⟨x.2, rfl⟩

/-- **The graph of an anti-isometry is isotropic.** The graph `Γ_γ ⊆ M₁ × M₂` of a linear map
`γ : H → M₂` is totally isotropic for the orthogonal sum `q₁ ⊕ q₂` if and only if `γ` reverses
quadratic values: `q₂ (γ x) = -q₁ x` for all `x ∈ H`. -/
theorem isTotallyIsotropic_quadraticGraph_iff
    (q₁ : QuadraticMap R M₁ W) (q₂ : QuadraticMap R M₂ W)
    (H : Submodule R M₁) (γ : H →ₗ[R] M₂) :
    (QuadModuleCat.ofQuadraticMap (QuadraticMap.prod q₁ q₂)).IsTotallyIsotropic
        (quadraticGraph H γ) ↔
      ∀ x : H, q₂ (γ x) = -q₁ (x : M₁) := by
  constructor
  · intro h x
    have hx := (QuadModuleCat.isTotallyIsotropic_ofQuadraticMap_iff
      (QuadraticMap.prod q₁ q₂) (quadraticGraph H γ)).mp h ((x : M₁), γ x)
      (quadraticGraph_apply x)
    rw [QuadraticMap.prod_apply] at hx
    exact eq_neg_of_add_eq_zero_right hx
  · intro h
    refine (QuadModuleCat.isTotallyIsotropic_ofQuadraticMap_iff
      (QuadraticMap.prod q₁ q₂) (quadraticGraph H γ)).mpr ?_
    intro p hp
    obtain ⟨hx, hxy⟩ := mem_quadraticGraph_iff.mp hp
    rw [QuadraticMap.prod_apply, ← hxy, h ⟨p.1, hx⟩, add_neg_cancel]

/-- **Every isotropic subgroup with injective projections is a graph.** A totally isotropic
submodule `N ≤ M₁ × M₂` whose two coordinate projections are injective is the graph of an
injective linear map `γ : H → M₂` out of a submodule `H ≤ M₁`, and that map reverses quadratic
values. This is the converse of `isTotallyIsotropic_quadraticGraph_iff`, with the projection
hypotheses of Nikulin §1.5, p. 111. -/
theorem exists_quadraticGraph_eq_of_isTotallyIsotropic
    (q₁ : QuadraticMap R M₁ W) (q₂ : QuadraticMap R M₂ W)
    (N : Submodule R (M₁ × M₂))
    (hN : (QuadModuleCat.ofQuadraticMap (QuadraticMap.prod q₁ q₂)).IsTotallyIsotropic N)
    (h₁ : Function.Injective fun x : N => ((x : M₁ × M₂)).1)
    (h₂ : Function.Injective fun x : N => ((x : M₁ × M₂)).2) :
    ∃ (H : Submodule R M₁) (γ : H →ₗ[R] M₂), Function.Injective γ ∧
      (∀ x : H, q₂ (γ x) = -q₁ (x : M₁)) ∧ N = quadraticGraph H γ := by
  classical
  -- Total isotropy, on pairs.
  have hq : ∀ p ∈ N, q₁ p.1 + q₂ p.2 = 0 := by
    intro p hp
    have hp' := (QuadModuleCat.isTotallyIsotropic_ofQuadraticMap_iff
      (QuadraticMap.prod q₁ q₂) N).mp hN p hp
    rwa [QuadraticMap.prod_apply] at hp'
  -- The first projection is an isomorphism of `N` onto its image.
  let H : Submodule R M₁ := N.map (LinearMap.fst R M₁ M₂)
  let π : N →ₗ[R] H :=
    ((LinearMap.fst R M₁ M₂).comp N.subtype).codRestrict H
      (fun z => Submodule.mem_map_of_mem (f := LinearMap.fst R M₁ M₂) z.2)
  have hπ_val : ∀ z : N, (π z : M₁) = ((z : M₁ × M₂)).1 := fun _ => rfl
  have hπ_inj : Function.Injective π := by
    intro z z' h
    exact h₁ (by simpa only [hπ_val] using congrArg (fun w : H => (w : M₁)) h)
  have hπ_surj : Function.Surjective π := by
    intro w
    obtain ⟨z, hz, hw⟩ := Submodule.mem_map.mp w.2
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    rw [hπ_val]
    exact hw
  let φ : N ≃ₗ[R] H := LinearEquiv.ofBijective π ⟨hπ_inj, hπ_surj⟩
  have hφ_val : ∀ z : N, ((φ z : H) : M₁) = ((z : M₁ × M₂)).1 := hπ_val
  have hsymm_fst : ∀ w : H, ((φ.symm w : N) : M₁ × M₂).1 = (w : M₁) := by
    intro w
    rw [← hφ_val (φ.symm w), φ.apply_symm_apply]
  -- The linear map whose graph is `N`: the second projection, read along `φ⁻¹`.
  let γ : H →ₗ[R] M₂ := ((LinearMap.snd R M₁ M₂).comp N.subtype).comp φ.symm.toLinearMap
  have hγ : ∀ w : H, γ w = ((φ.symm w : N) : M₁ × M₂).2 := fun _ => rfl
  have hsymm_pair : ∀ w : H, ((φ.symm w : N) : M₁ × M₂) = ((w : M₁), γ w) := by
    intro w
    exact Prod.ext (hsymm_fst w) (hγ w).symm
  have hsymm_mem : ∀ w : H, ((w : M₁), γ w) ∈ N := by
    intro w
    rw [← hsymm_pair w]
    exact (φ.symm w).2
  refine ⟨H, γ, ?_, ?_, ?_⟩
  · -- `γ` is injective, because the second projection is injective on `N`.
    intro u u' h
    have heq : (⟨((u : M₁), γ u), hsymm_mem u⟩ : N) =
        ⟨((u' : M₁), γ u'), hsymm_mem u'⟩ :=
      h₂ (by simpa using h)
    exact Subtype.ext (congrArg (fun z : N => ((z : M₁ × M₂)).1) heq)
  · -- The value condition is total isotropy of `N`, read at `(x, γ x) ∈ N`.
    intro x
    have hx := hq ((x : M₁), γ x) (hsymm_mem x)
    exact eq_neg_of_add_eq_zero_right hx
  · -- `N` is the graph of `γ`.
    apply le_antisymm
    · intro p hp
      have hx : p.1 ∈ H := Submodule.mem_map_of_mem (f := LinearMap.fst R M₁ M₂) hp
      refine mem_quadraticGraph_iff.mpr ⟨hx, ?_⟩
      have hsame : (⟨(p.1, γ ⟨p.1, hx⟩), hsymm_mem ⟨p.1, hx⟩⟩ : N) = ⟨p, hp⟩ := h₁ rfl
      exact congrArg (fun z : N => ((z : M₁ × M₂)).2) hsame
    · intro p hp
      obtain ⟨hx, hxy⟩ := mem_quadraticGraph_iff.mp hp
      have hp_eq : ((φ.symm ⟨p.1, hx⟩ : N) : M₁ × M₂) = p := by
        rw [hsymm_pair ⟨p.1, hx⟩]
        exact Prod.ext rfl hxy
      rw [← hp_eq]
      exact (φ.symm ⟨p.1, hx⟩).2

end LeanCategories.Modules.Quadratic.Valued

#print axioms LeanCategories.Modules.Quadratic.Valued.quadraticGraph
#print axioms LeanCategories.Modules.Quadratic.Valued.mem_quadraticGraph_iff
#print axioms LeanCategories.Modules.Quadratic.Valued.isTotallyIsotropic_quadraticGraph_iff
#print axioms LeanCategories.Modules.Quadratic.Valued.exists_quadraticGraph_eq_of_isTotallyIsotropic
