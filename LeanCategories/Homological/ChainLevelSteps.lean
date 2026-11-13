/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.Localization

@[expose] public section

/-!
# ChainLevelSteps: augmented exactness and the skeleton's differentials

Card `E-HAT-2.2-16` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 2.2, exercise 16.  Certificate: new-qual-site
`proofs/cards/ChainLevelSteps.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; the route is
Mathlib's maintained API, so the port imports it and renames nothing
mathematical.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/ChainLevelSteps.lean`; theorem names keep the certificate's spelling.
-/


/-!
# `E-HAT-2.2-16`: augmented exactness and the skeleton's differentials

The card computes the ranks of cycles and boundaries of the standard simplex and then passes
to its $k$-skeleton. Two steps of that argument need care, and this file certifies them.

The degree-zero step. In the ordinary chain complex $Z_0 = C_0$ and
$B_0 = \\operatorname{im}\\partial_1$, so $Z_0/B_0 = H_0$, which does not vanish; the reduced
statement is about the *augmented* complex, whose degree-zero boundary is an augmentation
$\\varepsilon : C_0 \\to \\ZZ$ with $\\ker\\varepsilon = \\operatorname{im}\\partial_1$. So

* `choose_rank_step`: Pascal's identity in the form the rank induction uses;
* `ker_ne_top_of_surjective_to_int`: a surjection onto $\\ZZ$ has proper kernel, so the
  augmented degree-zero cycles are not the ordinary ones;
* `not_subsingleton_ordinary_homology`: with $\\ker\\varepsilon = \\operatorname{im}\\partial_1$
  and $\\varepsilon$ onto $\\ZZ$, the ordinary $C_0/\\operatorname{im}\\partial_1 \\cong \\ZZ$ is
  **not** trivial, while the augmented $\\ker\\varepsilon/\\operatorname{im}\\partial_1$ is. This
  is exactly why $Z_0/B_0$ cannot stand in for $\\widetilde H_0$.

The skeleton step. The $k$-skeleton has the simplex's chain groups and differentials in
degrees at most $k$ and none above, so exactness of the augmented complex below degree $k$
passes to it. `ker_eq_range_of_comm_iso` is the transport: if the three-term complexes
$A \\leftarrow B \\leftarrow C$ and $A' \\leftarrow B' \\leftarrow C'$ are isomorphic by a chain
map, then $\\ker\\partial = \\operatorname{im}\\partial'$ transports. The range restriction
$i < k$ is where the agreement hypothesis is used.

Both halves of that chain-level comparison are now proved. `skSimplexEquiv` and
`skSimplexEquiv_δ` compare the simplices, `skChainsIso` compares the chain groups, and
`skChainsIso_δ` and `skChainsIso_d` compare the differentials: the alternating face map
differential is the alternating sum of the face maps, so the face-level compatibility summed
over `Fin (i + 2)` gives the chain-level square, for `i + 1 ≤ k`. What this file still does not
prove, and what `proofs/README.md` §5 records: the homology statement
$\widetilde H_i((\Delta^m)^k) = 0$ for $i < k$, and the barycentric chains, for which the pin has
no `SSet.B` and no `sd ⟶ B`.

The transport that the homology statement needs is `skChains_exact`: exactness at a degree,
`\\ker \\partial_{j+1} = \\operatorname{im} \\partial_{j+2}`, passes to the $k$-skeleton when
$j + 2 \\le k$, through `ker_eq_range_of_comm_iso` and the two squares. The lemma it feeds was
stated over `[AddCommGroup]` alone, so its linear maps carried `AddCommGroup.toIntModule` while the
`ModuleCat` differentials carry `ModuleCat.isModule`; the two structures are the same on paper and
not definitionally, which is the type-class diamond section 5b of `proofs/README.md` records
elsewhere. The binders are now explicit `[Module ℤ _]`, which is a sharper statement of the same
transport and leaves every existing use intact. What is still absent for the card's sentence is the
simplex's own exactness in `\\ker = \\operatorname{range}` form, which is a bridge from
`SimplexChains.isZero_homology` (`IsZero` of a homology object), not new mathematics.
-/

namespace LeanCategories.Homological.ChainLevelSteps

open scoped DirectSum

/-- Pascal's identity in the form used by the rank induction of `E-HAT-2.2-16`: the number
of $(i+1)$-subsets of an $(n+1)$-set minus the number of $i$-subsets of an $n$-set is the
number of $(i+1)$-subsets of the $n$-set. -/
theorem choose_rank_step (n i : ℕ) :
    Nat.choose (n + 1) (i + 1) - Nat.choose n i = Nat.choose n (i + 1) := by
  rw [Nat.choose_succ_succ]
  exact Nat.add_sub_cancel_left _ _

/-- The degree-zero defect of `E-HAT-2.2-16`: an augmentation onto `ℤ` cannot have kernel
`⊤`, so the augmented degree-zero cycles are a proper subgroup of `C₀`, unlike the ordinary
$Z_0 = C_0$. -/
theorem ker_ne_top_of_surjective_to_int {C₀ : Type*} [AddCommGroup C₀] [Module ℤ C₀]
    (e : C₀ →ₗ[ℤ] ℤ) (he : Function.Surjective e) : LinearMap.ker e ≠ ⊤ := by
  intro h
  have hzero : e = 0 := by
    ext x
    have hx : x ∈ LinearMap.ker e := by rw [h]; exact Submodule.mem_top
    simpa using hx
  obtain ⟨x, hx⟩ := he 1
  rw [hzero] at hx
  simp at hx

/-- Transport of exactness across an isomorphism of three-term complexes: if the squares
commute and `ker d₁ = range d₂`, then `ker d₁' = range d₂'`. This is the mechanism by which
the $k$-skeleton inherits exactness from the simplex in the degrees where their differentials
agree. -/
theorem ker_eq_range_of_comm_iso
    {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] [Module ℤ C']
    (ea : A' ≃ₗ[ℤ] A) (eb : B' ≃ₗ[ℤ] B) (ec : C' ≃ₗ[ℤ] C)
    (d₁ : B →ₗ[ℤ] A) (d₂ : C →ₗ[ℤ] B) (d₁' : B' →ₗ[ℤ] A') (d₂' : C' →ₗ[ℤ] B')
    (h₁ : d₁ ∘ₗ eb.toLinearMap = ea.toLinearMap ∘ₗ d₁')
    (h₂ : d₂ ∘ₗ ec.toLinearMap = eb.toLinearMap ∘ₗ d₂')
    (hex : LinearMap.ker d₁ = LinearMap.range d₂) :
    LinearMap.ker d₁' = LinearMap.range d₂' := by
  have hmem : ∀ y : B', y ∈ LinearMap.ker d₁' ↔ eb y ∈ LinearMap.ker d₁ := by
    intro y
    have h := congrArg (fun g => g y) h₁
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    rw [LinearMap.mem_ker, LinearMap.mem_ker, h, ea.map_eq_zero_iff]
  have hmem2 : ∀ y : B', y ∈ LinearMap.range d₂' ↔ eb y ∈ LinearMap.range d₂ := by
    intro y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨ec z, ?_⟩
      have h := congrArg (fun g => g z) h₂
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using h
    · rintro ⟨z, hz⟩
      refine ⟨ec.symm z, eb.injective ?_⟩
      have h := congrArg (fun g => g (ec.symm z)) h₂
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h
      rw [← h]
      exact hz
  ext y
  rw [hmem, hmem2, hex]

/-- The augmented degree-zero cycles are the boundaries, but the ordinary ones are not: with
`ker ε = range ∂` and `ε` onto `ℤ`, the ordinary `C₀ / im ∂` is not a subsingleton. This is
the exact defect that made $Z_0/B_0$ unusable as $\\widetilde H_0$. -/
theorem not_subsingleton_ordinary_homology {C₀ C₁ : Type*} [AddCommGroup C₀]
    [AddCommGroup C₁] (ε : C₀ →ₗ[ℤ] ℤ) (d : C₁ →ₗ[ℤ] C₀)
    (hε : Function.Surjective ε) (hex : LinearMap.ker ε = LinearMap.range d) :
    ¬ Subsingleton (C₀ ⧸ LinearMap.range d) := by
  intro hsub
  have hker : LinearMap.ker ε = ⊤ := by
    rw [hex]
    rw [Submodule.eq_top_iff']
    intro x
    have hx : Submodule.Quotient.mk x (p := LinearMap.range d) = 0 :=
      @Subsingleton.elim _ hsub _ _
    rwa [Submodule.Quotient.mk_eq_zero] at hx
  exact ker_ne_top_of_surjective_to_int ε hε hker

/-! ## The `k`-skeleton's simplices in degrees at most `k`

The skeleton step above is stated for a `k`-skeleton that "has the simplex's chain groups in degrees
at most `k`". That is now proved, at the level of simplices: `SSet.sk k X` is the `k`-skeleton and
`IsIso ((SSet.skAdj k).unit)` — the coreflection of the truncation onto it — gives an equivalence of
`i`-simplices for every `i ≤ k`, and `skSimplexEquiv_δ` shows that equivalence is natural for the
  face
maps whenever `j + 1 ≤ k`. `skChainsIso` compares the chain groups: the
alternating face map complex has the free abelian group on the `i`-simplices in degree `i`, so the
equivalence gives an isomorphism there for `i ≤ k`. What this file still does **not** prove is the
agreement of the *differentials*, i.e. the chain map itself, and with it
`H̃_i((Δ^m)^k) = 0` for `i < k`. `ker_eq_range_of_comm_iso` above is the
transport those pieces will feed. -/

open CategoryTheory Opposite Simplicial

/-- **The `i`-simplices of the `k`-skeleton are those of `X`, for `i ≤ k`.** This is the unit of the
skeleton–truncation adjunction, which is an isomorphism because `SSet.Truncated.sk k` is a
coreflection. -/
noncomputable def skSimplexEquiv (k : ℕ) (X : SSet.{0}) (i : ℕ) (hi : i ≤ k) :
    X _⦋i⦌ ≃ ((SSet.sk k).obj X) _⦋i⦌ := by
  haveI : IsIso ((SSet.skAdj k).unit.app ((SSet.truncation k).obj X)) := inferInstance
  have e : X _⦋i⦌ ≅ ((SSet.sk k).obj X) _⦋i⦌ :=
    (asIso ((SSet.skAdj k).unit.app ((SSet.truncation k).obj X))).app
      (op (⟨SimplexCategory.mk i, by simpa using hi⟩ : SimplexCategory.Truncated k))
  exact e.toEquiv

/-- **The simplex identification is natural for the face maps**, which is the compatibility the
chain-level half of the skeleton step needs: for `j + 1 ≤ k` the equivalence intertwines `δ_i` on
  `X`
with `δ_i` on the skeleton. -/
theorem skSimplexEquiv_δ (k : ℕ) (X : SSet.{0}) {j : ℕ} (hj : j ≤ k) (hj1 : j + 1 ≤ k)
    (i : Fin (j + 2)) (x : X _⦋j + 1⦌) :
    skSimplexEquiv k X j hj ((X.δ i) x)
      = ((SSet.sk k).obj X).δ i (skSimplexEquiv k X (j + 1) hj1 x) := by
  exact NatTrans.naturality_apply
    (asIso ((SSet.skAdj k).unit.app ((SSet.truncation k).obj X))).hom
    (op (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i)
      (by simpa using hj) (by simpa using hj1)) : _ ⟶ _) x

/-- **The `k`-skeleton's chain groups in degrees at most `k`.** The alternating face map complex of
  a
simplicial set has the free abelian group on its `i`-simplices in degree `i`, so `skSimplexEquiv`
induces an isomorphism of chain groups there. This is the degreewise half of the chain-level step;
  the
differentials' agreement is the remaining piece. -/
noncomputable def skChainsIso (k : ℕ) (X : SSet.{0}) (i : ℕ) (hi : i ≤ k) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (X ⋙ (ModuleCat.free ℤ))).X i
      ≅ (AlgebraicTopology.AlternatingFaceMapComplex.obj
          (((SSet.sk k).obj X) ⋙ (ModuleCat.free ℤ))).X i :=
  (ModuleCat.free ℤ).mapIso (skSimplexEquiv k X i hi).toIso

/-- The chain complex of a simplicial set's free chain groups, named so that the differential
statements below read as chain-level statements. -/
noncomputable abbrev chainsCpx (X : SSet.{0}) : ChainComplex (ModuleCat ℤ) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj (X ⋙ (ModuleCat.free ℤ))

/-- **The `k`-skeleton's chain groups are the simplex's, compatibly with one face map.** The
degree-wise isomorphism of `skChainsIso` commutes with `δ j`: on generators `freeMk x` it says that
`skSimplexEquiv_δ` holds, which is the only input. This is the face-level half of the chain map. -/
theorem skChainsIso_δ (k : ℕ) (X : SSet.{0}) {i : ℕ} (hi : i + 1 ≤ k) (j : Fin (i + 2)) :
    (skChainsIso k X (i + 1) hi).hom ≫
        SimplicialObject.δ (X := (SSet.sk k).obj X ⋙ ModuleCat.free ℤ) j =
      SimplicialObject.δ (X := X ⋙ ModuleCat.free ℤ) j ≫
        (skChainsIso k X i (Nat.le_of_succ_le hi)).hom := by
  have h1 : SimplicialObject.δ (X := (SSet.sk k).obj X ⋙ ModuleCat.free ℤ) j
      = (ModuleCat.free ℤ).map (((SSet.sk k).obj X).δ j) := rfl
  have h2 : SimplicialObject.δ (X := X ⋙ ModuleCat.free ℤ) j
      = (ModuleCat.free ℤ).map (X.δ j) := rfl
  rw [h1, h2]
  apply ModuleCat.free_hom_ext
  intro x
  simp only [ModuleCat.comp_apply, skChainsIso, Functor.mapIso_hom]
  simp only [ModuleCat.free_map_apply (R := ℤ)]
  exact congrArg (ModuleCat.freeMk (R := ℤ))
    (skSimplexEquiv_δ k X (Nat.le_of_succ_le hi) hi j x).symm

/-- **The `k`-skeleton's differentials agree with the simplex's in degrees at most `k`.** The
alternating face map differential is the alternating sum of the face maps, so the face-level
compatibility of `skChainsIso_δ`, summed over `Fin (i + 2)`, gives the square. With
`skChainsIso` this is the degreewise isomorphism of the two chain complexes where both are
defined, i.e. the low-degree part of a chain map; the differentials above degree `k` are the
part the skeleton does not have. -/
theorem skChainsIso_d (k : ℕ) (X : SSet.{0}) {i : ℕ} (hi : i + 1 ≤ k) :
    (skChainsIso k X (i + 1) hi).hom ≫ (chainsCpx ((SSet.sk k).obj X)).d (i + 1) i =
      (chainsCpx X).d (i + 1) i ≫ (skChainsIso k X i (Nat.le_of_succ_le hi)).hom := by
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  exact Finset.sum_congr rfl fun j _ => by rw [skChainsIso_δ k X hi j]


/-- Inverting a commuting square of linear maps: from `d' ∘ e₁ = e₀ ∘ d` with `e₀`, `e₁` linear
equivalences, the square with the inverses commutes the other way, `d ∘ e₁⁻¹ = e₀⁻¹ ∘ d'`. This is
the orientation `ker_eq_range_of_comm_iso` asks for, and `skChainsIso_d` supplies the other one. -/
theorem comp_inv_of_inv_comp {A A' B B' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module ℤ A] [Module ℤ A'] [Module ℤ B] [Module ℤ B']
    (e₀ : A ≃ₗ[ℤ] A') (e₁ : B ≃ₗ[ℤ] B') (d : B →ₗ[ℤ] A) (d' : B' →ₗ[ℤ] A')
    (h : d'.comp e₁.toLinearMap = e₀.toLinearMap.comp d) :
    d.comp e₁.symm.toLinearMap = e₀.symm.toLinearMap.comp d' := by
  ext y
  apply e₀.injective
  have hh := LinearMap.congr_fun h (e₁.symm y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hh ⊢
  exact hh.symm

/-- **Exactness at a degree transports to the `k`-skeleton.** If the simplex's chain complex has
`ker ∂_{j+1} = im ∂_{j+2}` and `j + 2 ≤ k`, then so does the `k`-skeleton's: their chain groups in
degrees `j`, `j + 1`, `j + 2` agree (`skChainsIso`) and so do the two differentials involved
(`skChainsIso_d`), which is exactly what `ker_eq_range_of_comm_iso` transports. -/
theorem skChains_exact (k : ℕ) (X : SSet.{0}) {j : ℕ} (hj : j + 2 ≤ k)
    (hex : LinearMap.ker ((chainsCpx X).d (j + 1) j).hom
      = LinearMap.range ((chainsCpx X).d (j + 2) (j + 1)).hom) :
    LinearMap.ker ((chainsCpx ((SSet.sk k).obj X)).d (j + 1) j).hom
      = LinearMap.range ((chainsCpx ((SSet.sk k).obj X)).d (j + 2) (j + 1)).hom := by
  have hsq1 := (comp_inv_of_inv_comp
    ((skChainsIso k X j (by omega)).toLinearEquiv)
    ((skChainsIso k X (j + 1) (by omega)).toLinearEquiv)
    ((chainsCpx X).d (j + 1) j).hom
    ((chainsCpx ((SSet.sk k).obj X)).d (j + 1) j).hom
    (by
      have := congrArg ModuleCat.Hom.hom (skChainsIso_d k X (i := j) (by omega : j + 1 ≤ k))
      simpa only [ModuleCat.hom_comp, CategoryTheory.Iso.toLinearMap_toLinearEquiv] using this))
  have hsq2 := (comp_inv_of_inv_comp
    ((skChainsIso k X (j + 1) (by omega)).toLinearEquiv)
    ((skChainsIso k X (j + 2) hj).toLinearEquiv)
    ((chainsCpx X).d (j + 2) (j + 1)).hom
    ((chainsCpx ((SSet.sk k).obj X)).d (j + 2) (j + 1)).hom
    (by
      have := congrArg ModuleCat.Hom.hom
        (skChainsIso_d k X (i := j + 1) (by omega : j + 1 + 1 ≤ k))
      simpa only [ModuleCat.hom_comp, CategoryTheory.Iso.toLinearMap_toLinearEquiv] using this))
  exact ker_eq_range_of_comm_iso
    ((skChainsIso k X j (by omega)).symm.toLinearEquiv)
    ((skChainsIso k X (j + 1) (by omega)).symm.toLinearEquiv)
    ((skChainsIso k X (j + 2) hj).symm.toLinearEquiv)
    ((chainsCpx X).d (j + 1) j).hom ((chainsCpx X).d (j + 2) (j + 1)).hom
    ((chainsCpx ((SSet.sk k).obj X)).d (j + 1) j).hom
    ((chainsCpx ((SSet.sk k).obj X)).d (j + 2) (j + 1)).hom
    (by simpa only [CategoryTheory.Iso.toLinearEquiv_symm] using hsq1)
    (by simpa only [CategoryTheory.Iso.toLinearEquiv_symm] using hsq2)
    hex

end LeanCategories.Homological.ChainLevelSteps

