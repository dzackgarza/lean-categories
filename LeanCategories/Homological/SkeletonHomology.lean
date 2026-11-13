/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Flat.Equalizer

@[expose] public section

/-!
# SkeletonHomology: the k-skeleton of the standard simplex is acyclic below degree k

Card `E-HAT-2.2-16` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 2.2, exercise 16.  Certificate: new-qual-site
`proofs/cards/SkeletonHomology.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; the route is
Mathlib's maintained API, so the port imports it and renames nothing
mathematical.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/SkeletonHomology.lean`; theorem names keep the certificate's spelling.
-/


/-!
# `E-HAT-2.2-16`: the `k`-skeleton of the standard simplex is acyclic below degree `k`

The card computes the ranks of the standard simplex's cycles and boundaries and then passes to its
`k`-skeleton. Its third step needs three things, two of which are certified in
`cards/SimplexChains.lean` (the simplex's augmented exactness) and `cards/ChainLevelSteps.lean`
(the `k`-skeleton's differentials agreeing with the simplex's in degrees at most `k`). This file
composes them into the card's sentence, `H̃_i((Δ^m)^k) = 0` for `i < k`, and in doing so it repeats
their statements: a file in `proofs/cards/` cannot import its sibling, so the shared lemmas are
copied in, as the directory's convention requires.

The composition is not the `ker ∂ = im ∂` transport. Mathlib states exactness of a homological
complex at a degree, `K.ExactAt i`, as exactness of the three-term complex `K.sc i`, and
`K.exactAt_iff'` identifies that with `(K.sc' (i+1) i (i-1)).Exact`; an isomorphism of those
three-term complexes therefore transports exactness by `ShortComplex.exact_of_iso`, with no
`Submodule`/`LinearEquiv` plumbing at all. `scIso` is that isomorphism — the three chain-group
isomorphisms and the two differential squares — and `skExactAt` is the transport.

What this file does **not** do: it says nothing about the barycentric chains, for which the pin has
neither `SSet.B` nor `sd ⟶ B` (`AlgebraicTopology/SimplicialSet/Subdivision.lean:19-23`), and it
does not compare the normalised and unnormalised models beyond what `cards/SimplexChains.lean`
already does.
-/

open CategoryTheory Opposite Simplicial SimplicialObject SimplicialObject.Augmented Limits

namespace LeanCategories.Homological.SkeletonHomology

/-! ## The simplex's chain complex is acyclic in positive degrees (from `cards/SimplexChains.lean`)
  -/

/-- The standard `m`-simplex, as an augmented simplicial set. -/
noncomputable abbrev stdSimplex (m : ℕ) : SSet.Augmented :=
  SSet.Augmented.stdSimplex.obj (SimplexCategory.mk m)

/-- The simplicial group of chains on the standard `m`-simplex: the free abelian group functor
applied to `stdSimplex m`. -/
noncomputable abbrev chains (m : ℕ) : SimplicialObject.Augmented (ModuleCat ℤ) :=
  ((Augmented.whiskering Type (ModuleCat ℤ)).obj (ModuleCat.free ℤ)).obj (stdSimplex m)

/-- The extra degeneracy on the standard simplex, transported along the free abelian group functor.
This is what makes the augmented chain complex of the simplex contractible. -/
noncomputable def chainsExtraDegeneracy (m : ℕ) : ExtraDegeneracy (chains m) :=
  (SSet.Augmented.StandardSimplex.extraDegeneracy (SimplexCategory.mk m)).map
    (ModuleCat.free ℤ)

/-- **The chain complex of the standard simplex is homotopy equivalent to one supported in degree
zero.** This is `ExtraDegeneracy.homotopyEquiv` applied to the transported extra degeneracy; it
carries all of the content, and nothing is assumed. -/
noncomputable def chainsHomotopyEquiv (m : ℕ) :
    HomotopyEquiv
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (chains m)))
      ((ChainComplex.single₀ (ModuleCat ℤ)).obj (point.obj (chains m))) :=
  ExtraDegeneracy.homotopyEquiv (chainsExtraDegeneracy m)

/-- **The augmented chain complex of the standard simplex is exact in positive degrees**, i.e.
`H̃_i(Δ^m) = 0` for `i ≠ 0`. The homotopy equivalence of `chainsHomotopyEquiv` identifies the
homology with that of a complex supported in degree `0`, which vanishes in every other degree
(`isZero_single_obj_homology`). -/
theorem isZero_homology (m : ℕ) (i : ℕ) (hi : i ≠ 0) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (chains m))).homology i) :=
      by
  have h : IsZero (((ChainComplex.single₀ (ModuleCat ℤ)).obj
      (point.obj (chains m))).homology i) := by
    have h' := HomologicalComplex.isZero_single_obj_homology (C := ModuleCat ℤ)
      (c := ComplexShape.down ℕ) (j := 0) (point.obj (chains m)) i hi
    simpa using h'
  exact h.of_iso ((chainsHomotopyEquiv m).toHomologyIso i)

/-- **The augmentation computes the zeroth homology.** `H_0` of the simplex's chain complex is the
target `ℤ` of the augmentation, via the augmentation itself; that is the form `ker ε = im ∂_1` takes
here, since `H_0` is `ker ∂_0 / im ∂_1` and `ker ∂_0 = X_0`. -/
noncomputable def homologyZeroIso (m : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (chains m))).homology 0 ≅
      point.obj (chains m) :=
  ((chainsHomotopyEquiv m).toHomologyIso 0).trans (by
    have h := HomologicalComplex.singleObjHomologySelfIso (C := ModuleCat ℤ)
      (c := ComplexShape.down ℕ) (j := 0) (point.obj (chains m))
    simpa using h)

/-- **The Dold–Kan comparison**, at the point this file needs: for any simplicial object in an
abelian category — here the chains on the standard simplex — the normalized Moore complex and the
alternating face map complex are homotopy equivalent. This is maintained API
(`DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`), so the normalized and
unnormalized models are not merely related by a comparison map here: they have the same homotopy
type, hence the same homology. -/
noncomputable def normalizedHomotopyEquiv (m : ℕ) :
    HomotopyEquiv
      ((AlgebraicTopology.normalizedMooreComplex (ModuleCat ℤ)).obj (drop.obj (chains m)))
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (chains m))) :=
  AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

/-- The normalized Moore complex of the simplex's chains is homotopy equivalent to a complex
supported in degree zero. -/
noncomputable def normalizedChainsHomotopyEquiv (m : ℕ) :
    HomotopyEquiv
      ((AlgebraicTopology.normalizedMooreComplex (ModuleCat ℤ)).obj (drop.obj (chains m)))
      ((ChainComplex.single₀ (ModuleCat ℤ)).obj (point.obj (chains m))) :=
  (normalizedHomotopyEquiv m).trans (chainsHomotopyEquiv m)

/-- **The normalized complex of the standard simplex is acyclic in positive degrees as well**, so
`H̃_i(Δ^m) = 0` for `i ≠ 0` holds in both models and the choice of model does not matter here. -/
theorem isZero_normalizedHomology (m : ℕ) (i : ℕ) (hi : i ≠ 0) :
    IsZero (((AlgebraicTopology.normalizedMooreComplex (ModuleCat ℤ)).obj
      (drop.obj (chains m))).homology i) := by
  have h : IsZero (((ChainComplex.single₀ (ModuleCat ℤ)).obj
      (point.obj (chains m))).homology i) := by
    have h' := HomologicalComplex.isZero_single_obj_homology (C := ModuleCat ℤ)
      (c := ComplexShape.down ℕ) (j := 0) (point.obj (chains m)) i hi
    simpa using h'
  exact h.of_iso ((normalizedChainsHomotopyEquiv m).toHomologyIso i)
/-! ## The skeleton's chain groups and differentials in degrees at most `k` (from
  `cards/ChainLevelSteps.lean`) -/

open CategoryTheory Opposite Simplicial

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
/-! ## The card's sentence

`E-HAT-2.2-16` asks that the `k`-skeleton of the standard `m`-simplex have
$\widetilde H_i = 0$ for $i < k$. The two halves above are the ingredients: the simplex's chain
complex is acyclic in positive degrees, and the skeleton's chain groups and differentials agree
with it in degrees at most `k`. What is left is that they compose, and it is
`K.exactAt_iff'`/`ShortComplex.exact_of_iso` on the one hand and
`HomologicalComplex.exactAt_iff_isZero_homology` on the other — not the `ker = range` form.

Note the degree bookkeeping. `sc' (j + 2) (j + 1) j` is the three-term complex
`C_{j+2} → C_{j+1} → C_j`, so exactness of it is `ExactAt (j + 1)`, and `j + 2 ≤ k` is exactly
the hypothesis under which the three degrees and the two differentials are compared. Naming the
middle degree `i = j + 1`, that is `i + 1 ≤ k`, which is where the card's `i < k` lives.
-/

/-- The standard `m`-simplex, as the simplicial set the chain complex is built on: the underlying
simplicial set of the augmented object carrying the extra degeneracy. -/
noncomputable abbrev simplexSet (m : ℕ) : SSet := drop.obj (stdSimplex m)

/-- **The three-term complexes at a degree agree.** For `j + 2 ≤ k` the chain groups of `X` and of
its `k`-skeleton agree in degrees `j`, `j + 1`, `j + 2` (`skChainsIso`) and so do the two
differentials between them (`skChainsIso_d`), which is exactly a commuting square at each step of
`ShortComplex.isoMk`. -/
noncomputable def scIso (k : ℕ) (X : SSet.{0}) {j : ℕ} (hj : j + 2 ≤ k) :
    (chainsCpx X).sc' (j + 2) (j + 1) j ≅
      (chainsCpx ((SSet.sk k).obj X)).sc' (j + 2) (j + 1) j :=
  ShortComplex.isoMk (skChainsIso k X (j + 2) hj) (skChainsIso k X (j + 1) (by omega))
    (skChainsIso k X j (by omega))
    (skChainsIso_d k X (i := j + 1) (by omega)) (skChainsIso_d k X (i := j) (by omega))

/-- **Exactness at a degree transports to the `k`-skeleton**, short-complex form. -/
theorem skExactAt (k : ℕ) (X : SSet.{0}) {j : ℕ} (hj : j + 2 ≤ k)
    (h : (chainsCpx X).ExactAt (j + 1)) : (chainsCpx ((SSet.sk k).obj X)).ExactAt (j + 1) := by
  rw [HomologicalComplex.exactAt_iff' (K := chainsCpx X) (j := j + 1) (i := j + 2) (k := j)
      (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff' (K := chainsCpx ((SSet.sk k).obj X)) (j := j + 1)
      (i := j + 2) (k := j) (by simp) (by simp)]
  exact ShortComplex.exact_of_iso (scIso k X hj) h

/-- Whiskering an augmented simplicial object by a functor and then dropping is the free functor
applied to the dropped object, so the chain complex above is `chainsCpx` of the underlying
simplicial set of the standard simplex. -/
theorem simplexCpx_eq (m : ℕ) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (chains m)) =
      chainsCpx (simplexSet m) := rfl

/-- **The simplex's chain complex is exact in positive degrees**, in the short-complex form the
transport takes: this is `isZero_homology` read through `exactAt_iff_isZero_homology`. -/
theorem exactAt_simplex (m : ℕ) (j : ℕ) : (chainsCpx (simplexSet m)).ExactAt (j + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ← simplexCpx_eq m]
  exact isZero_homology m (j + 1) (by omega)

/-- **`E-HAT-2.2-16`'s sentence: the `k`-skeleton of the standard simplex is acyclic below degree
`k`.** For `j + 2 ≤ k`, i.e. for every degree `i = j + 1` with `i + 1 ≤ k`, the homology of the
`k`-skeleton's chain complex vanishes in degree `i` — that is `H̃_i((Δ^m)^k) = 0` for `i > 0`,
since the reduced and ordinary homology agree away from degree zero. -/
theorem isZero_skHomology (m k j : ℕ) (hj : j + 2 ≤ k) :
    IsZero ((chainsCpx ((SSet.sk k).obj (simplexSet m))).homology (j + 1)) :=
  HomologicalComplex.ExactAt.isZero_homology (skExactAt k (simplexSet m) hj (exactAt_simplex m j))

end LeanCategories.Homological.SkeletonHomology

