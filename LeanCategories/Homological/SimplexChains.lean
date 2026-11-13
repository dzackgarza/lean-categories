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
# SimplexChains: the standard simplex's chain complex is acyclic in positive degrees

Card `E-HAT-2.2-16` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 2.2, exercise 16.  Certificate: new-qual-site
`proofs/cards/SimplexChains.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; the route is
Mathlib's maintained API, so the port imports it and renames nothing
mathematical.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/SimplexChains.lean`; theorem names keep the certificate's spelling.
-/


/-!
# The standard simplex's chain complex is acyclic in positive degrees

`E-HAT-2.2-16`'s third step needs, among other things, that the augmented chain complex of the
standard simplex be exact, i.e. that `H̃_i(Δ^m) = 0` for `i > 0`. This file proves that from the
maintained API rather than rebuilding chains:

* the standard simplex is an augmented simplicial set carrying an extra degeneracy
  (`SSet.Augmented.StandardSimplex.extraDegeneracy`);
* an extra degeneracy transports along any functor (`ExtraDegeneracy.map`), here the free
  `ℤ`-module functor `ModuleCat.free ℤ`, which sends a simplicial set to its simplicial group of
  chains;
* an extra degeneracy on an augmented simplicial object in a preadditive category makes the
  augmentation a homotopy equivalence onto the complex supported in degree `0`
  (`ExtraDegeneracy.homotopyEquiv`).

Composing these, the chain complex of the standard simplex is homotopy equivalent to a complex
supported in degree zero, so its homology vanishes in every positive degree.

What this file does **not** do, and what `proofs/README.md` §5 continues to record: it does not
compare the normalised and unnormalised models, and it says nothing about the `k`-skeleton maps of
`E-HAT-2.2-16` nor about the barycentric chains. It supplies one of the three things §5 lists.
-/

open CategoryTheory SimplicialObject SimplicialObject.Augmented Limits

namespace LeanCategories.Homological.SimplexChains

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

end LeanCategories.Homological.SimplexChains

