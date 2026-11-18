/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# `IsChamberWithWalls` for the invariant lattice `M^σ` (`#116`, stage 3)

Stage 2 (`FoldingDiagram.lean`) proved that, inside the invariant part of the real form, the folded
roots cut out the trace of a chamber of `W(M)` and are its walls. What was not stated there is the
predicate `IsChamberWithWalls` for the invariant lattice itself (`#23`, `WeylChambers.lean`),
because its root-theoretic fields are not consequences of folding. This file states it, and proves
everything that is *not* arithmetic.

## What is proved here

* `invariantFixedLattice`: the fixed sublattice `M^σ = ker(σ - 1)` as a lattice object with the
  restricted form, and the pairing agreement
  `invariantFixedLattice_realForm_pairing` between its real form and the ambient one. The
  projectivity of the fixed submodule is the Smith-normal-form input that the repository's
  `formedSublattice`/`orthogonalSubmodule` also carry as an instance argument
  (`Submodule.basisOfPid`, `Mathlib/LinearAlgebra/FreeModule/PID.lean:272`); it is not arithmetic.
* `realForm_mem_span_fixed`: **the fixed part of the real form is spanned by the fixed lattice
  vectors**, `V^σ = (M^σ) ⊗ ℝ`. This is the general identification that the predicate needs: it is
  what makes an interior point of the invariant lattice an interior point of the invariant part.
  The proof is the averaging argument, for an arbitrary integral lattice and involution.
* `isChamberWithWalls_invariant`: `IsChamberWithWalls (M^σ)` for the folded root set, from three
  lattice-level inputs — a folded negative reflective root set, an interior lattice point, and the
  completeness of the wall set. Those three are exactly the arithmetic of AEGS §3.7, and
  `chamberOf_invariant_folded` then identifies the chamber with the folded cone.

## The arithmetic input that is *not* here, stated exactly

`isChamberWithWalls_invariant` takes three hypotheses. None of them is a restatement of
`IsChamberWithWalls`: the first is a divisibility statement in `ℤ`, the second an existence
statement about a *lattice* vector, the third a classification statement about the roots of `M^σ`.
They are:

1. `hroots`: every folded vector `α^J` of the chamber's wall set whose square is negative is a
   negative reflective root of `M^σ`, i.e. `(α^J)² ∣ 2 (α^J · v)` for every `v ∈ M^σ`.
   This is **AEGS Lemma 3.4 (printed pp. 11–12), cases (1)–(3)**, together with its divisibility
   argument (`div(α_I) = 2` in `T_En`). It is *not* a formal consequence of folding: the only data
   a general argument could use are `α²`, `α · σα` and the divisibility of `α` itself. Take
   `α² = -4` and `α · σα = -2` (so `(α^J)² = 2(-4) + 2(-2) = -12`) and a fixed `v` with
   `α · v = 2`; since `α^J · v = 2 (α · v) = 4`, integrality of the reflection in `α^J` would need
   `-12 ∣ 2 · 4 = 8`, which fails. So the fold of a reflective root of negative square is not
   reflective in general, and this input has to come from the classification of the roots of the
   particular lattice, as it does in the source. (Hand computation, not formalized.)
2. `hpoint`: an interior *lattice* vector of the folded chamber — `w ∈ M^σ` with `w² > 0` and
   `w · α^J > 0` for every folded root. In the source this is the fundamental chamber `C^J` of
   Lemma 3.8, whose interior is nonempty because `W(Γ_{En,2,e})` is a reflection group with
   finitely many walls (AEGS §3.4, equations (2)–(3), printed p. 10, and the folded diagrams of
   Figures 7–8). A real point is not enough for the predicate's *lattice* presentation, and a
   lattice one is what Vinberg's algorithm produces.
3. `hcomplete`: every negative reflective root of `M^σ` is a nonzero integer multiple of a folded
   root — the completeness of the wall set. This is **AEGS Lemma 3.4's converse**, "vice versa, all
   roots of `T_En` are of these three types" (printed p. 12), proved there from Namikawa
   [Nam85, 2.13 and 2.15]: up to `Γ_En = O(T_En)` there is one type of `(-2)`-vector and two types
   of `(-4)`-vector, so the folded set exhausts the mirrors that can meet the folded chamber.

For the worked lattice `T_dP` of `FoldingEnriques.lean` these three cannot yet be *instantiated*,
and the reason is data, not method: the 19- and 22-vertex Coxeter diagrams `G(T^dP)` of AEGS
Figure 5 (printed p. 11) are printed as pictures; the text tabulates only the relations (4) and (5)
and the two folded diagrams of Figures 7–8. Without the simple roots of that chamber as vectors,
`hroots` and `hcomplete` have no input; `hpoint` likewise. Computing the folded diagrams by folding
(AEGS §3.8) is exactly what those data would certify.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces with a
  numerical polarization of degree 2*, Nagoya Math. J. 259 (2025), arXiv:2312.03638v2, §3.4
  (printed p. 10, equations (2)–(3)), §3.7–3.8 (printed pp. 11–13: Definition 3.3, Lemma 3.4,
  Definition 3.7, Lemma 3.8).
* Y. Namikawa, *Periods of Enriques surfaces*, Math. Ann. 270 (1985), 2.13 and 2.15 (the orbit
  classification of the `(-2)`- and `(-4)`-vectors of `T_En` up to `O(T_En)`), as cited by AEGS.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1, for chambers and their walls.
* E. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972), §1.

## LC-09 record

Searched before writing any declaration: the repository; Mathlib at the pinned head; and the live
Formalization Corpus (`scripts/formalization_corpus.py batch`).

* Repository: `Folding.lean`/`FoldingDiagram.lean` are the only folding; `Sublattice.lean` has
  `formedSublattice`/`orthogonalSubmodule` with `Module.Projective` instance arguments, which is the
  pattern used for `invariantFixedLattice`; nothing states a chamber for a fixed sublattice.
* Mathlib: `LinearMap.IsReflective` (`LinearAlgebra/RootSystem/OfBilinear.lean:41`) is the
  divisibility notion `IsReflectiveRoot` wraps, with no classification;
  `LinearAlgebra/RootSystem/Defs.lean:94` carries `reflectionPerm`, and the finite-type root-system
  API (`RootSystem/Base.lean`, `WeilGroup`-style files) has no statement that the roots of a given
  *indefinite* lattice are reflection-group translates of a chamber's simple roots;
  `LinearAlgebra/FixedSubmodule.lean:32` gives `LinearMap.fixedSubmodule` (our
  `involutionFixedSubmodule`); `LinearAlgebra/FreeModule/PID.lean:272,387` gives the
  Smith-normal-form and finite-torsion-free-freeness inputs used for the projectivity;
  `Algebra/Module/Torsion/Basic.lean` has `Module.IsTorsionFree`. Nothing to port.
* Corpus (`inv1`–`inv5`: invariant sublattice roots, fixed-lattice root system up to the reflection
  group, `IsChamberWithWalls`, roots as translates of simple roots, `(-2)`/`(-4)` classification of
  a 2-elementary lattice): the three narrow formulations return no files; the two broad ones return
  finite-type root-system files (TauCeti `LongestElement`) with no chamber of a fixed lattice and no
  classification of the negative-square vectors of a given lattice. Nothing to import.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-! ## The invariant lattice -/

/-- **The invariant lattice** `M^σ`: the fixed submodule of an involution, with the restricted
form. The `Module.Projective` argument is the Smith-normal-form input that
`formedSublattice`/`orthogonalSubmodule` also take (`Submodule.basisOfPid`). -/
noncomputable def invariantFixedLattice (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] : FiniteProjectiveLatticeCat ℤ ℤ where
  obj := formedSublattice L.obj (involutionFixedSubmodule g)
  property := Module.Finite.of_injective (Submodule.subtype _) fun _ _ h => Subtype.ext h

@[simp] theorem invariantFixedLattice_pairing (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (v w : involutionFixedSubmodule g) :
    (invariantFixedLattice (L := L) g).obj.obj.pairing v w
      = L.obj.obj.pairing (v : L.obj.obj.carrier) (w : L.obj.obj.carrier) := rfl

/-- The pairing of the invariant lattice in the real form is the ambient pairing on the same
lattice vectors. -/
theorem invariantFixedLattice_realForm_pairing (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (v w : involutionFixedSubmodule g) :
    (realForm (invariantFixedLattice (L := L) g)).obj.pairing
        (toRealForm _ (v : (invariantFixedLattice (L := L) g).obj.obj.carrier))
        (toRealForm _ (w : (invariantFixedLattice (L := L) g).obj.obj.carrier))
      = (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier))
          (toRealForm L (w : L.obj.obj.carrier)) := by
  refine (realFormPairing_toRealForm (L := invariantFixedLattice (L := L) g)
    (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)
    (w : (invariantFixedLattice (L := L) g).obj.obj.carrier)).trans ?_
  exact (realFormPairing_toRealForm (L := L) (v : L.obj.obj.carrier)
    (w : L.obj.obj.carrier)).symm

/-- The pairing of two images of lattice vectors in the invariant real form is the invariant
lattice's pairing. -/
theorem invariant_pairing_toRealForm (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (v w : involutionFixedSubmodule g) :
    (realForm (invariantFixedLattice (L := L) g)).obj.pairing
        (toRealForm _ (v : (invariantFixedLattice (L := L) g).obj.obj.carrier))
        (toRealForm _ (w : (invariantFixedLattice (L := L) g).obj.obj.carrier))
      = ((invariantFixedLattice (L := L) g).obj.obj.pairing v w : ℝ) :=
  (invariantFixedLattice_realForm_pairing g v w).trans
    (realFormPairing_toRealForm (L := L) (v : L.obj.obj.carrier) (w : L.obj.obj.carrier))

/-- **The fixed part of the real form is spanned by the fixed lattice vectors**: `V^σ = (M^σ) ⊗ ℝ`.
The averaging argument, in the real form itself: `z + σz` is a sum of multiples of fixed vectors,
and a fixed `z` is half of it. -/
theorem realForm_mem_span_fixed (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    {z : (realForm L).obj.carrier} (hz : realFormOrthogonalHom L g z = z) :
    z ∈ Submodule.span ℝ (Set.range fun v : involutionFixedSubmodule g =>
      toRealForm L (v : L.obj.obj.carrier)) := by
  classical
  set S : Submodule ℝ (realForm L).obj.carrier :=
    Submodule.span ℝ (Set.range fun v : involutionFixedSubmodule g =>
      toRealForm L (v : L.obj.obj.carrier)) with hS
  have hmem : ∀ v : involutionFixedSubmodule g, toRealForm L (v : L.obj.obj.carrier) ∈ S :=
    fun v => Submodule.subset_span ⟨v, rfl⟩
  have hsmul : ∀ (r : ℝ) (m : L.obj.obj.carrier),
      ((r : ℝ) ⊗ₜ[ℤ] m) = r • toRealForm L m := by
    intro r m
    change (r : ℝ) ⊗ₜ[ℤ] m = r • ((1 : ℝ) ⊗ₜ[ℤ] m)
    rw [TensorProduct.smul_tmul']
    simp
  suffices h : ∀ z : (realForm L).obj.carrier, z + realFormOrthogonalHom L g z ∈ S by
    have hz' : z = (1 / 2 : ℝ) • (z + realFormOrthogonalHom L g z) := by
      rw [hz, ← two_smul ℝ z, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
    rw [hz']
    exact S.smul_mem _ (h z)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r m =>
      have hcoe : realFormOrthogonalHom L g ((r : ℝ) ⊗ₜ[ℤ] m) = (r : ℝ) ⊗ₜ[ℤ] (g.1 m) := by
        rw [hsmul r m, map_smul, realFormOrthogonalHom_toRealForm, ← hsmul r (g.1 m)]
      have hfix : (m + g.1 m) ∈ involutionFixedSubmodule g := by
        rw [mem_involutionFixedSubmodule_iff, map_add, isometry_apply_apply g hg, add_comm]
      have hsum : (r : ℝ) ⊗ₜ[ℤ] m + (r : ℝ) ⊗ₜ[ℤ] (g.1 m)
          = r • toRealForm L (m + g.1 m) := by
        change ((r : ℝ) ⊗ₜ[ℤ] m) + ((r : ℝ) ⊗ₜ[ℤ] (g.1 m))
          = r • ((1 : ℝ) ⊗ₜ[ℤ] (m + g.1 m))
        rw [← TensorProduct.tmul_add, TensorProduct.smul_tmul']
        simp
      rw [hcoe]
      exact hsum ▸ S.smul_mem r (hmem ⟨m + g.1 m, hfix⟩)
  | add x y hx hy =>
      convert S.add_mem hx hy using 1
      have hmap := map_add (realFormOrthogonalHom L g) x y
      exact (congrArg (fun w => x + y + w) hmap).trans (by abel)

/-! ## The chamber of the invariant lattice -/

/-- The folded root set as a subset of the invariant lattice. -/
noncomputable def foldedRootSetInvariant (g : OrthogonalGroup L.obj)
    (R : Set L.obj.obj.carrier) : Set (involutionFixedSubmodule g) :=
  {v | (v : L.obj.obj.carrier) ∈ foldedRootSet g R}

theorem mem_foldedRootSetInvariant_iff (g : OrthogonalGroup L.obj)
    (R : Set L.obj.obj.carrier) (v : involutionFixedSubmodule g) :
    v ∈ foldedRootSetInvariant g R ↔ (v : L.obj.obj.carrier) ∈ foldedRootSet g R :=
  Iff.rfl

/-- **`M^σ` is a chamber with the folded walls.** The three hypotheses are the arithmetic inputs of
AEGS §3.7 spelled out in the module docstring: the folded roots are negative reflective roots of
`M^σ` (Lemma 3.4, cases (1)–(3)), an interior lattice vector exists, and the folded roots are a
complete wall set (Lemma 3.4's converse, from Namikawa 2.13/2.15). -/
theorem isChamberWithWalls_invariant (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (R : Set L.obj.obj.carrier)
    (hroots : foldedRootSetInvariant g R ⊆
      negativeReflectiveRoots (invariantFixedLattice (L := L) g))
    (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwv : ∀ v ∈ foldedRootSetInvariant g R,
      0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w v)
    (hcomplete : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ∃ v ∈ foldedRootSetInvariant g R, ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g)
      (toRealForm _ w) (foldedRootSetInvariant g R) := by
  refine ⟨hroots, ⟨toRealForm _ w, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
  · have hQ : 0 < realFormQuadratic (invariantFixedLattice (L := L) g) (toRealForm _ w) := by
      rw [realFormQuadratic_apply]
      rw [invariant_pairing_toRealForm]
      exact_mod_cast hw
    exact hQ
  · have hQ : 0 < realFormQuadratic (invariantFixedLattice (L := L) g) (toRealForm _ w) := by
      rw [realFormQuadratic_apply]
      rw [invariant_pairing_toRealForm]
      exact_mod_cast hw
    rw [associated_self_apply]; exact hQ
  · intro v hv
    have hpair := invariant_pairing_toRealForm (L := L) g w (v : involutionFixedSubmodule g)
    have hpos : (0 : ℝ) < ((invariantFixedLattice (L := L) g).obj.obj.pairing w
        (v : involutionFixedSubmodule g) : ℝ) := by
      exact_mod_cast hwv v hv
    exact hpair ▸ hpos
  · intro z hz
    have hz' : z ∈ positiveCone.upper
        (realFormQuadratic (invariantFixedLattice (L := L) g)) (toRealForm _ w) ∧
        ∀ r ∈ foldedRootSetInvariant g R,
          0 < (realForm (invariantFixedLattice (L := L) g)).obj.pairing z (toRealForm _ r) := hz
    refine (mem_weylRegularLocus_iff (L := invariantFixedLattice (L := L) g)
      (t := toRealForm _ w) (x := z)).mpr ⟨hz'.1, ?_⟩
    intro ρ hρ
    obtain ⟨v, hv, k, hk, rfl⟩ := hcomplete ρ hρ
    have hzsmul : toRealForm (invariantFixedLattice (L := L) g) (k • v)
        = (k : ℝ) • toRealForm (invariantFixedLattice (L := L) g) v :=
      toRealForm_zsmul (L := invariantFixedLattice (L := L) g) k
        (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)
    have step : (realForm (invariantFixedLattice (L := L) g)).obj.pairing z
        ((k : ℝ) • toRealForm (invariantFixedLattice (L := L) g) v)
        = (k : ℝ) * (realForm (invariantFixedLattice (L := L) g)).obj.pairing z
          (toRealForm (invariantFixedLattice (L := L) g) v) := by
      change (realForm (invariantFixedLattice (L := L) g)).obj.bilinMap z
          ((k : ℝ) • toRealForm (invariantFixedLattice (L := L) g) v)
        = (k : ℝ) * (realForm (invariantFixedLattice (L := L) g)).obj.bilinMap z
          (toRealForm (invariantFixedLattice (L := L) g) v)
      rw [map_smul, smul_eq_mul]
    refine hzsmul.symm ▸ step ▸ ?_
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk) (ne_of_gt (hz'.2 v hv))

/-- **The invariant chamber is the folded chamber**: at an interior point, the chamber of the
invariant lattice is the cone cut out by the folded roots. -/
theorem chamberOf_invariant_folded (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (R : Set L.obj.obj.carrier)
    (hroots : foldedRootSetInvariant g R ⊆
      negativeReflectiveRoots (invariantFixedLattice (L := L) g))
    (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwv : ∀ v ∈ foldedRootSetInvariant g R,
      0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w v)
    (hcomplete : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ∃ v ∈ foldedRootSetInvariant g R, ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v)
    (hpos : (integralSignature (invariantFixedLattice (L := L) g)).1 = 1)
    {z : (realForm (invariantFixedLattice (L := L) g)).obj.carrier}
    (hz : z ∈ rootInteriorCone (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (foldedRootSetInvariant g R)) :
    chamberOf (invariantFixedLattice (L := L) g) (toRealForm _ w) z =
      rootInteriorCone (invariantFixedLattice (L := L) g) (toRealForm _ w)
        (foldedRootSetInvariant g R) := by
  have hQ : 0 < realFormQuadratic (invariantFixedLattice (L := L) g) (toRealForm _ w) := by
    rw [realFormQuadratic_apply]
    rw [invariant_pairing_toRealForm]
    exact_mod_cast hw
  exact IsChamberWithWalls.chamberOf_eq (L := invariantFixedLattice (L := L) g)
    (t := toRealForm _ w) hpos hQ
    (isChamberWithWalls_invariant g R hroots w hw hwv hcomplete) hz

end LeanCategories.Lattices.Valued
