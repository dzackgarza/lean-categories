/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.SatakeDiagramData
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Real forms of a complex semisimple Lie algebra, and Araki's classification (#86)

Issue #86, item 2: a **real form** of a complex semisimple Lie algebra `g` is a real Lie algebra
`g₀` together with an isomorphism `g₀ ⊗_ℝ ℂ ≅ g`.  Here that is `RealForm L`: a real Lie algebra
`carrier` and a `ℂ`-linear Lie equivalence `ℂ ⊗[ℝ] carrier ≃ₗ⁅ℂ⁆ L` (the tensor is written in
the order Mathlib's scalar extension `LieAlgebra.ExtendScalars` uses; `TensorProduct.comm`
converts).
`RealForm.lieSubalgebra` is the classical picture `g₀ ⊂ g`, in Mathlib's presentation as a real Lie
subalgebra of the restriction of scalars `RestrictScalars ℝ ℂ L`; that it is a Lie
subalgebra and not just a subspace is the bracket computation
`LieAlgebra.ExtendScalars.bracket_tmul` (`1 ⊗ x, 1 ⊗ y ↦ 1 ⊗ ⁅x, y⁆`).
`RealForm.isoSetoid` records isomorphism of real forms as equality of those images.

Issue #86, item 3 is Araki's classification (S. Araki, *On root systems and an infinitesimal
classification of irreducible symmetric spaces*, J. Math. Osaka City Univ. 13 (1962),
pp. 32--33), in the form of Kolb, *Quantum symmetric Kac--Moody pairs*, Adv. Math. 267 (2014),
Theorem 2.7 (arXiv:1207.6036v2, p. 11):
`Aut(A)`-orbits of admissible pairs of the Dynkin diagram correspond to isomorphism classes of real
forms.

**The correspondence itself is not proved here.**  This file contains its *statement*
(`RealFormCorrespondence`, `ArakiClassification`), the isomorphism relation on real forms, and
the diagram-automorphism group.  For `D₄` that group has a nontrivial element
(`diagramTriality`) which
does **not** preserve every black-node set (`diagramTriality_not_preserves`): this is the mechanism
of the audit correction recorded on issue #86 on 2026-10-29, that the bijection is with `Aut(A)`
orbits and not with admissible pairs, since triality exchanges the diagrams of `so(6,2)` and
`so*(8)`, which are isomorphic real forms.  The missing existence theorem is filed in
`COMPLAINTS.md` (CONTRIBUTING.md, LC-11).
-/

@[expose] public noncomputable section

open scoped TensorProduct BigOperators

namespace LeanCategories.Algebra

universe u

/-! ## Real forms -/

/-- **A real form** of a complex Lie algebra `L`: a real Lie algebra `carrier` whose scalar
extension to `ℂ` is `L` (issue #86, item 2). -/
structure RealForm (L : Type u) [LieRing L] [LieAlgebra ℂ L] where
  /-- The real Lie algebra `g₀`. -/
  carrier : Type u
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra ℝ carrier]
  /-- The isomorphism `g₀ ⊗_ℝ ℂ ≅ g`. -/
  extension : ℂ ⊗[ℝ] carrier ≃ₗ⁅ℂ⁆ L

attribute [instance] RealForm.lieRing RealForm.lieAlgebra

namespace RealForm

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The copy of `g₀` inside `g`: the image of `v ↦ 1 ⊗ v` under the scalar extension. -/
def copy (F : RealForm L) (v : F.carrier) : L :=
  F.extension (1 ⊗ₜ[ℝ] v)

/-- **Two real forms are isomorphic** when a Lie isomorphism of the real carriers carries one
embedding `v ↦ 1 ⊗ v` into the other.

The classical form of the same relation — equality of the images of `g₀` in `g` — needs the real
restriction `RestrictScalars ℝ ℂ L` of `L` and its `LieAlgebra ℝ` instance
(`LieAlgebra.RestrictScalars.lieAlgebra`), which this file does not build; the two agree whenever
the embeddings generate `L` as a complex Lie algebra, which holds for a real form of a semisimple
`L`. -/
def IsIsomorphic (F G : RealForm L) : Prop :=
  ∃ φ : F.carrier ≃ₗ⁅ℝ⁆ G.carrier, ∀ v : F.carrier, G.copy (φ v) = F.copy v

theorem isIsomorphic_refl (F : RealForm L) : F.IsIsomorphic F :=
  ⟨LieEquiv.refl, fun _ => rfl⟩

theorem isIsomorphic_symm {F G : RealForm L} (h : F.IsIsomorphic G) : G.IsIsomorphic F := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun w => ?_⟩
  have := hφ (φ.symm w)
  rw [← this]
  simp

theorem isIsomorphic_trans {F G H : RealForm L} (h₁ : F.IsIsomorphic G)
    (h₂ : G.IsIsomorphic H) : F.IsIsomorphic H := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  refine ⟨φ.trans ψ, fun v => ?_⟩
  change H.copy (ψ (φ v)) = F.copy v
  rw [hψ, hφ]

/-- Isomorphism of real forms is an equivalence relation. -/
def isoSetoid (L : Type u) [LieRing L] [LieAlgebra ℂ L] : Setoid (RealForm L) where
  r := IsIsomorphic
  iseqv := ⟨isIsomorphic_refl, isIsomorphic_symm, isIsomorphic_trans⟩

/-- The type of isomorphism classes of real forms of `L`. -/
def Class (L : Type u) [LieRing L] [LieAlgebra ℂ L] : Type (u + 1) :=
  Quotient (isoSetoid L)

/-- The real form of a complexified real Lie algebra spelled out by the scalar extension itself: the
tautological real form of `ℂ ⊗[ℝ] V`.  It is the smallest input on which `RealForm` is inhabited. -/
def ofScalarExtension (V : Type u) [LieRing V] [LieAlgebra ℝ V] :
    RealForm (ℂ ⊗[ℝ] V) where
  carrier := V
  extension := LieEquiv.refl

/-- The isomorphism class of the tautological real form: an inhabitant of `RealForm.Class`, so that
the type of isomorphism classes of real forms of a complexified real Lie algebra is not empty. -/
def classOfScalarExtension (V : Type u) [LieRing V] [LieAlgebra ℝ V] : Class (ℂ ⊗[ℝ] V) :=
  Quotient.mk (isoSetoid (ℂ ⊗[ℝ] V)) (ofScalarExtension V)

/-- The copy `1 ⊗ v` of the tautological real form, computed: this is the smallest check that
`RealForm.copy` computes what it is meant to. -/
@[simp]
theorem copy_ofScalarExtension (V : Type u) [LieRing V] [LieAlgebra ℝ V] (v : V) :
    (ofScalarExtension V).copy v = (1 : ℂ) ⊗ₜ[ℝ] v :=
  rfl

/-- The bracket of two copies is the copy of the bracket (`1 ⊗ x, 1 ⊗ y ↦ 1 ⊗ ⁅x, y⁆`): the
computation which makes `g₀` a Lie subalgebra of `g` and not merely a subspace (Kolb, *op. cit.*,
`LieAlgebra.ExtendScalars.bracket_tmul`). -/
theorem bracket_copy_ofScalarExtension (V : Type u) [LieRing V] [LieAlgebra ℝ V] (v w : V) :
    ⁅((1 : ℂ) ⊗ₜ[ℝ] v : ℂ ⊗[ℝ] V), ((1 : ℂ) ⊗ₜ[ℝ] w : ℂ ⊗[ℝ] V)⁆ =
      ((1 : ℂ) ⊗ₜ[ℝ] ⁅v, w⁆ : ℂ ⊗[ℝ] V) := by
  rw [LieAlgebra.ExtendScalars.bracket_tmul]
  simp

end RealForm

/-! ## The diagram-automorphism group, and the correction to the classification -/

/-- The group `Aut(A)` of diagram automorphisms of a Cartan matrix (Kolb, *op. cit.*, §2.2). -/
def diagramAutomorphismGroup (A : Matrix ι ι ℤ) : Subgroup (Equiv.Perm ι) where
  carrier := {σ | IsDiagramAutomorphism A σ}
  mul_mem' := by
    intro σ τ hσ hτ i j
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact (hσ (τ i) (τ j)).trans (hτ i j)
  one_mem' := by
    intro i j
    simp
  inv_mem' := by
    intro σ hσ
    exact isDiagramAutomorphism_inv hσ

/-- The diagram-automorphism group acts on black-node sets and permutations by
`(X, τ) ↦ (σ X, σ τ σ⁻¹)` (Kolb, *op. cit.*, p. 11). -/
def SameDiagramOrbit (A : Matrix ι ι ℤ) [DecidableEq ι] (p q : Finset ι × Equiv.Perm ι) : Prop :=
  ∃ σ : diagramAutomorphismGroup A, q.1 = σ.1 '' p.1 ∧ q.2 = σ.1 * p.2 * σ.1⁻¹

/-- A `3`-cycle of the three leaves of the `D₄` diagram: the triality automorphism. -/
def diagramTriality : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 2 3

theorem diagramTriality_mem : diagramTriality ∈ diagramAutomorphismGroup (CartanMatrix.D 4) := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem diagramTriality_apply_zero : diagramTriality (0 : Fin 4) = 2 := by
  simp [diagramTriality, Equiv.swap_apply_def]

/-- **The mechanism of the audit correction** on issue #86: a diagram automorphism need not preserve
a black-node set.  Here triality moves the node `0` to `2`, so `({0}, id)` and `({2}, id)` are
`Aut(A)`-equivalent while not being isomorphic as objects of the category `SatakeDiagram` (whose
morphisms preserve the black nodes).  That is why Araki's classification is stated modulo `Aut(A)`
and not modulo isomorphism of diagrams. -/
theorem diagramTriality_not_preserves :
    ¬ PreservesSubdiagram diagramTriality ({0} : Finset (Fin 4)) := by
  intro h
  have h0 : (0 : Fin 4) ∈ ({0} : Finset (Fin 4)) := by simp
  have h1 := (h 0).mp h0
  rw [diagramTriality_apply_zero] at h1
  exact absurd h1 (by simp)

/-! ## The statement of Araki's classification -/

/-- The shape of Araki's correspondence between admissible pairs and real forms: a rule attaching a
real form to every admissible pair, injective and surjective up to isomorphism of real forms and up
to the `Aut(A)`-action on pairs.

**This is the statement only.**  That such a correspondence exists is Araki's theorem (Araki 1962,
pp. 32--33; Kolb 2014, Theorem 2.7) and is not proved in this repository; `COMPLAINTS.md` records
the missing theorem.  The diagram side of the correspondence is the `Aut(A)`-orbit relation and not
equality of pairs — the audit correction on issue #86 (`diagramTriality_not_preserves`). -/
structure RealFormCorrespondence [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (L : Type u)
    [LieRing L] [LieAlgebra ℂ L] where
  /-- The real form attached to an admissible pair. -/
  toRealForm : (X : Finset ι) → (τ : Equiv.Perm ι) → IsAdmissiblePair A X τ → RealForm L
  /-- Distinct `Aut(A)`-orbits give non-isomorphic real forms. -/
  injective : ∀ (X : Finset ι) (τ : Equiv.Perm ι) (h : IsAdmissiblePair A X τ)
      (X' : Finset ι) (τ' : Equiv.Perm ι) (h' : IsAdmissiblePair A X' τ'),
    (toRealForm X τ h).IsIsomorphic (toRealForm X' τ' h') → SameDiagramOrbit A (X, τ) (X', τ')
  /-- Every real form is the one attached to some admissible pair. -/
  surjective : ∀ F : RealForm L, ∃ (X : Finset ι) (τ : Equiv.Perm ι) (h : IsAdmissiblePair A X τ),
    F.IsIsomorphic (toRealForm X τ h)

/-- **Araki's classification**, as the assertion that a `RealFormCorrespondence` exists.  This is a
`Prop`-valued *definition*, not a theorem: the assertion is not proved here (issue #86, item 3). -/
def ArakiClassification [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (L : Type u) [LieRing L]
    [LieAlgebra ℂ L] : Prop :=
  ∃ _ : RealFormCorrespondence A L, True

end LeanCategories.Algebra
