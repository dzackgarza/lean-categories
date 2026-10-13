/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.ProfiniteIntegerData
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.GroupTheory.Index

/-!
# Abstract normalized-degree data

Definition-level realization of Neukirch FC09-C04-U045.

For the fixed continuous degree map `d : G → Z-hat` and an abstract field
`K` represented by a closed subgroup `G_K`, Neukirch defines

* `f_K = (Z-hat : d(G_K))`,
* `e_K = (I : I_K)`, with `I = ker d` and `I_K = G_K ∩ I`, and
* when `f_K` is finite, `d_K = (1 / f_K) d`.

The accepted reference constructs a bundled continuous homomorphism only after
proving that `d(G_K) = f_K Z-hat`.  That image classification, together with
surjectivity, the kernel computation, and the induced maximal-unramified
quotient equivalence, is result content.  Sweep III therefore records the two
indices and the raw normalization formula only.

The local profinite-integer carrier is multiplicative because it is the
profinite completion of `Multiplicative Z`.  Thus multiplication by `n` in
additive `Z-hat` is represented by the power map `z ↦ z ^ n`.  As for the
existing raw Herbrand inverse, `Function.invFun` records the selected inverse
without requiring the later range and inverse-law proofs.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The image `d(G_K)` of the subgroup representing the abstract field
`K`. -/
def abstractDegreeImageData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G) :
    Subgroup serreProfiniteIntegerData :=
  K.toSubgroup.map d.toMonoidHom

/-- The abstract inertia subgroup over `K`,
`I_K = G_K ∩ ker(d)`.

In Neukirch's fixed-field notation this subgroup represents the maximal
unramified extension `K-tilde / K`. -/
def abstractFieldInertiaData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G) :
    Subgroup G :=
  K.toSubgroup ⊓ d.toMonoidHom.ker

/-- The coset type whose cardinality is Neukirch's absolute residue index
`f_K = (Z-hat : d(G_K))`. -/
def abstractResidueQuotientData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G) : Type :=
  (⊤ : Subgroup serreProfiniteIntegerData) ⧸
    (abstractDegreeImageData d K).subgroupOf
      (⊤ : Subgroup serreProfiniteIntegerData)

/-- Neukirch's absolute residue index
`f_K = (Z-hat : d(G_K))`, retained as an honest cardinal so an infinite
index is not collapsed to zero. -/
def abstractResidueDegreeData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G) : Cardinal :=
  Cardinal.mk (abstractResidueQuotientData d K)

/-- The coset type whose cardinality is Neukirch's absolute ramification index
`e_K = (I : I_K)`. -/
def abstractRamificationQuotientData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G) : Type u :=
  d.toMonoidHom.ker ⧸
    (abstractFieldInertiaData d K).subgroupOf d.toMonoidHom.ker

/-- Neukirch's absolute ramification index `e_K = (I : I_K)`, again as an
honest cardinal. -/
def abstractRamificationIndexData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G) : Cardinal :=
  Cardinal.mk (abstractRamificationQuotientData d K)

/-- At the finite-residue boundary, the natural number underlying `f_K`.

The `Finite` instance is exactly Neukirch's hypothesis that `f_K` is
finite; positivity and comparison with the cardinal-valued index are
result-layer facts. -/
def finiteAbstractResidueDegreeData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G)
    [Finite (abstractResidueQuotientData d K)] : ℕ :=
  Nat.card (abstractResidueQuotientData d K)

/-- Multiplication by `n` on additive `Z-hat`, written on the local
multiplicative carrier. -/
def profiniteIntegerMulNatData (n : ℕ) :
    serreProfiniteIntegerData → serreProfiniteIntegerData :=
  fun z => z ^ n

/-- Raw division by `n` on `Z-hat`: a selected inverse to multiplication
by `n`.

On the range of multiplication by `n`, the later inverse-law theorem
identifies this selected value with the unique quotient intended by the
source.  No such proposition is needed to form the Sweep-III datum. -/
def profiniteIntegerDivNatData (n : ℕ) :
    serreProfiniteIntegerData → serreProfiniteIntegerData :=
  Function.invFun (profiniteIntegerMulNatData n)

/-- Neukirch's raw normalized-degree formula
`d_K = (1 / f_K) d` for a field of finite residue degree.

The source subsequently proves that every `d(k)` lies in the
`f_K`-multiple range and that this raw function is a continuous surjective
homomorphism with kernel `I_K`.  Those propositions are deliberately not
constructor fields here. -/
def abstractNormalizedDegreeData
    (d : G →ₜ* serreProfiniteIntegerData) (K : ClosedSubgroup G)
    [Finite (abstractResidueQuotientData d K)] :
    K.toSubgroup → serreProfiniteIntegerData :=
  fun k =>
    profiniteIntegerDivNatData (finiteAbstractResidueDegreeData d K) (d k.1)

end LeanCategories.Algebra
