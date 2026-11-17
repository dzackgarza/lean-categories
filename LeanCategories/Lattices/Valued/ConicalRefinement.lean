/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FibreRefinement
public import LeanCategories.Lattices.Valued.ConicalMemberDescent
public import LeanCategories.Lattices.Valued.SemifanArrangement
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Support inclusion along a refinement of the conical locus (Looijenga, Lemma 6.6, p. 30)

E. Looijenga, *Compactifications defined by arrangements II: the locally symmetric varieties of
type IV*, arXiv math/0201218v2 (2002), text version
`.tmp-sources/looijenga-math0201218v2.md`:

> Lemma 6.6 (text line 821). Let `Σ'` be a `Γ`-invariant admissible decomposition of the conical
> locus that is refined by `Σ`. Given `σ ∈ Σ`, let `σ'` be the smallest member of `Σ'` that
> contains `σ`. Then `V_σ ⊂ V_{σ'}`, so that we have a factorization of `D → π_{σ'}D` over
> `π_σ D`.

The parent issue is lean-categories#162; this module is the part owed by #169. The source calls the
proof of the lemma straightforward. It is not: the refinement the lemma needs carries a *covering*
clause that the source's definitions do not state, and lean-categories#174 decides that the clause
is not derivable from them but that every decomposition the source constructs has it — so refinement
for these objects includes it, and the arrangement instance is proved. See "The refinement relation"
below, and "What is not in this module" for the gap that leaves.

The three steps the source leaves implicit are:

1. **the insertion lemma** (`IsLocallyRationalDecomposition.le_of_isRelintPoint`, and its leastness
   form `eq_of_isLeastMem_of_isRelintPoint`): a member of a decomposition that contains a point of
   the *relative interior* of another member contains that member, and a *least* member containing
   such a point is that member. The proof is the face axiom alone — two members of a locally
   rational decomposition meet along a common face
   (`inf_isFaceOf_of_isLocallyRationalDecomposition`), and a face of a cone that meets its relative
   interior is the cone;
2. **the subordinate refinement** of the support index of Lemma-Definition 4.5
   (`exists_subordinate_of_isRelintPoint`): the hypothesis `Semifan.sigmaSupportSpace_le_of_refines`
   consumes — every coarse member above `σ` meeting the open cone contains a fine member above `σ`
   meeting it — is produced by the insertion lemma as soon as the fine member in question meets the
   *relative interior* of the coarse one. `Semifan.sigmaSupportSpace_le_of_refines` then gives
   `J_Σ ⊆ J_{Σ'}` at the half line of a plane, which is Lemma 6.6 in case (ii);
3. **the line case** (`vSigma_le_of_carrier_subset_of_isCaseIFibre`,
   `vSigma_le_of_refines_conicalLocus`): for a member `σ` of a fibre that Definition 6.1 (i) covers,
   the support space of any member of an admissible decomposition whose *carrier* in `⋀²V(ℝ)`
   contains the carrier of `σ` contains `vSigma` of `σ`. This is the one case of Lemma 6.6 that
   crosses strata, and it is where the ambient refinement — containment of members in the conical
   locus, not a same-fibre containment — is consumed.

## The refinement relation: containment *and* covering

`RefinesConicalLocus` below is the source's hypothesis "`Σ'` is refined by `Σ`" at the geometric
object, in the form lean-categories#174 decides: **two** fields, `containment` — every member of the
finer collection lies, as a cone of the conical locus inside `⋀²V(ℝ)`, in a member of the coarser
one, which is the source's own gloss at text line 603 — and `covering` (`CoversConicalLocus`) —
every coarse member is the union of the fine members it contains. The second is not in the source:
Definition 4.2 (`:481`) asks only that the union of a decomposition's members be `C₊`, the §4 gloss
is containment only, and Lemma 6.6 is stated without proof. #174 decides that covering is **not
derivable** from Definition 4.2 and Definition 6.1 as stated, that **every decomposition the source
constructs has it** (`Σ(bb)` and `Σ(ℋ)` are stratifications of `C₊`), and that refinement for these
objects therefore includes it. That is a definitional choice justified by the constructions, not an
assumption inside a theorem; the docstring of `CoversConicalLocus` records the decision and the
source lines, and the arrangement instance is *proved* here
(`arrangementDecomposition_eq_sUnion_of_mem`, `semifanArrangement_refinesConicalLocus`).

`RefinesConicalLocus` is *not* `FibreRefinement.RefinesLocus`, which relates the two families fibre
by fibre and is therefore a strictly stronger hypothesis on each fibre and no statement at all
across strata; and it is not `Semifan.sigmaSupportSpace_le_of_refines`'s support-index domination,
which assumes a containment between supports.

## What is not in this module: the general-class gap

**Looijenga's Lemma 6.6 for an arbitrary pair of admissible decompositions is not derivable from his
definitions, and this module does not assert it.** The covering clause is carried for the pairs the
programme uses and proved for arrangement families; the statement for a general admissible pair
would need either covering as an extra hypothesis on the pair (which is what the field is) or a
construction argument that the source does not give. This is #174's decision, recorded here rather
than repaired: the pages that cite Lemma 6.6 cite it through the arrangement instance.

Two further links are carried as hypotheses rather than proved, each recorded at its declaration:
the clause of Definition 6.1 (ii) that `C_{J,+}` *is a member* of every admissible decomposition
(the source's parenthetical "(so that the cone `C_{J,+} = C̄_J` in `⋀²J` is member of `Σ`)", which
`IsAdmissibleDecomposition` does not carry), and the identification of Definition 6.1 (i)'s span
formula at an isotropic half line with the plane support space `J_Σ` of case (ii).
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The insertion lemma: a relative interior point determines its member

Looijenga, Definition 4.2, p. 17, gives a locally rational decomposition as a collection of cones
whose restriction to every rational subcone is a rational cone system, and a rational cone system
(`IsRationalConeSystem`) meets along common faces. Of the two facts the insertion lemma needs, the
first is exactly that axiom; the second is that a face of a cone containing a point of its relative
interior is the cone. Together they say that a member cannot *cross* another: a member is contained
in every member that reaches any of its relative interior points.

The relative interior is taken in the cone-theoretic sense, as the complement of the union of the
proper faces — `IsRelintPoint` below, which is the form in which the insertion lemma is used and the
only form the face axioms see. It does not need a topology on `realified V`, and it does not need a
notion of relative interior for convex sets. -/

/-- **A relative interior point of a cone `σ`**: a point of `σ` that lies in no *proper* face of
`σ`. This is the cone-theoretic relative interior — the complement, inside `σ`, of the union of its
proper faces — and it is the hypothesis under which the insertion lemma runs: a face of `σ`
containing such a point is `σ` itself. -/
def IsRelintPoint (σ : PointedCone ℝ (realified V)) (y : realified V) : Prop :=
  y ∈ σ ∧ ∀ F : PointedCone ℝ (realified V), F.IsFaceOf σ → y ∈ F → F = σ

omit [Module.Finite ℚ V] in
theorem isRelintPoint_iff {σ : PointedCone ℝ (realified V)} {y : realified V} :
    IsRelintPoint σ y ↔
      y ∈ σ ∧ ∀ F : PointedCone ℝ (realified V), F.IsFaceOf σ → y ∈ F → F = σ :=
  Iff.rfl

omit [Module.Finite ℚ V] in
/-- A relative interior point is a point of the cone. -/
theorem IsRelintPoint.mem {σ : PointedCone ℝ (realified V)} {y : realified V}
    (h : IsRelintPoint σ y) : y ∈ σ := h.1

omit [Module.Finite ℚ V] in
/-- No proper face of `σ` contains a relative interior point of `σ`. -/
theorem IsRelintPoint.eq_of_isFaceOf {σ : PointedCone ℝ (realified V)} {y : realified V}
    (h : IsRelintPoint σ y) {F : PointedCone ℝ (realified V)} (hF : F.IsFaceOf σ) (hy : y ∈ F) :
    F = σ := h.2 F hF hy

omit [Module.Finite ℚ V] in
/-- **The insertion lemma, Looijenga Definition 4.2, p. 17**: if two members of a locally rational
decomposition are given and the second contains a relative interior point of the first, then the
first is contained in the second.

The proof is the decomposition's face axiom. The intersection `σ ⊓ σ'` of the two members is a face
of `σ` (`inf_isFaceOf_of_isLocallyRationalDecomposition`, the pairwise-incidence half of Definition
4.1's rational cone system), it contains the relative interior point `y`, and a face of `σ` that
meets the relative interior is `σ`; hence `σ ⊓ σ' = σ`, i.e. `σ ≤ σ'`.

**The equality `σ' = σ` is not available and is false.** The facial decomposition `Σ(bb)` of a fibre
(Looijenga, Example 6.2, p. 29) is an admissible decomposition and contains the boundary half line
`C_{J,+}` together with `C_{I,+} ⊋ C_{J,+}`; `C_{I,+}` contains every point of the relative interior
of `C_{J,+}` and is not `C_{J,+}`. What the insertion lemma gives, and all that Lemma 6.6 of
Looijenga's source uses, is the containment; the *leastness* hypothesis, which turns it into
equality, is `eq_of_isLeastMemPoint_of_isRelintPoint` below. -/

theorem IsLocallyRationalDecomposition.le_of_isRelintPoint {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {σ σ' : PointedCone ℝ (realified V)} (hσ : σ ∈ S) (hσ' : σ' ∈ S) {y : realified V}
    (hy : IsRelintPoint σ y) (hy' : y ∈ σ') : σ ≤ σ' := by
  have hface : (σ ⊓ σ').IsFaceOf σ :=
    inf_isFaceOf_of_isLocallyRationalDecomposition hS hσ hσ'
  have heq : σ ⊓ σ' = σ := hy.2 (σ ⊓ σ') hface ⟨hy.1, hy'⟩
  exact inf_eq_left.1 heq

/-! ## The least containing member of a point, and the equality form

Definition 6.1's "let `σ'` be the smallest member of `Σ'` that contains `σ`" is what turns the
insertion lemma into an equality: a least member containing a relative interior point of `σ` is
`σ`. The next two declarations supply that form, at a point rather than at a cone, because that is
the shape in which the plane case of Lemma 6.6 uses it (a half line's relative interior point is
contained in the half line, and the least member containing it is the half line). -/

omit [Module.Finite ℚ V] in
/-- **Nested members of a locally rational decomposition are faces of each other.** If `σ ≤ τ` and
both are members, then `σ = σ ⊓ τ` is a face of `τ` by the pairwise-incidence half of the rational
cone system (`inf_isFaceOf_of_isLocallyRationalDecomposition`).

This is the axiom that excludes a *nested pair of cones that are not face-incident* from being a
locally rational decomposition at all, and with it the family that `HasSubordinateRefinement`'s
refutation was built on in the previous round: take `C₊` together with a proper sub-wedge
`τ = C₊ ⊓ {φ ≥ 0}` (cut by a half-space, so `τ ⊓ C₊ = τ` is *not* a face of `C₊`). As members of
one decomposition they would have to satisfy `τ.IsFaceOf C₊` by this lemma, and the restriction of
Definition 4.2 to the rational subcone `C₊` requires exactly that face incidence; so the pair is not
locally rational, and the coarse `{C̄, τ}`-shaped families of
`tests/regression/ConicalRefinementSplit22.lean` are not admissible. -/
theorem IsLocallyRationalDecomposition.isFaceOf_of_le {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {σ τ : PointedCone ℝ (realified V)} (hσ : σ ∈ S) (hτ : τ ∈ S) (h : σ ≤ τ) :
    σ.IsFaceOf τ := by
  have hface : (σ ⊓ τ).IsFaceOf τ := by
    rw [inf_comm]
    exact inf_isFaceOf_of_isLocallyRationalDecomposition hS hτ hσ
  rwa [inf_eq_left.2 h] at hface

omit [Module.Finite ℚ V] in
/-- **Two members of a locally rational decomposition whose relative interiors meet are equal.**
Given `x` in the relative interior of both `σ` and `τ`, the insertion lemma gives `σ ≤ τ` (from
`x ∈ relint σ` and `x ∈ τ`) and `τ ≤ σ` (from `x ∈ relint τ` and `x ∈ σ`), so the two coincide.

This is the relative interiors being pairwise disjoint, and it is what makes `τ ↦` "the member whose
relative interior contains `x`" well defined on a locally rational decomposition. It is a
consequence of the face axiom through `le_of_isRelintPoint`; no field of
`IsLocallyRationalDecomposition` beyond `restriction` (via
`inf_isFaceOf_of_isLocallyRationalDecomposition`) is used, and in particular no partition of `C₊` by
relative interiors has to be assumed. -/
theorem IsLocallyRationalDecomposition.eq_of_common_isRelintPoint {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {σ τ : PointedCone ℝ (realified V)} (hσ : σ ∈ S) (hτ : τ ∈ S) {x : realified V}
    (hxσ : IsRelintPoint σ x) (hxτ : IsRelintPoint τ x) : σ = τ :=
  le_antisymm (hS.le_of_isRelintPoint (σ := σ) (σ' := τ) hσ hτ hxσ hxτ.1)
    (hS.le_of_isRelintPoint (σ := τ) (σ' := σ) hτ hσ hxτ hxσ.1)

omit [Module.Finite ℚ V] in
/-- **The member whose relative interior contains a point is unique**: two members of a locally
rational decomposition whose relative interiors both contain `x` are the same member. -/
theorem IsLocallyRationalDecomposition.existsUnique_mem_isRelintPoint
    {C : PointedCone ℝ (realified V)} {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S) {x : realified V}
    (hx : ∃ σ ∈ S, IsRelintPoint σ x) :
    ∃! σ : PointedCone ℝ (realified V), σ ∈ S ∧ IsRelintPoint σ x := by
  obtain ⟨σ, hσ, hxσ⟩ := hx
  refine ⟨σ, ⟨hσ, hxσ⟩, ?_⟩
  rintro τ ⟨hτ, hxτ⟩
  exact (hS.eq_of_common_isRelintPoint (σ := σ) (τ := τ) (x := x) hσ hτ hxσ hxτ).symm

/-- **`σ'` is the least member of `S` containing the point `y`**. This is the point form of
`FibreRefinement.IsLeastMem`, and the shape in which the insertion lemma is used: the source's
"smallest member of `Σ'` that contains `σ`" is the least member containing `σ`'s relative interior
points. -/
structure IsLeastMemPoint (S : Set (PointedCone ℝ (realified V))) (y : realified V)
    (σ' : PointedCone ℝ (realified V)) : Prop where
  /-- `σ'` is a member. -/
  mem : σ' ∈ S
  /-- `σ'` contains the point. -/
  mem_point : y ∈ σ'
  /-- `σ'` lies below every member containing the point. -/
  least : ∀ ⦃τ⦄, τ ∈ S → y ∈ τ → σ' ≤ τ

omit [Module.Finite ℚ V] in
/-- The least member containing a point is unique, so that it is a function of the point. -/
theorem IsLeastMemPoint.eq {S : Set (PointedCone ℝ (realified V))} {y : realified V}
    {σ₁ σ₂ : PointedCone ℝ (realified V)} (h₁ : IsLeastMemPoint S y σ₁)
    (h₂ : IsLeastMemPoint S y σ₂) : σ₁ = σ₂ :=
  le_antisymm (h₁.least h₂.mem h₂.mem_point) (h₂.least h₁.mem h₁.mem_point)

omit [Module.Finite ℚ V] in
/-- **The insertion lemma at the least member**: the least member of a locally rational
decomposition containing a relative interior point of a member `σ` of it *is* `σ`. This is the
form of Lemma 6.6's "smallest member" that the plane case consumes: the least member containing a
point of the relative interior of `C_{J,+}` is `C_{J,+}` itself, provided `C_{J,+}` is a member. -/
theorem IsLocallyRationalDecomposition.eq_of_isLeastMemPoint {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {σ σ' : PointedCone ℝ (realified V)} (hσ : σ ∈ S) {y : realified V}
    (hy : IsRelintPoint σ y) (hleast : IsLeastMemPoint S y σ') : σ' = σ :=
  le_antisymm (hleast.least hσ hy.1) (hS.le_of_isRelintPoint hσ hleast.mem hy hleast.mem_point)

/-! ## The same, for an admissible decomposition of the conical locus

`IsAdmissibleDecomposition` supplies the locally rational decomposition of each conical fibre as
condition (i) of Definition 6.1 (p. 28), and `ConicalLine.closure` is by definition the rational
closure of the fibre's cone, which is the form `inf_isFaceOf_of_isLocallyRationalDecomposition`
takes. So the insertion lemma transports to the conical locus with no further input, and it is at
that level that Lemma 6.6 uses it. -/

omit [Module.Finite ℚ V] in
/-- **The insertion lemma at a conical fibre** (Looijenga, Definition 6.1 (i), p. 28, and
Definition 4.2, p. 17): if two members of the decomposition of the fibre of a `ℚ`-isotropic line
are given and the second contains a relative interior point of the first, the first lies in the
second. -/
theorem IsAdmissibleDecomposition.le_of_isRelintPoint {BQ : LinearMap.BilinForm ℚ V}
    {Q : QuadraticForm ℝ (realified V)} {Γ : Set (V ≃ₗ[ℚ] V)}
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (D : IsAdmissibleDecomposition BQ Q Γ locus) (F : ConicalLine BQ Q)
    {σ σ' : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F) (hσ' : σ' ∈ locus F)
    {y : realified ↥F.space} (hy : IsRelintPoint σ y) (hy' : y ∈ σ') : σ ≤ σ' :=
  IsLocallyRationalDecomposition.le_of_isRelintPoint (C := F.cone) (D.condition_i F) hσ hσ' hy hy'

omit [Module.Finite ℚ V] in
/-- **The insertion lemma at a conical fibre, leastness form**: the least member of the fibre's
decomposition containing a relative interior point of the member `σ` is `σ`. -/
theorem IsAdmissibleDecomposition.eq_of_isLeastMemPoint {BQ : LinearMap.BilinForm ℚ V}
    {Q : QuadraticForm ℝ (realified V)} {Γ : Set (V ≃ₗ[ℚ] V)}
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (D : IsAdmissibleDecomposition BQ Q Γ locus) (F : ConicalLine BQ Q)
    {σ σ' : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F) {y : realified ↥F.space}
    (hy : IsRelintPoint σ y) (hleast : IsLeastMemPoint (locus F) y σ') : σ' = σ :=
  IsLocallyRationalDecomposition.eq_of_isLeastMemPoint (C := F.cone) (D.condition_i F) hσ hy hleast

/-! ## Rational cones are closed

The pairwise-incidence axiom is not the only thing a locally rational decomposition inherits from
its members' being *rational* cones: a rational cone is finitely generated
(`IsRationalCone` is `∃ s : Finset V, σ = PointedCone.hull ℝ (rationalPoint '' s)`), and a
finitely generated cone is closed. The repository's support-space lemmas carry closedness as the
hypothesis `hclosed : ∀ τ ∈ S, IsClosed τ` (`LocallyRationalDecomposition.lean:4873` and four
further places); this section removes that hypothesis.

The route is the file's own duality port rather than a compactness argument. A finitely generated
cone equals its algebraic bipolar (`Submodule.FG.cone_dual_dual_flip_id`,
`LeanCategories/ForMathlib/PointedConeFiniteDuality.lean:75`, ported from TauCeti/Mei), and a dual
cone with respect to a continuous perfect pairing is closed (`PointedCone.isClosed_dual`). The
compactness route — the cone hull of `{c : ι → ℝ≥0 | ∑ c = 1} × [0,1]` — does *not* work as stated:
the cone hull of a compact convex set need not be closed (a disc tangent to the origin has the open
half-plane plus the origin as its cone hull), and what saves the finitely generated case is precisely
Minkowski–Weyl, which is what the bipolarity encodes. -/

omit [Module.Finite ℚ V] in
/-- **A rational cone is closed.** This is the closedness the support-space comparison consumes
(`LocallyRationalDecomposition.lean:4873, 4929, 5029, 5059, 5084` carry it as a hypothesis):
finite generation gives the bipolarity `σ = (σ^∘)^∘`, and a dual cone for a continuous perfect
pairing is closed. -/
theorem IsRationalCone.isClosed {σ : PointedCone ℝ (realified V)} (hσ : IsRationalCone σ) :
    IsClosed (σ : Set (realified V)) := by
  obtain ⟨s, hs⟩ := hσ
  have hFG : Submodule.FG σ := by
    rw [hs]
    exact Submodule.fg_span (s.finite_toSet.image _)
  rw [← hFG.cone_dual_dual_flip_id (K := ℝ) (V := realified V)]
  exact PointedCone.isClosed_dual
    (p := (LinearMap.id : Module.Dual ℝ (realified V) →ₗ[ℝ] Module.Dual ℝ (realified V)))
    (fun x => by simpa using IsModuleTopology.continuous_of_linearMap x)

/-! ## The subordinate refinement of the support index (Lemma-Definition 4.5, p. 19)

`Semifan.sigmaSupportSpace_le_of_refines` compares the support space of one member `σ` relative to
two decompositions, and it consumes the hypothesis that *every* coarse member above `σ` meeting the
open cone contains a fine member above `σ` meeting it. That hypothesis is containment of *members*,
not support-index domination, and this section names it (`HasSubordinateRefinement`), shows it is
reflexive, and states the support inclusion at a half line through it
(`sigmaSupportSpace_le_of_hasSubordinateRefinement`).

**The status of the hypothesis: it is not implied by Definition 6.1 (i)--(ii).** The family that
shows this is the one below, in the split model of signature `(2,2)`
(`tests/regression/ConicalRefinementSplit22.lean`, `tests/regression/ConicalPlaneSplit22.lean`). Let
`W = ℚ⁴` carry `x₀y₁ + x₁y₀ − x₂y₃ − x₃y₂`, let `I = ⟨e₀⟩` with partner `e₁`, so that the fibre
`I^⊥/I = ⟨e₂, e₃⟩` carries `−2x₂x₃` of signature `(1,1)` with closed cone `C̄ = ⟨e₂, −e₃⟩`; let
`τ = ⟨e₂, e₂ − e₃⟩ ⊊ C̄`; take `Σ` to have members `{C̄, τ} ∪ faces(τ) ∪ {−e₃}` at the fibre of `I`
and the facial decomposition at every other fibre, with `Γ` trivial.

* Definition 6.1 (i) **passes**: at the fibre of `I` the members are a locally rational decomposition
  of `C_{I,+}` (union `C̄`, face-closed, finite restrictions), and at every other fibre it is `Σ(bb)`.
* Definition 6.1 (ii) **passes**: for the plane `J₁ = ⟨e₀, e₂⟩` the support space of `C_{J₁,+}`
  relative to the family at `I` is the common zero set of the forms `β x₃` with `β ≤ 0` — namely
  `⟨e₂⟩` in the fibre, i.e. `J₁` — and `J₁^⊥ = J₁`; for `J₂ = ⟨e₀, e₃⟩` the members above its half
  line are `C̄` alone, whose support space is `⟨e₃⟩`, i.e. `J₂ = J₂^⊥`. Both equalities are those of
  `Σ(bb)`'s values at every other line, so the independence holds.
* `HasSubordinateRefinement` **fails** for this `Σ` against a coarse `Σ'` whose fibre member above the
  half line is a proper sub-wedge `[0, ε]`: the fine members above the half line are `τ` (wider) and
  `C̄`, and neither lies in `[0, ε]`.

So the hypothesis is genuinely extra as a hypothesis, and it is not derivable from Definition 6.1.
That is half of what lean-categories#174 decides; the other half is that every decomposition the
source constructs *does* satisfy the covering clause, so refinement for these objects carries it
(`RefinesConicalLocus.covering`), and the subordinate refinement is then a theorem of the covering
clause rather than an extra hypothesis: `exists_subordinate_of_isRelintPoint` below, whose witness
is the fine member that covering inserts through a relative interior point of `σ`, the insertion
lemma upgrading that point membership to containment. The plane case of Lemma 6.6 is stated from it
(`vSigmaPlane_le_of_covers`), for an arbitrary coarse family rather than only the Baily–Borel one.

**Why the insertion lemma alone cannot supply it.** The insertion lemma compares two members of one
family: the rational-cone-system axiom it uses — two members meet along a common face — is an axiom
*within* a decomposition, and there is no counterpart relating a member of one decomposition to a
member of another. The only cross-family input is the refinement itself, and what the covering
clause adds is a same-family member to apply the insertion lemma to.
-/

section Subordinate

variable {C : Set (realified V)} {Cpb : PointedCone ℝ (realified V)}
  {S S' : Set (PointedCone ℝ (realified V))}

/-- **The subordinate refinement of a support index**: every member of the coarse family above `σ`
that meets the open cone contains a member of the fine family above `σ` that meets it. This is
verbatim the hypothesis of `Semifan.sigmaSupportSpace_le_of_refines`, named here so that its status
is explicit. It is a statement about *members*; no support space, support index or containment of
support spaces occurs in it.

**It is not derivable from Definition 6.1, and it is derived from the covering clause instead.** The
section docstring above gives the family that decides the first half: on the split model of
signature `(2,2)` the members `{C̄, τ} ∪ faces` at the fibre of `I = ⟨e₀⟩` pass both conditions of
Definition 6.1 (with `Γ` trivial) and fail this hypothesis against a coarse family whose member
above the half line is a proper sub-wedge. The second half is lean-categories#174's decision:
refinement for the decompositions the source constructs carries the covering clause, and
`exists_subordinate_of_isRelintPoint` below produces this hypothesis from it.
`tests/regression/ConicalRefinementSplit22.lean` exercises the line case, which consumes neither. -/
def HasSubordinateRefinement (C : Set (realified V)) (S S' : Set (PointedCone ℝ (realified V)))
    (σ : PointedCone ℝ (realified V)) : Prop :=
  ∀ τ' : supportIndex C S' σ, ∃ τ ∈ S, σ ≤ τ ∧ τ ≤ τ'.1 ∧
    ((τ : Set (realified V)) ∩ C).Nonempty

omit [Module.Finite ℚ V] in
theorem hasSubordinateRefinement_iff {σ : PointedCone ℝ (realified V)} :
    HasSubordinateRefinement C S S' σ ↔
      ∀ τ' : supportIndex C S' σ, ∃ τ ∈ S, σ ≤ τ ∧ τ ≤ τ'.1 ∧
        ((τ : Set (realified V)) ∩ C).Nonempty :=
  Iff.rfl

omit [Module.Finite ℚ V] in
/-- **A decomposition subordinates itself**: at every member `τ'` of the index the member `τ'`
itself is the witness, since it lies above `σ` and meets the open cone by membership in the index.
So `HasSubordinateRefinement C S σ` is not a vacuous requirement, and the support comparison of
Lemma-Definition 4.5 is unconditional at every member meeting the open cone. -/
theorem hasSubordinateRefinement_self {σ : PointedCone ℝ (realified V)} :
    HasSubordinateRefinement C S S σ :=
  fun τ' => ⟨τ'.1, τ'.2.1, τ'.2.2.1, le_rfl, τ'.2.2.2⟩

omit [Module.Finite ℚ V] in
/-- **The support inclusion at a half line, from the subordinate refinement**: if the fine family
subordinates the coarse one above `σ`, and the fine index is nonempty, then the support space of `σ`
relative to the fine decomposition is contained in that relative to the coarse one. This is the
`J_Σ ⊆ J_{Σ'}` half of Lemma 6.6, p. 30, and it is exactly
`Semifan.sigmaSupportSpace_le_of_refines` read at `HasSubordinateRefinement`. -/
theorem sigmaSupportSpace_le_of_hasSubordinateRefinement {σ : PointedCone ℝ (realified V)}
    (hidx : supportIndex C S σ) (h : HasSubordinateRefinement C S S' σ) :
    sigmaSupportSpace C S σ ≤ sigmaSupportSpace C S' σ :=
  sigmaSupportSpace_le_of_refines hidx h

end Subordinate

/-! ## The carrier in `⋀²V(ℝ)` across two fibres

The line case of Lemma 6.6 is the one case in which the coarse member containing a member `σ` need
not lie in `σ`'s fibre, so the comparison of support spaces cannot be read off a containment of
cones. What the carrier gives instead is a comparison of 2-vectors:
`e ∧ ĉ = e' ∧ ĉ'` for `e = rationalPoint F.gen`, `ĉ` a vector of `σ`, and `e'`, `ĉ'` the
corresponding vectors of the coarse member. The two lemmas below turn that into
`span{e, ĉ} = span{e', ĉ'}`: the contraction `x ↦ g(x₀)x₁ - g(x₁)x₀` of a linear functional `g`,
factored through the universal property of `⋀²` (`insertWedge`), reads both spans off one equation.

Looijenga's §1B (p. 11) is where the 2-vector `e ∧ c` comes from; the contraction is the standard
Hodge-style insertion `⋀²V ⊗ V* → V`, and Mathlib has neither a name nor this identity for it
(`Mathlib.LinearAlgebra.Contraction` is the tensor product `V* ⊗ V → R`, not the exterior
contraction — LC-09), hence its construction here.
-/

section ExteriorContraction

omit [Module.Finite ℚ V] in
/-- `(1 : Fin 2) ≠ 0`, without a `DecidableEq` instance on `Fin 2` in scope. -/
theorem fin_two_one_ne_zero : (1 : Fin 2) ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp at this

omit [Module.Finite ℚ V] in
/-- `(0 : Fin 2) ≠ 1`, without a `DecidableEq` instance on `Fin 2` in scope. -/
theorem fin_two_zero_ne_one : (0 : Fin 2) ≠ 1 := by
  intro h; have := congrArg Fin.val h; simp at this

/-- **The insertion of a linear functional into a 2-vector**, as an alternating map:
`v ↦ g(v₀) • v₁ - g(v₁) • v₀`. Factoring it through `⋀²` is `insertWedge` below. -/
noncomputable def insertAlt (g : realified V →ₗ[ℝ] ℝ) :
    realified V [⋀^Fin 2]→ₗ[ℝ] realified V where
  toFun v := g (v 0) • v 1 - g (v 1) • v 0
  map_update_add' := by
    intro inst m i x y
    letI := inst
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [Function.update_self, Function.update_of_ne fin_two_one_ne_zero,
        Function.update_self, Function.update_of_ne fin_two_one_ne_zero,
        Function.update_self, Function.update_of_ne fin_two_one_ne_zero,
        map_add, add_smul, smul_add]
      module
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [Function.update_self, Function.update_of_ne fin_two_zero_ne_one,
        Function.update_self, Function.update_of_ne fin_two_zero_ne_one,
        Function.update_self, Function.update_of_ne fin_two_zero_ne_one,
        map_add, add_smul, smul_add]
      module
  map_update_smul' := by
    intro inst m i c x
    letI := inst
    fin_cases i
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [Function.update_self, Function.update_of_ne fin_two_one_ne_zero,
        Function.update_self, Function.update_of_ne fin_two_one_ne_zero,
        map_smul, smul_sub, smul_smul, smul_smul]
      rw [RingHom.id_apply]
      module
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [Function.update_self, Function.update_of_ne fin_two_zero_ne_one,
        Function.update_self, Function.update_of_ne fin_two_zero_ne_one,
        map_smul, smul_sub, smul_smul]
      rw [RingHom.id_apply]
      module
  map_eq_zero_of_eq' := by
    intro v i j hij hijne
    fin_cases i <;> fin_cases j
    · exact absurd rfl hijne
    · simp only [Fin.zero_eta, Fin.mk_one] at hij ⊢
      rw [hij, sub_self]
    · simp only [Fin.zero_eta, Fin.mk_one] at hij ⊢
      rw [← hij, sub_self]
    · exact absurd rfl hijne

/-- **The contraction `⋀²V(ℝ) → V` along a linear functional**: the insertion `insertAlt g` read on
the exterior square through its universal property. -/
noncomputable def insertWedge (g : realified V →ₗ[ℝ] ℝ) :
    ⋀[ℝ]^2 (realified V) →ₗ[ℝ] realified V :=
  exteriorPower.alternatingMapLinearEquiv (insertAlt g)

omit [Module.Finite ℚ V] in
/-- The contraction reads a wedge as the insertion: `g ↦ (g a) • b - (g b) • a`. -/
theorem insertWedge_apply (g : realified V →ₗ[ℝ] ℝ) (a b : realified V) :
    insertWedge g (wedgeTwo a b) = g a • b - g b • a := by
  rw [insertWedge, wedgeTwo, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

omit [Module.Finite ℚ V] in
/-- The insertion of a 2-vector is its wedge with the two vectors swapped, negated. -/
theorem wedgeTwo_swap_eq (a b : realified V) : wedgeTwo b a = -wedgeTwo a b := by
  have hcomp : (![b, a] : Fin 2 → realified V)
      = ![a, b] ∘ ⇑(Equiv.swap 0 1) := by
    funext i; fin_cases i <;> simp
  rw [wedgeTwo, wedgeTwo, hcomp, AlternatingMap.map_swap _ _ (by decide)]

omit [Module.Finite ℚ V] in
/-- A 2-vector that is a wedge of two vectors is zero exactly when they are dependent, in the form
needed below: if `u` lies in the line spanned by `v` then `u ∧ v = 0`. -/
theorem wedgeTwo_eq_zero_of_mem_span {u v : realified V}
    (hu : u ∈ Submodule.span ℝ ({v} : Set (realified V))) : wedgeTwo u v = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
  change exteriorPower.ιMulti ℝ 2 (![t • v, v] : Fin 2 → realified V) = 0
  rw [show (![t • v, v] : Fin 2 → realified V)
      = Function.update (![v, v] : Fin 2 → realified V) 0 (t • v) from by
    funext i; fin_cases i <;> simp]
  change (exteriorPower.ιMulti ℝ 2).toMultilinearMap
    (Function.update (![v, v] : Fin 2 → realified V) 0 (t • v)) = 0
  rw [MultilinearMap.map_update_smul (exteriorPower.ιMulti ℝ 2).toMultilinearMap
    (![v, v] : Fin 2 → realified V) 0 t v]
  rw [show Function.update (![v, v] : Fin 2 → realified V) 0 v = ![v, v] from by
    funext i; fin_cases i <;> simp]
  have hvv : (exteriorPower.ιMulti ℝ 2).toMultilinearMap (![v, v] : Fin 2 → realified V) = 0 :=
    AlternatingMap.map_eq_zero_of_eq (exteriorPower.ιMulti ℝ 2) (![v, v] : Fin 2 → realified V)
      (i := 0) (j := 1) rfl (by decide)
  rw [hvv, smul_zero]

omit [Module.Finite ℚ V] in
/-- A nonzero 2-vector cannot be a wedge with a dependent factor: `u ∉ ℝ v` when `u ∧ v ≠ 0`. -/
theorem notMem_span_of_wedgeTwo_ne {u v : realified V} (h : wedgeTwo u v ≠ 0) :
    u ∉ Submodule.span ℝ ({v} : Set (realified V)) :=
  fun hu => h (wedgeTwo_eq_zero_of_mem_span hu)

omit [Module.Finite ℚ V] in
/-- A vector outside a line is separated from it by a linear functional normalized to `1`. -/
theorem exists_dual_one_zero {u v : realified V}
    (hu : u ∉ Submodule.span ℝ ({v} : Set (realified V))) :
    ∃ g : realified V →ₗ[ℝ] ℝ, g u = 1 ∧ g v = 0 := by
  obtain ⟨f, hf0, hfker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := Submodule.span ℝ ({v} : Set (realified V)))
      hu (inferInstance : Module.Projective ℝ
        (realified V ⧸ Submodule.span ℝ ({v} : Set (realified V))))
  have hfv : f v = 0 := by
    have hmem : f v ∈ (Submodule.span ℝ ({v} : Set (realified V))).map f :=
      ⟨v, Submodule.subset_span (Set.mem_singleton v), rfl⟩
    rw [hfker] at hmem
    simpa using hmem
  refine ⟨(f u)⁻¹ • f, ?_, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf0]
  · simp only [LinearMap.smul_apply, hfv, smul_eq_mul, mul_zero]

omit [Module.Finite ℚ V] in
/-- **Faithfulness of the wedge on a pair, in the span form used by the line case**: two nonzero
2-vectors that are equal are wedges of the same plane. Both vectors of the first pair lie in the
span of the second. -/
theorem wedgeTwo_span_le {a b a' b' : realified V} (h : wedgeTwo a b = wedgeTwo a' b')
    (hne : wedgeTwo a b ≠ 0) :
    a ∈ Submodule.span ℝ ({a', b'} : Set (realified V)) ∧
      b ∈ Submodule.span ℝ ({a', b'} : Set (realified V)) := by
  classical
  obtain ⟨g₁, hg₁a, hg₁b⟩ :=
    exists_dual_one_zero (notMem_span_of_wedgeTwo_ne (v := b) hne)
  obtain ⟨g₂, hg₂b, hg₂a⟩ :=
    exists_dual_one_zero (notMem_span_of_wedgeTwo_ne (v := a)
      (by rw [wedgeTwo_swap_eq]; exact neg_ne_zero.2 hne))
  have hb : b = g₁ a • b - g₁ b • a := by
    simp only [hg₁a, hg₁b, one_smul, zero_smul, sub_zero]
  have ha : a = g₂ b • a - g₂ a • b := by
    simp only [hg₂b, hg₂a, one_smul, zero_smul, sub_zero]
  have hb' : b' ∈ Submodule.span ℝ ({a', b'} : Set (realified V)) :=
    Submodule.subset_span (by simp)
  have ha' : a' ∈ Submodule.span ℝ ({a', b'} : Set (realified V)) :=
    Submodule.subset_span (by simp)
  have hmem₁ : g₁ a' • b' - g₁ b' • a' ∈ Submodule.span ℝ ({a', b'} : Set (realified V)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hb') (Submodule.smul_mem _ _ ha')
  have hmem₂ : g₂ a' • b' - g₂ b' • a' ∈ Submodule.span ℝ ({a', b'} : Set (realified V)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hb') (Submodule.smul_mem _ _ ha')
  refine ⟨?_, ?_⟩
  · rw [ha, ← insertWedge_apply g₂ b a, wedgeTwo_swap_eq a b, h, ← wedgeTwo_swap_eq a' b',
      insertWedge_apply g₂ b' a']
    have : g₂ b' • a' - g₂ a' • b' = -(g₂ a' • b' - g₂ b' • a') := by module
    rw [this]
    exact Submodule.neg_mem _ hmem₂
  · rw [hb, ← insertWedge_apply g₁ a b, h, insertWedge_apply g₁ a' b']
    exact hmem₁

end ExteriorContraction

/-! ## The line case of Lemma 6.6 on actual admissible decompositions

Definition 6.1 (i), p. 28, gives `V_σ` by the span formula for a member of a fibre that is not an
isotropic half line, and the span formula is monotone in the member (`ConicalLocus.vSigma_mono`).
The passage from that monotonicity to Lemma 6.6 has two halves: the refinement must give a member
of the coarse decomposition above `σ` (that is `RefinesConicalLocus`, the source's relation between
the two collections), and the identity `V_σ = I ⊕ ⟨σ⟩` must survive the change of fibre when the
coarse member lies in another stratum. The second half is the content below: the carrier equation
of the two members reads `e ∧ c = e' ∧ c'`, and `wedgeTwo_span_le` turns it into
`span{e, c} = span{e', c'}`, so both summands of `vSigma F σ` lie in `vSigma F' σ'`.
-/

section LineCase

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The line `I` of a fibre is transverse to the fibre's own space**: the generator of the
isotropic line does not lie in the real form of the complement `I^⊥/I`'s carrier
`F.space = ⟨gen, partner⟩^⊥`. This is what makes `e ∧ c` detect `c`: `e ∧ c = 0` forces
`c ∈ ℝ e`, and no nonzero vector of the fibre is there. -/
theorem lineSpan_inf_realify_space (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    lineSpan F ⊓ realify F.space = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx1
  have hval : (associated Q) (rationalPoint F.partner) (r • rationalPoint F.gen)
      = r * (BQ F.partner F.gen : ℝ) := by
    rw [LinearMap.map_smul, smul_eq_mul, hBQ]
  have hzero : (associated Q) (rationalPoint F.partner) (r • rationalPoint F.gen) = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_
      ((mem_realify_iff F.space (r • rationalPoint F.gen)).1 hx2)
    · rintro _ ⟨w, hw, rfl⟩
      rw [hBQ]
      have hw0 : BQ F.partner w = 0 := ((ConicalLine.mem_space_iff F).1 hw).2
      rw [hw0]
      simp
    · simp
    · intro y z _ _ hy hz
      rw [map_add, hy, hz, add_zero]
    · intro a y _ hy
      rw [map_smul, hy, smul_eq_mul, mul_zero]
  rw [hval] at hzero
  have hpair : (BQ F.partner F.gen : ℝ) = 1 := by
    rw [LinearMap.BilinForm.IsSymm.eq hBsym, F.pairing]; norm_num
  rw [hpair, mul_one] at hzero
  rw [hzero, zero_smul]

set_option maxHeartbeats 1000000 in
-- The carrier equation and the two span computations elaborate slowly at the default limit.
/-- **Lemma 6.6, p. 30, at one member of Definition 6.1 (i), across strata**: if the carrier in
`⋀²V(ℝ)` of a nonzero member `σ` of the fibre of `I` is contained in the carrier of a member `σ'` of
the fibre of `I'` — the two lines possibly different — then `V_σ ⊆ V_{σ'}`. The hypothesis `hne`
is not decoration: the apex has carrier `{0}` and is contained in every carrier, while its support
space is `{0}`; the statement is about the case (i) members of Definition 6.1.

Nothing here uses that the fibres agree. That is the point: the source's inclusion is a statement
about the two support spaces, and the carrier comparison is enough to force each summand of the span
formula into the coarse support space. -/
theorem vSigma_le_of_carrier_subset (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) {F F' : ConicalLine BQ Q}
    {σ : PointedCone ℝ (realified ↥F.space)} {σ' : PointedCone ℝ (realified ↥F'.space)}
    (hne : σ ≠ ⊥)
    (hsub : (ConicalMember.fibre F σ).carrier hBsym ⊆
      (ConicalMember.fibre F' σ').carrier hBsym) :
    vSigma F σ ≤ vSigma F' σ' := by
  classical
  have hline : lineSpan F ⊓ realify F.space = ⊥ := lineSpan_inf_realify_space hBQ hBsym F
  have hene : rationalPoint F.gen ≠ 0 := rationalPoint_ne_zero F.gen_ne
  -- a nonzero member has a nonzero vector
  obtain ⟨c₀, hc₀, hc₀0⟩ : ∃ c : realified ↥F.space, c ∈ σ ∧ c ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, ne_eq, not_not] at h
    exact hne (le_bot_iff.1 fun x hx => by simp [h x hx])
  -- the two memberships of the span formula, from one carrier comparison
  have key : ∀ c ∈ σ, c ≠ 0 → ∃ c' ∈ σ',
      rationalPoint F.gen ∈ Submodule.span ℝ
        ({rationalPoint F'.gen, realifyMap F'.space c'} : Set (realified V)) ∧
      realifyMap F.space c ∈ Submodule.span ℝ
        ({rationalPoint F'.gen, realifyMap F'.space c'} : Set (realified V)) := by
    intro c hc hc0
    have hĉ0 : realifyMap F.space c ≠ 0 := fun h =>
      hc0 ((realifyMap_injective F.space) (by simpa using h))
    have hmem : wedgeTwo (rationalPoint F.gen) (realifyMap F.space c) ∈
        (ConicalMember.fibre F' σ').carrier hBsym :=
      hsub ⟨realifyMap F.space c, ⟨c, hc, rfl⟩, rfl⟩
    simp only [ConicalMember.carrier, Set.mem_image] at hmem
    obtain ⟨x, ⟨c', hc', rfl⟩, hx⟩ := hmem
    refine ⟨c', hc', ?_⟩
    have hz : wedgeTwo (rationalPoint F.gen) (realifyMap F.space c) ≠ 0 := by
      intro hzero
      -- `ĉ` would be a multiple of the line's generator, hence zero by transversality
      obtain ⟨g, hge, -⟩ := exists_dual_one_zero (v := (0 : realified V)) (by
        simpa using hene)
      have : realifyMap F.space c = g (realifyMap F.space c) • rationalPoint F.gen := by
        have hcalc := insertWedge_apply g (rationalPoint F.gen) (realifyMap F.space c)
        rw [hzero] at hcalc
        simp only [map_zero] at hcalc
        rw [hge, one_smul] at hcalc
        exact sub_eq_zero.1 hcalc.symm
      have hmemline : realifyMap F.space c ∈ lineSpan F ⊓ realify F.space :=
        ⟨by rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)),
          ⟨c, rfl⟩⟩
      rw [hline] at hmemline
      exact hĉ0 (by simpa using hmemline)
    exact wedgeTwo_span_le hx.symm hz
  -- the two summands of `vSigma F σ`
  have hspanle : ∀ c' ∈ σ',
      Submodule.span ℝ ({rationalPoint F'.gen, realifyMap F'.space c'} : Set (realified V))
        ≤ vSigma F' σ' := by
    intro c' hc'
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.mem_sup_right ⟨c', Submodule.subset_span hc', rfl⟩
  have hE : rationalPoint F.gen ∈ vSigma F' σ' := by
    obtain ⟨c', hc', h1, -⟩ := key c₀ hc₀ hc₀0
    exact hspanle c' hc' h1
  have hmap : Submodule.map (realifyMap F.space) (Submodule.span ℝ (σ : Set (realified ↥F.space)))
      ≤ vSigma F' σ' := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    by_cases hc0 : c = 0
    · subst hc0
      simp
    · obtain ⟨c', hc', -, h2⟩ := key c hc hc0
      exact hspanle c' hc' h2
  refine sup_le ?_ hmap
  rw [lineSpan]
  exact Submodule.span_le.2 (by rintro x rfl; exact hE)

end LineCase

/-! ## Genuine refinement of two admissible decompositions, and the line case -/

section AmbientRefinement

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The covering clause of refinement**: each member of the coarse collection is the union of the
members of the fine collection that it contains — "every member of `Σ'` is the union of the members
of `Σ` it contains".

**This clause is a definitional choice, not a theorem, and the docstring says why.** It is not in
the source. Looijenga's §4 gloss of "refined by" is containment of members and nothing more
(`.tmp-sources/looijenga-math0201218v2.md:603`: *"So every `σ ∈ Σ` is contained in a member of
`Σ'`"*); Definition 4.2 (`:481`) asks of a decomposition only that the union of its members be `C₊`;
and Lemma 6.6 (text line 821) is stated without proof. lean-categories#174 decides the frontier
question: the covering clause is **not derivable** from Definition 4.2 and Definition 6.1 as the
source states them — four routes from admissibility to it are closed, each by a proof in this
repository — but **every decomposition the source constructs has it**, because `Σ(bb)` (Example 6.2,
p. 29) and `Σ(ℋ)` (Example 6.4, p. 29) are stratifications of `C₊` by locally finite families, and a
chamber of a coarser arrangement is the union of the chambers of a finer one inside it. Refinement
for *these* objects therefore includes covering, and that is the relation this programme uses. It is
a definitional choice justified by the constructions, not an assumption inside a theorem: the
instance the programme uses is proved (`arrangementDecomposition_eq_sUnion_of_mem` for arrangements,
`semifanArrangement_refinesConicalLocus` at the conical locus), and the statement for an arbitrary
pair of admissible decompositions is recorded as a gap in the module docstring, not assumed here.

The union is taken in `⋀²V(ℝ)` through `ConicalMember.carrier`, because the two collections live on
*different* conical fibres: a fine member is a cone of `realified ↥F.space` and a coarse one of
`realified ↥F'.space`, so their intersection is not a set-theoretic union of cones. The carrier is
this file's established common currency for comparing members across fibres (it is what
`RefinesConicalLocus.containment` compares), and on one fibre it is faithful: `c ↦ wedgeLeft e c` is
injective there, the cone being transverse to the line (`lineSpan_inf_realify_space`). -/
def CoversConicalLocus (hBsym : BQ.IsSymm)
    (locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) : Prop :=
  ∀ (F' : ConicalLine BQ Q) (τ' : PointedCone ℝ (realified ↥F'.space)), τ' ∈ locus' F' →
    (ConicalMember.fibre F' τ').carrier hBsym ⊆
      ⋃₀ { T : Set (⋀[ℝ]^2 (realified V)) |
        ∃ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)), σ ∈ locus F ∧
          (ConicalMember.fibre F σ).carrier hBsym ⊆
            (ConicalMember.fibre F' τ').carrier hBsym ∧
          T = (ConicalMember.fibre F σ).carrier hBsym }

omit [Module.Finite ℚ V] in
theorem coversConicalLocus_iff {hBsym : BQ.IsSymm}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))} :
    CoversConicalLocus (Q := Q) hBsym locus locus' ↔
      ∀ (F' : ConicalLine BQ Q) (τ' : PointedCone ℝ (realified ↥F'.space)), τ' ∈ locus' F' →
        (ConicalMember.fibre F' τ').carrier hBsym ⊆
          ⋃₀ { T : Set (⋀[ℝ]^2 (realified V)) |
            ∃ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)), σ ∈ locus F ∧
              (ConicalMember.fibre F σ).carrier hBsym ⊆
                (ConicalMember.fibre F' τ').carrier hBsym ∧
              T = (ConicalMember.fibre F σ).carrier hBsym } :=
  Iff.rfl

/-- **Refinement of two admissible decompositions of the conical locus, in the form this programme
uses**: the source's containment of members (`containment`, Looijenga §4, text line 603) *and* the
covering clause (`covering`, `CoversConicalLocus`). The two are stated together because
lean-categories#174 decides that the covering clause is part of what refinement means for the
decompositions Looijenga constructs — see `CoversConicalLocus` for the decision, the source lines it
rests on, and what is not derivable. -/
structure RefinesConicalLocus (hBsym : BQ.IsSymm)
    (locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) : Prop where
  /-- The source's gloss: every fine member lies in a coarse member. -/
  containment : ∀ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)),
    σ ∈ locus F → σ ≠ ⊥ →
      ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)), σ' ∈ locus' F' ∧
        (ConicalMember.fibre F σ).carrier hBsym ⊆ (ConicalMember.fibre F' σ').carrier hBsym
  /-- The covering clause: every coarse member is the union of the fine members it contains. -/
  covering : CoversConicalLocus hBsym locus locus'

omit [Module.Finite ℚ V] in
theorem refinesConicalLocus_iff {hBsym : BQ.IsSymm}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))} :
    RefinesConicalLocus (Q := Q) hBsym locus locus' ↔
      ((∀ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)), σ ∈ locus F → σ ≠ ⊥ →
          ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)), σ' ∈ locus' F' ∧
            (ConicalMember.fibre F σ).carrier hBsym ⊆
              (ConicalMember.fibre F' σ').carrier hBsym) ∧
        CoversConicalLocus hBsym locus locus') :=
  ⟨fun h => ⟨h.containment, h.covering⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Looijenga, Lemma 6.6, p. 30, case (i) — the line case — on actual admissible decompositions.**
Let `Σ` and `Σ'` be admissible decompositions of the conical locus (Definition 6.1, p. 28) with `Σ'`
refined by `Σ` in the source's sense (`RefinesConicalLocus`). Then every member `σ` of `Σ` that
Definition 6.1 (i) covers — a nonzero member of a conical fibre that is not an isotropic half line —
has `V_σ ⊆ V_{σ'}`, where `σ'` is a member of `Σ'` whose carrier contains `σ`'s.

The `Γ`-invariance and condition (ii) of both decompositions are carried because they are the
source's hypotheses; the case-(i) inclusion consumes neither. What it consumes is the carrier
comparison of the refinement and the exterior-power faithfulness of the carrier
(`vSigma_le_of_carrier_subset`), which is why the containing member may lie in another stratum. The
case-(ii) member — an isotropic half line — is not covered here: the least member of `Σ'` containing
it is the half line itself once Definition 6.1 (ii)'s membership clause is available, and the
comparison there is `J_Σ ≤ J_{Σ'}`, which is the comparison of
`sigmaSupportSpace_le_of_hasSubordinateRefinement`. -/
theorem vSigma_le_of_refinesConicalLocus (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) {Γ : Set (V ≃ₗ[ℚ] V)}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (_D : IsAdmissibleDecomposition BQ Q Γ locus)
    (_D' : IsAdmissibleDecomposition BQ Q Γ locus')
    (href : RefinesConicalLocus (Q := Q) hBsym locus locus')
    (F : ConicalLine BQ Q) {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F)
    (hcase : IsCaseIFibre F σ) :
    ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)),
      σ' ∈ locus' F' ∧ vSigma F σ ≤ vSigma F' σ' := by
  obtain ⟨F', σ', hσ', hsub⟩ := href.containment F σ hσ hcase.1
  exact ⟨F', σ', hσ', vSigma_le_of_carrier_subset hBQ hBsym hcase.1 hsub⟩

/-! ## The plane case against the source's principal coarse family

Lemma 6.6's coarse family `Σ'` is usually the Baily–Borel decomposition — the source says so
("This applies in particular to the case when `Σ'` is the Baily-Borel decomposition", text line
823). Against that particular `Σ'` the plane case needs no subordinate refinement at all: the two
support spaces of a half line are `J_Σ` (Lemma-Definition 4.5 relative to the finer family) and
`J_{Σ(bb)} = J^⊥` (Example 6.2), and `J_Σ ⊆ J^⊥` is a *definitional* consequence of the two
source'd formulas, for every finer family of the arrangement shape.

The comparison is not vacuous: `J_{Σ(ℋ)} = J^⊥ ⊓ ⋂ {H ∈ ℋ : J ⊆ H}` (Example 6.4), so a wall
through `J` cuts it strictly below `J^⊥`, and in signature `(2,3)` the window `J^⊥/J` is
one-dimensional (`tests/regression/ConicalPlaneRefinement23.lean`).
-/

section PrincipalCoarse

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **Looijenga, Lemma 6.6, p. 30, the plane case, against `Σ' = Σ(bb)`**: for the arrangement
decomposition `Σ(ℋ)` (Example 6.4, p. 29) and the Baily–Borel decomposition (Example 6.2, p. 29),
the support space of the half line `C_{J,+}` relative to the finer family is contained in that
relative to the coarser one:

`J_{Σ(ℋ)} = J^⊥ ⊓ ⋂ {H ∈ ℋ : J ⊆ H} ⊆ J^⊥ = J_{Σ(bb)}`.

No subordinate refinement and no refinement hypothesis enter: the inclusion is `JH ≤ planePerpQ`
of the two definitions. So the plane case of Lemma 6.6 is available for the source's principal
`Σ'`, and the open question is only the general coarse family (`HasSubordinateRefinement`). -/
theorem vSigmaPlane_semifanArrangement_le_facial {ι : Type*} (ψ : ι → V →ₗ[ℚ] ℚ)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i)))
    (hS : IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F)) :
    vSigmaPlane hBsym F (semifanArrangement ψ F) G h ≤
      vSigmaPlane hBsym F (facialDecomposition F.closure) G h := by
  rw [vSigmaPlane_semifanArrangement_eq_JH ψ hBQ hBsym F G h hpos hnd hcut hS,
    vSigmaPlane_eq_ker_inf_ker hBQ hBsym F G h hpos hnd]
  refine le_inf ?_ ?_
  · exact (inf_le_left : JH (Q := Q) ψ G ≤ planePerpQ (Q := Q) G).trans
      (iInf_le (fun a : ↥G.plane => LinearMap.ker (associated Q (rationalPoint (a : V))))
        ⟨F.gen, F.gen_mem_plane G h⟩)
  · exact (inf_le_left : JH (Q := Q) ψ G ≤ planePerpQ (Q := Q) G).trans
      (iInf_le (fun a : ↥G.plane => LinearMap.ker (associated Q (rationalPoint (a : V))))
        ⟨F.planeRay G h, F.planeRay_mem G h⟩)

end PrincipalCoarse

/-! ## The arrangement instance of the covering clause

Looijenga's Example 6.4, p. 29: `Σ(ℋ)` is cut out of `C₊` by the traces of the hyperplanes of `ℋ`
(`semifanArrangement` at each fibre, `arrangementDecomposition` in general). Two such families with
`ℋ' ⊆ ℋ` — the coarser one cut by a subfamily of the forms — are the pair `#169` needs, and on them
the covering clause is not an extra hypothesis but a sign-pattern computation: a cell of the coarse
arrangement is the set of points whose signs on `ℋ'` are given, so it is the union of the cells of
the fine arrangement refining it, and the members of the decomposition are faces of cells, so a
coarse *member* is the union of the fine members inside it.

The one point that is not the naive sign-pattern union is the face-closure. A coarse member `τ'` is
a face of some coarse cell `C'` (`faceClosure`, Definition 4.2's completion at text line 483), and
the fine members inside `τ'` through a point `x ∈ τ'` are *not* the fine cell at `x`: that cell lies
in `C'` but need not lie in `τ'`. What works is the intersection `F_x ⊓ τ'`, which is a face of
`F_x` (`isFaceOf_inf_restrict` — a face of a cone restricts to a face of any subcone inside it),
hence a fine member, and contains `x` and lies in `τ'`. That is the sense in which "every stratum of
`ℋ` lies in the closure of one stratum of `ℋ'`", and it is why the argument needs no facet theory of
polyhedral cones. -/

section ArrangementCovering

open LeanCategories.Analysis.Convex

omit [Module.Finite ℚ V] in
/-- **A face of a cone restricts to a face of any subcone inside it.** If `F` is a face of `C` and
`P ≤ C`, then `P ⊓ F` is a face of `P`: a positive combination of two points of `P` that lands in
`P ⊓ F` lands in `F`, and the face property of `F` in `C` applies because `P ≤ C`. -/
theorem isFaceOf_inf_restrict {F C P : PointedCone ℝ (realified V)} (h : F.IsFaceOf C)
    (hle : P ≤ C) : (P ⊓ F).IsFaceOf P where
  le := inf_le_left
  mem_of_smul_add_mem := by
    intro x y a hx hy ha hxy
    exact ⟨hx, h.mem_of_smul_add_mem (hle hx) (hle hy) ha hxy.2⟩

omit [Module.Finite ℚ V] in
/-- **The cell of the finer arrangement at a point lies in the coarse cell of any pattern the point
specializes**: if `x` lies in the coarse cell of the pattern `s'` and `y` lies in the fine cell of
`x`'s own sign pattern, then `y` lies in the coarse cell of `s'`. Both are read through
`mem_arrangementCone_iff_specializes`: the fine signs at `y` are `0` or the fine signs at `x`, which
are `0` or `s'` on the coarse indices. -/
theorem arrangementCone_le_of_mem_signPattern {ι ι' : Type*} {φ : ι → (realified V) →L[ℝ] ℝ}
    {φ' : ι' → (realified V) →L[ℝ] ℝ} {ν : ι' → ι} (hν : ∀ i, φ' i = φ (ν i))
    {s' : ι' → SignType} {x y : realified V}
    (hx : x ∈ arrangementCone φ' s') (hy : y ∈ arrangementCone φ (signPattern φ x)) :
    y ∈ arrangementCone φ' s' := by
  rw [mem_arrangementCone_iff_specializes] at hx hy ⊢
  intro i
  rw [hν i]
  have hxi : SignType.sign (φ (ν i) x) = 0 ∨ SignType.sign (φ (ν i) x) = s' i := by
    have h := hx i
    rw [hν i] at h
    exact h
  have hyi : SignType.sign (φ (ν i) y) = 0 ∨
      SignType.sign (φ (ν i) y) = SignType.sign (φ (ν i) x) := hy (ν i)
  rcases hxi with h0 | hs
  · rcases hyi with h | h
    · exact Or.inl h
    · exact Or.inl (h.trans h0)
  · rcases hyi with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hs)

omit [Module.Finite ℚ V] in
/-- The fine cell at a point of a coarse cell lies in the coarse cell. -/
theorem arrangementCone_signPattern_inf_le {ι ι' : Type*} {φ : ι → (realified V) →L[ℝ] ℝ}
    {φ' : ι' → (realified V) →L[ℝ] ℝ} {ν : ι' → ι} (hν : ∀ i, φ' i = φ (ν i))
    {Cplus : PointedCone ℝ (realified V)} {s' : ι' → SignType} {x : realified V}
    (hx : x ∈ arrangementCone φ' s' ⊓ Cplus) :
    arrangementCone φ (signPattern φ x) ⊓ Cplus ≤ arrangementCone φ' s' ⊓ Cplus := by
  intro y hy
  exact ⟨arrangementCone_le_of_mem_signPattern hν hx.1 hy.1, hy.2⟩

omit [Module.Finite ℚ V] in
/-- **The covering clause for two arrangement decompositions, pointwise**: every point of a member
of the coarse arrangement decomposition `Σ(ℋ')` lies in a member of the fine one `Σ(ℋ)` that it
contains.

The fine member is `F_x ⊓ τ'`, the fine cell at `x` intersected with `τ'`: it lies in `τ'` and
contains `x`, and it is a member because `F_x` is a cell and `τ'` is a face of a coarse cell `C'`
that contains `F_x`. -/
theorem exists_mem_arrangementDecomposition_le_of_mem {ι ι' : Type*}
    {φ : ι → (realified V) →L[ℝ] ℝ} {φ' : ι' → (realified V) →L[ℝ] ℝ} {ν : ι' → ι}
    (hν : ∀ i, φ' i = φ (ν i))
    {Cplus : PointedCone ℝ (realified V)} {τ' : PointedCone ℝ (realified V)}
    (hτ' : τ' ∈ arrangementDecomposition φ' Cplus) {x : realified V} (hx : x ∈ τ') :
    ∃ σ ∈ arrangementDecomposition φ Cplus, x ∈ σ ∧ σ ≤ τ' := by
  obtain ⟨C', ⟨s', rfl⟩, hface⟩ := mem_faceClosure.1 hτ'
  have hxC' : x ∈ arrangementCone φ' s' ⊓ Cplus := hface.le hx
  exact ⟨arrangementCone φ (signPattern φ x) ⊓ Cplus ⊓ τ',
    mem_faceClosure.2 ⟨arrangementCone φ (signPattern φ x) ⊓ Cplus, ⟨signPattern φ x, rfl⟩,
      isFaceOf_inf_restrict hface (arrangementCone_signPattern_inf_le hν hxC')⟩,
    ⟨⟨mem_arrangementCone_signPattern φ x, hxC'.2⟩, hx⟩, inf_le_right⟩

omit [Module.Finite ℚ V] in
/-- **The covering clause for two arrangement decompositions, as a union**: each coarse member
is the union of the fine members it contains. -/
theorem arrangementDecomposition_eq_sUnion {ι ι' : Type*} {φ : ι → (realified V) →L[ℝ] ℝ}
    {φ' : ι' → (realified V) →L[ℝ] ℝ} {ν : ι' → ι} (hν : ∀ i, φ' i = φ (ν i))
    {Cplus : PointedCone ℝ (realified V)} {τ' : PointedCone ℝ (realified V)}
    (hτ' : τ' ∈ arrangementDecomposition φ' Cplus) :
    (τ' : Set (realified V)) =
      ⋃₀ { T : Set (realified V) |
        ∃ σ ∈ arrangementDecomposition φ Cplus, σ ≤ τ' ∧ T = (σ : Set (realified V)) } := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    obtain ⟨σ, hσ, hxσ, hle⟩ := exists_mem_arrangementDecomposition_le_of_mem hν hτ' hx
    exact Set.mem_sUnion.2 ⟨(σ : Set (realified V)), ⟨σ, hσ, hle, rfl⟩, hxσ⟩
  · refine Set.sUnion_subset ?_
    rintro T ⟨σ, -, hle, rfl⟩
    exact SetLike.coe_subset_coe.2 hle

omit [Module.Finite ℚ V] in
/-- **The containment half for two arrangement decompositions**: every fine member lies in a coarse
member, namely the coarse cell of its sign pattern restricted to the subfamily. -/
theorem exists_mem_arrangementDecomposition_of_mem {ι ι' : Type*}
    {φ : ι → (realified V) →L[ℝ] ℝ} {φ' : ι' → (realified V) →L[ℝ] ℝ} {ν : ι' → ι}
    (hν : ∀ i, φ' i = φ (ν i)) {Cplus : PointedCone ℝ (realified V)}
    {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ arrangementDecomposition φ Cplus) :
    ∃ τ' ∈ arrangementDecomposition φ' Cplus, σ ≤ τ' := by
  obtain ⟨C, ⟨s, rfl⟩, hface⟩ := mem_faceClosure.1 hσ
  refine ⟨arrangementCone φ' (fun i => s (ν i)) ⊓ Cplus,
    mem_faceClosure.2 ⟨_, ⟨fun i => s (ν i), rfl⟩, PointedCone.IsFaceOf.refl _⟩,
    hface.le.trans ?_⟩
  intro y hy
  obtain ⟨hycell, hyP⟩ := Submodule.mem_inf.1 hy
  refine Submodule.mem_inf.2 ⟨?_, hyP⟩
  rw [mem_arrangementCone_iff_specializes] at hycell ⊢
  intro i
  have hyi : SignType.sign (φ (ν i) y) = 0 ∨ SignType.sign (φ (ν i) y) = s (ν i) := hycell (ν i)
  rw [hν i]
  exact hyi

end ArrangementCovering

/-! ## The arrangement instance at the conical locus

`Σ(ℋ)` at every fibre is `semifanArrangement ψ`, and the coarser family cut by a subfamily
`ℋ' = ψ'` of the same hyperplanes is `semifanArrangement ψ'`; the walls containing a given line are
carried along by `fibreWallsMap`. Both families live on the *same* fibre, so the carrier comparison
of `ConicalMember.carrier` that `RefinesConicalLocus` asks for is a restatement of the cone
inclusion in that fibre (`carrier_fibre_mono`). -/

section SemifanInstance

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- **The inclusion of wall families**: the hyperplanes of `ℋ'` are among those of `ℋ`, so the
traces of the coarse family on a fibre are indexed by a subset of the traces of the fine one. -/
def fibreWallsMap {ι ι' : Type*} {ψ : ι → V →ₗ[ℚ] ℚ} {ψ' : ι' → V →ₗ[ℚ] ℚ} {ν : ι' → ι}
    (hν : ∀ i, ψ' i = ψ (ν i)) (F : ConicalLine BQ Q) :
    fibreWalls ψ' F → fibreWalls ψ F :=
  fun i => ⟨ν i.1, by rw [← hν i.1]; exact i.2⟩

omit [Module.Finite ℚ V] in
/-- The trace forms agree along the inclusion of wall families. -/
theorem fibreWallsMap_form {ι ι' : Type*} {ψ : ι → V →ₗ[ℚ] ℚ} {ψ' : ι' → V →ₗ[ℚ] ℚ}
    {ν : ι' → ι} (hν : ∀ i, ψ' i = ψ (ν i)) (F : ConicalLine BQ Q) (i : fibreWalls ψ' F) :
    fibreFormC F (ψ' i.1) = fibreFormC F (ψ (fibreWallsMap (Q := Q) hν F i).1) := by
  rw [fibreWallsMap, hν i.1]

omit [Module.Finite ℚ V] in
/-- **A smaller member of a fibre has a smaller carrier**. -/
theorem carrier_fibre_mono {hBsym : BQ.IsSymm} {F : ConicalLine BQ Q}
    {σ τ : PointedCone ℝ (realified ↥F.space)} (h : σ ≤ τ) :
    (ConicalMember.fibre F σ).carrier hBsym ⊆ (ConicalMember.fibre F τ).carrier hBsym := by
  rintro v ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  exact ⟨_, ⟨c, h hc, rfl⟩, rfl⟩

omit [Module.Finite ℚ V] in
/-- **The arrangement instance of the covering clause** (lean-categories#169, decided by #174):
for two families of hyperplanes with `ℋ' ⊆ ℋ`, the arrangement decomposition `Σ(ℋ)` refines
`Σ(ℋ')` in the programme's sense — containment of members *and* the covering clause. -/
theorem semifanArrangement_refinesConicalLocus {ι ι' : Type*} {ψ : ι → V →ₗ[ℚ] ℚ}
    {ψ' : ι' → V →ₗ[ℚ] ℚ} {ν : ι' → ι}
    (hBsym : BQ.IsSymm) (hν : ∀ i, ψ' i = ψ (ν i)) :
    RefinesConicalLocus (Q := Q) hBsym (semifanArrangement ψ) (semifanArrangement ψ') where
  containment := by
    intro F σ hσ _
    have hσ' : σ ∈ arrangementDecomposition
        (fun i : fibreWalls ψ F => fibreFormC F (ψ i)) F.closure := by
      simpa only [semifanArrangement] using hσ
    obtain ⟨τ', hτ', hle⟩ := exists_mem_arrangementDecomposition_of_mem
      (φ := fun i : fibreWalls ψ F => fibreFormC F (ψ i))
      (φ' := fun i : fibreWalls ψ' F => fibreFormC F (ψ' i))
      (ν := fibreWallsMap (Q := Q) hν F) (fibreWallsMap_form hν F) hσ'
    exact ⟨F, τ', by simpa only [semifanArrangement] using hτ', carrier_fibre_mono hle⟩
  covering := by
    intro F' τ' hτ' v hv
    have hτ'' : τ' ∈ arrangementDecomposition
        (fun i : fibreWalls ψ' F' => fibreFormC F' (ψ' i)) F'.closure := by
      simpa only [semifanArrangement] using hτ'
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨c, hc, rfl⟩ := hw
    obtain ⟨σ, hσ, hcσ, hle⟩ := exists_mem_arrangementDecomposition_le_of_mem
      (φ := fun i : fibreWalls ψ F' => fibreFormC F' (ψ i))
      (φ' := fun i : fibreWalls ψ' F' => fibreFormC F' (ψ' i))
      (ν := fibreWallsMap (Q := Q) hν F') (fibreWallsMap_form hν F') hτ'' hc
    exact Set.mem_sUnion.2 ⟨_, ⟨F', σ, by simpa only [semifanArrangement] using hσ,
      carrier_fibre_mono hle, rfl⟩, ⟨_, ⟨c, hcσ, rfl⟩, rfl⟩⟩

end SemifanInstance

/-! ## The subordinate refinement from the covering clause

This is the step lean-categories#169 asks for by name: `HasSubordinateRefinement` — the hypothesis
`Semifan.sigmaSupportSpace_le_of_refines` consumes, and with it the plane case of Lemma 6.6 —
derived from the covering clause rather than assumed.

The derivation is two lines of mathematics and no polyhedral geometry. Covering at the coarse member
`τ'` inserts a fine member `σ_x` through any point `x` of `τ'` that one names, inside `τ'`; if that
point is a *relative interior* point of a fine member `σ`, the insertion lemma of this file
(`IsLocallyRationalDecomposition.le_of_isRelintPoint`) upgrades the point membership to
`σ ≤ σ_x`. So `σ_x` is a fine member between `σ` and `τ'`, which is exactly
`HasSubordinateRefinement`.

What is *not* used: closedness of the members. The docstring of the earlier section names closure of
rational cones (`IsRationalCone.isClosed`) as an input of the route through the trace argument; that
route is what the covering clause replaces, and this derivation does not need it. -/

section SubordinateFromCovering

variable {C : Set (realified V)} {Cpb : PointedCone ℝ (realified V)}
  {S S' : Set (PointedCone ℝ (realified V))}

omit [Module.Finite ℚ V] in
/-- **A relative interior point of a half line is its generator.** The proper faces of `hull {v}`
are `{0}`, so a nonzero `v` lies in none of them. -/
theorem isRelintPoint_hull_singleton {v : realified V} (hv : v ≠ 0) :
    IsRelintPoint (PointedCone.hull ℝ ({v} : Set (realified V))) v := by
  refine ⟨PointedCone.subset_hull (Set.mem_singleton v), ?_⟩
  intro F hF hvF
  refine le_antisymm hF.le ?_
  rw [PointedCone.hull]
  exact Submodule.span_le.2 (by rintro _ rfl; exact hvF)

omit [Module.Finite ℚ V] in
/-- **The subordinate refinement, from the covering clause and the insertion lemma.** Let `S` be a
locally rational decomposition, `S'` a family each of whose members is covered by the members of `S`
inside it (`hcov` — the pointwise form of the covering clause, which
`exists_mem_arrangementDecomposition_le_of_mem` supplies for arrangement families), and `σ ∈ S` a
member with a relative interior point `x` in the open cone. Then every member of `S'` above `σ`
contains a member of `S` above `σ` meeting the open cone: `HasSubordinateRefinement`.

The witness is the fine member through `x` that covering supplies, and the containment `σ ≤ σ_x` is
the insertion lemma, which is available because that witness is a member of the *same* family as
`σ`. This is the cross-family insertion the earlier section of this module records as unavailable
from the insertion lemma alone: covering is what supplies the same-family member to apply it to. -/
theorem exists_subordinate_of_isRelintPoint
    (hS : IsLocallyRationalDecomposition (rationalClosure Cpb) S)
    (hcov : ∀ (τ' : PointedCone ℝ (realified V)), τ' ∈ S' → ∀ x ∈ τ', ∃ σ ∈ S, x ∈ σ ∧ σ ≤ τ')
    {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ S) {x : realified V}
    (hx : IsRelintPoint σ x) (hxC : x ∈ C) :
    HasSubordinateRefinement C S S' σ := by
  rintro ⟨τ', hτ', hστ', -⟩
  obtain ⟨σx, hσx, hxσx, hle⟩ := hcov τ' hτ' x (hστ' hx.mem)
  exact ⟨σx, hσx, hS.le_of_isRelintPoint hσ hσx hx hxσx, hle, ⟨x, hxσx, hxC⟩⟩

end SubordinateFromCovering

/-! ## Lemma 6.6, case (ii): the plane case, from the covering clause

With the subordinate refinement available at the half line `C_{J,+}` of a plane — its relative
interior point is its generator (`isRelintPoint_hull_singleton`), and it is a member of the fine
family by Definition 6.1 (ii)'s parenthetical clause — the comparison `J_Σ ≤ J_{Σ'}` of Lemma 6.6 is
`vSigmaPlane_le_of_refines`, and the support-index comparison behind it is
`sigmaSupportSpace_le_of_hasSubordinateRefinement`. What the covering clause adds over the earlier
statement of the plane case is that `S'` is an *arbitrary* coarse family, not only the Baily–Borel
one (`vSigmaPlane_semifanArrangement_le_facial`). -/

section PlaneCase

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- **Looijenga, Lemma 6.6, p. 30, case (ii) — the plane case — from the covering clause**: for two
decompositions `S`, `S'` of the fibre of `I` with `S'` covered by `S`, the `Σ`-support space of the
half line `C_{J,+}` relative to `S` is contained in the one relative to `S'`.

The hypotheses are: the covering clause pointwise (`hcov`), the fine decomposition's local
rationality (`hS`, needed by the insertion lemma), Definition 6.1 (ii)'s membership clause for the
half line at the fine family (`hidx`, the source's "(so that the cone `C_{J,+} = C̄_J` in `⋀²J` is
member of `Σ`)", which `IsAdmissibleDecomposition` does not carry), and that the half line's
generator lies in the open cone (`hxC`). -/
theorem vSigmaPlane_le_of_covers (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (hFG : F.line ≤ G.plane)
    {S S' : Set (PointedCone ℝ (realified ↥F.space))} {Cpb : PointedCone ℝ (realified ↥F.space)}
    (hS : IsLocallyRationalDecomposition (rationalClosure Cpb) S)
    (hcov : ∀ (τ' : PointedCone ℝ (realified ↥F.space)), τ' ∈ S' → ∀ x ∈ τ',
      ∃ σ ∈ S, x ∈ σ ∧ σ ≤ τ')
    (hmem : PointedCone.hull ℝ
      ({rationalPoint (fibreRay hBsym F G hFG)} : Set (realified ↥F.space)) ∈ S)
    (hxne : rationalPoint (fibreRay hBsym F G hFG) ≠ 0)
    (hxC : (rationalPoint (fibreRay hBsym F G hFG) : realified ↥F.space) ∈
      positiveCone.upper (fibreForm Q F.space) F.sheet) :
    vSigmaPlane hBsym F S G hFG ≤ vSigmaPlane hBsym F S' G hFG := by
  have hidx : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet) S
      (PointedCone.hull ℝ {rationalPoint (fibreRay hBsym F G hFG)}) :=
    ⟨_, hmem, le_rfl,
      ⟨_, PointedCone.subset_hull (Set.mem_singleton _), hxC⟩⟩
  exact vSigmaPlane_le_of_refines hBsym F G hFG hidx
    (exists_subordinate_of_isRelintPoint
      (C := positiveCone.upper (fibreForm Q F.space) F.sheet) (Cpb := Cpb)
      (σ := PointedCone.hull ℝ {rationalPoint (fibreRay hBsym F G hFG)})
      hS hcov hmem (isRelintPoint_hull_singleton hxne) hxC)

end PlaneCase

/-! ## The exported statement, and what its four cases need

Lemma 6.6 says: for `σ ∈ Σ` and `σ'` the smallest member of `Σ'` containing `σ`, `V_σ ⊆ V_{σ'}`.
The four cases are the shapes a member of the conical locus takes in Definition 6.1, and the
development supplies three of them: the line case, which is `vSigma_le_of_refinesConicalLocus` and
carries the cross-stratum case with it (the containment of carriers there is a comparison in
`⋀²V(ℝ)`, so the containing member may sit in another fibre); the plane case, which is
`vSigmaPlane_le_of_covers`; and the apex, for which the support is `{0}`
(`ConicalMember.fibreVSigma_bot`). The isotropic half line is the one member shape whose value is
*not* Definition 6.1 (i)'s span formula — the source routes it through case (ii) — so the case-(ii)
comparison is fed into the export as the hypothesis `hhalf`, in the same shape as the other cases;
`vSigmaPlane_le_of_covers` is what discharges it in the arrangement setting, and what is still
missing to discharge it unconditionally is the identification of the fibre's span formula at an
isotropic half line with the plane support space `J_Σ` (the two are different submodules as the
development stands, and `ConicalMember.fibreVSigma`'s docstring records why the source separates
them). -/

section Export

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- **Looijenga, Lemma 6.6, p. 30, case (ii) at the member level: the apex has support `{0}`**, so
its inclusion in any other support space is immediate. -/
theorem ConicalMember.fibreVSigma_bot_le {F F' : ConicalLine BQ Q}
    {σ' : PointedCone ℝ (realified ↥F'.space)} :
    ConicalMember.fibreVSigma F (⊥ : PointedCone ℝ (realified ↥F.space)) ≤
      ConicalMember.fibreVSigma F' σ' := by
  rw [ConicalMember.fibreVSigma_bot]
  exact bot_le

/-- **Looijenga, Lemma 6.6, p. 30, exported on two actual admissible decompositions**: for a member
`σ` of the fine decomposition at a fibre, there is a member `σ'` of the coarse decomposition with
`V_σ ⊆ V_{σ'}`, the three cases of Definition 6.1 (i) being discharged here and the isotropic half
line, which is Definition 6.1 (ii)'s, being supplied by `hhalf`.

`hhalf` is where case (ii) enters. It is not an assumption of the source — the source's Lemma 6.6
covers the half line through condition (ii) of Definition 6.1 — but the development has no
identification of the fibre's span formula at an isotropic half line with the plane support space,
so the case is stated in the same shape as the others and discharged by
`vSigmaPlane_le_of_covers` (the plane case, from the covering clause) in the setting where the half
line is a member of the fine family. -/
theorem vSigma_le_of_refines_of_cases (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) {Γ : Set (V ≃ₗ[ℚ] V)}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (D : IsAdmissibleDecomposition BQ Q Γ locus)
    (D' : IsAdmissibleDecomposition BQ Q Γ locus')
    (href : RefinesConicalLocus (Q := Q) hBsym locus locus')
    (F : ConicalLine BQ Q) {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F)
    (hbot : σ ≠ ⊥)
    (hhalf : IsIsotropicHalfLine (fibreForm Q F.space) σ →
      ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)), σ' ∈ locus' F' ∧
        vSigma F σ ≤ vSigma F' σ') :
    ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)), σ' ∈ locus' F' ∧
      vSigma F σ ≤ vSigma F' σ' := by
  by_cases hline : IsIsotropicHalfLine (fibreForm Q F.space) σ
  · exact hhalf hline
  · exact vSigma_le_of_refinesConicalLocus hBQ hBsym D D' href F hσ ⟨hbot, hline⟩

end Export

end AmbientRefinement

end LeanCategories.Lattices.Valued
