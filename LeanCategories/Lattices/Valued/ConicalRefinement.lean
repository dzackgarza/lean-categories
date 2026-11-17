/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FibreRefinement
public import LeanCategories.Lattices.Valued.ConicalMemberDescent
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
proof of the lemma straightforward, and the three steps it leaves implicit are:

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

## The refinement relation

`RefinesConicalLocus` below is the source's hypothesis "`Σ'` is refined by `Σ`" at the geometric
object: every member of the finer collection lies, as a cone of the conical locus inside `⋀²V(ℝ)`,
in a member of the coarser one. It is *not* `FibreRefinement.RefinesLocus`, which relates the two
families fibre by fibre and is therefore a strictly stronger hypothesis on each fibre and no
statement at all across strata; and it is not `Semifan.sigmaSupportSpace_le_of_refines`'s
support-index domination, which assumes a containment between supports.

## What is not in this module

The zero case and the plane case of Lemma 6.6 are the next unit; the plane case reduces, by
Definition 6.1 (ii), to `J_Σ ⊆ J_{Σ'}` for the same plane, which is the comparison in item 2 above,
and it additionally needs the clause of Definition 6.1 (ii) that `C_{J,+}` *is a member* of every
admissible decomposition — the source's parenthetical "(so that the cone `C_{J,+} = C̄_J` in `⋀²J` is
member of `Σ`)", which `IsAdmissibleDecomposition` does not carry today.
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

So the hypothesis is genuinely extra as a hypothesis. What is *not* settled by this family is whether
Lemma 6.6's plane-case *conclusion* `J_Σ ≤ J_{Σ'}` can also fail: in a `(2,2)` model every half
line's support space is the plane itself, so both sides agree there. A refutation needs a fibre of
signature `(1, n−1)` with `n ≥ 3`, where `J^⊥ ⊋ J`, and the value at the fibre where the coarse
member above the half line contains no fine one. That is the open question, and it is why the plane
case is not stated in this module.

**Why the insertion lemma cannot supply it either.** The insertion lemma compares two members of one
family: the rational-cone-system axiom it uses — two members meet along a common face — is an axiom
*within* a decomposition, and there is no counterpart relating a member of one decomposition to a
member of another. The only cross-family input is the refinement itself.
-/

section Subordinate

variable {C : Set (realified V)} {S S' : Set (PointedCone ℝ (realified V))}

/-- **The subordinate refinement of a support index**: every member of the coarse family above `σ`
that meets the open cone contains a member of the fine family above `σ` that meets it. This is
verbatim the hypothesis of `Semifan.sigmaSupportSpace_le_of_refines`, named here so that its status
is explicit. It is a statement about *members*; no support space, support index or containment of
support spaces occurs in it.

**It is kept as a hypothesis, and it is not derivable from Definition 6.1.** The section docstring
above gives the family that decides this: on the split model of signature `(2,2)` the members
`{C̄, τ} ∪ faces` at the fibre of `I = ⟨e₀⟩` pass both conditions of Definition 6.1 (with `Γ`
trivial) and fail this hypothesis against a coarse family whose member above the half line is a
proper sub-wedge. The plane case of Lemma 6.6 therefore rests on this hypothesis in the present
development, and `tests/regression/ConicalRefinementSplit22.lean` exercises the line case that does
not. -/
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

/-- **Genuine global refinement of two admissible decompositions of the conical locus**: every
member of the finer collection is contained, as a cone of the conical locus inside `⋀²V(ℝ)`
(`ConicalMember.carrier`), in a member of the coarser one. This is the source's "`Σ'` ... is
refined by `Σ`" (Looijenga, Lemma 6.6, p. 30): a relation between the two collections as
collections of cones in the conical locus, with no support space and no support index in it.

It is strictly stronger on each fibre than the fibre-wise `FibreRefinement.RefinesLocus` (which
it implies, up to the fibre presentation of the containing member) and strictly weaker than
`Semifan.sigmaSupportSpace_le_of_refines`'s support-index domination, which assumes the inclusion of
supports that Lemma 6.6 concludes. `σ ≠ ⊥` is carried because the apex is contained in every carrier
while its support space is `{0}`, so it is not a case-(i) member at all. -/
def RefinesConicalLocus (hBsym : BQ.IsSymm)
    (locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) : Prop :=
  ∀ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)), σ ∈ locus F → σ ≠ ⊥ →
    ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)), σ' ∈ locus' F' ∧
      (ConicalMember.fibre F σ).carrier hBsym ⊆ (ConicalMember.fibre F' σ').carrier hBsym

omit [Module.Finite ℚ V] in
theorem refinesConicalLocus_iff {hBsym : BQ.IsSymm}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))} :
    RefinesConicalLocus (Q := Q) hBsym locus locus' ↔
      ∀ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)), σ ∈ locus F → σ ≠ ⊥ →
        ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)), σ' ∈ locus' F' ∧
          (ConicalMember.fibre F σ).carrier hBsym ⊆
            (ConicalMember.fibre F' σ').carrier hBsym :=
  Iff.rfl

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
  obtain ⟨F', σ', hσ', hsub⟩ := href F σ hσ hcase.1
  exact ⟨F', σ', hσ', vSigma_le_of_carrier_subset hBQ hBsym hcase.1 hsub⟩

end AmbientRefinement

end LeanCategories.Lattices.Valued
