/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ConicalLocus

/-!
# Refining a locally rational decomposition: the least containing coarse member

E. Looijenga, *Compactifications defined by arrangements II: the locally symmetric varieties of
type IV*, arXiv math/0201218v2 (2002), `looijenga-math0201218v2.md`: Definition 4.2, p. 17
(text line 481) and Lemma 6.6, p. 30 (text line 821):

> Lemma 6.6. Let `Σ'` be a `Γ`-invariant admissible decomposition of the conical locus that is
> refined by `Σ`. Given `σ ∈ Σ`, let `σ'` be the smallest member of `Σ'` that contains `σ`. Then
> `V_σ ⊂ V_{σ'}`, so that we have a factorization of `D → π_{σ'}D` over `π_σ D`.

The source's proof is one line ("The proof of the following lemma is straightforward"), and this
module supplies the two steps that line leaves implicit, at the generality the source uses.

* **Refinement, as containment of members.** `Refines S S'` says every member of `S` is contained
  in a member of `S'`. That is the fan-theoretic meaning of "`Σ'` is refined by `Σ`", and it is the
  hypothesis under which a least containing member can exist: the covering clause of Definition 4.2
  (`IsLocallyRationalDecomposition.union_eq`) is pointwise and does not by itself put a *single*
  member of `S'` above a given member of `S`. Nothing about support indices enters.

* **Existence and leastness of the containing member, from the face axioms.** `IsLeastMem S' σ σ'`
  records that `σ'` is a member of `S'` containing `σ` and below every such member.
  `exists_least_mem_of_le` derives it from Definition 4.2 alone: two members of `S'` meet along a
  common face (`inf_isFaceOf_of_isLocallyRationalDecomposition`), that face is itself a member
  (`IsLocallyRationalDecomposition.mem_of_isFaceOf`), and among the members of `S'` above `σ` one of
  minimal linear-span rank lies below all of them, because a proper face drops that rank strictly
  (`finrank_span_lt_of_isFaceOf_of_ne`). No member is assumed; the leastness comes out of the face
  system and finite dimensionality (`Module.Finite ℚ V`).

**Why no finiteness, complete lattice or infinite-intersection hypothesis.** Definition 4.2 asks
for a rational cone system — so a *finite* family — only on each rational subcone
(`IsLocallyRationalDecomposition.restriction`); the decomposition `Σ'` itself is not finite, and the
source never intersects an infinite subfamily. Accordingly the argument below minimizes a natural
number, the rank, rather than a finite set of members, and it takes one pairwise intersection at a
time. The closest formalised analogue is TauCeti's `TauCeti.Toric.FanHom.exists_isLeast_cone`,
"the target cones containing the image of a given source cone have a least element": its proof is
this argument, with `Fan.finite_cones` supplying the element to minimize over and
`Fan.inf_mem` supplying the meet. Replacing that finiteness by the rank is what makes the statement
available for a locally rational decomposition, whose members are neither finite in number nor
polyhedral cones of a fan; it is also why no least member, no support inclusion and no complete
lattice of cones is assumed anywhere.

**The fibre and the support space.** In a conical fibre `F` of a `ℚ`-isotropic line (Definition 6.1
(i), p. 28) the two families `locus F` and `locus' F` are locally rational decompositions of the
same carrier `F.closure = C_{I,+}` (Definition 6.1 (i)), so the refinement relation and the
least-member statement hold fibre by fibre (`RefinesLocus`, `exists_least_mem_of_refines_fibre`),
and `vSigma_mono` turns `σ ≤ σ'` into `V_σ ⊆ V_{σ'}`. That is Lemma 6.6's inclusion for the members
whose support space Definition 6.1 (i) defines, namely the members that are not isotropic half lines
(`vSigma_le_of_refines_of_not_isotropicHalfLine`).

The source's principal instance is the refinement by the coarsest decomposition `Σ(bb)` ("This
applies in particular to the case when `Σ'` is the Baily-Borel decomposition", text line 823);
`exists_least_mem_facialDecomposition` is that instance, so the hypothesis is not vacuous.

## Main declarations

* `Refines`, `RefinesLocus`: refinement by containment of members, and its fibre-wise form.
* `IsLeastMem`: `σ'` is the least member of `S'` containing `σ`.
* `exists_least_mem_of_le`: existence of `σ'`, from Definition 4.2 and `Module.Finite ℚ V`.
* `IsLeastMem.eq`: it is unique, so that `σ ↦ σ'` is a function.
* `exists_least_mem_of_refines`: the same, from a genuine refinement.
* `exists_least_mem_facialDecomposition`: the source's `Σ' = Σ(bb)` instance.
* `exists_least_mem_of_refines_fibre`: the fibre-wise form, step one of Lemma 6.6.
* `vSigma_le_of_refines_of_not_isotropicHalfLine`: `V_σ ⊆ V_{σ'}`, step two of Lemma 6.6.
-/

@[expose] public section

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

universe u

/-! ## Genuine refinement of a family of cones

Looijenga, Definition 4.2, p. 17, calls a collection of convex cones a locally rational
decomposition of `C₊` when its union is `C₊` and its restriction to every rational subcone is a
rational cone system. "`Σ'` is refined by `Σ`" (Lemma 6.6, p. 30) has no separate definition in the
source: it is the standard relation on cone decompositions, which the decomposition axioms make
meaningful — every member of the finer collection lies in a member of the coarser one. The cover of
`C₊` is not enough by itself (a member of `Σ` can meet several members of `Σ'`), and the source's
next sentence uses exactly the single containing member, so containment of members is what is
carried below.
-/

section General

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- **`S` refines `S'`**: every member of `S` is contained in a member of `S'`. This is the sense in
which a decomposition `Σ'` "is refined by `Σ`" in Looijenga, Lemma 6.6, p. 30, and it is what the
source's "let `σ'` be the smallest member of `Σ'` that contains `σ`" presupposes: the covering
clause of Definition 4.2 gives, through each point of `σ`, a member of `S'`, not one member above
all of `σ`. The refinement step of Lemma 6.6 was previously available only through the support-index
domination hypothesis of `Semifan.sigmaSupportSpace_le_of_refines`, which assumes the containment
conclusion instead of a refinement of the two decompositions. -/
def Refines (S S' : Set (PointedCone ℝ (realified V))) : Prop :=
  ∀ σ ∈ S, ∃ σ' ∈ S', σ ≤ σ'

theorem refines_iff {S S' : Set (PointedCone ℝ (realified V))} :
    Refines S S' ↔ ∀ σ ∈ S, ∃ σ' ∈ S', σ ≤ σ' := Iff.rfl

/-- Every family refines itself. -/
theorem Refines.refl (S : Set (PointedCone ℝ (realified V))) : Refines S S :=
  fun σ hσ => ⟨σ, hσ, le_rfl⟩

/-- Refinement is transitive. -/
theorem Refines.trans {S S' S'' : Set (PointedCone ℝ (realified V))}
    (h : Refines S S') (h' : Refines S' S'') : Refines S S'' := by
  intro σ hσ
  obtain ⟨τ, hτ, hστ⟩ := h σ hσ
  obtain ⟨υ, hυ, hτυ⟩ := h' τ hτ
  exact ⟨υ, hυ, hστ.trans hτυ⟩

/-- A finer family contained in another one still refines the same coarser family. -/
theorem Refines.mono_left {S T S' : Set (PointedCone ℝ (realified V))}
    (h : Refines S S') (hTS : T ⊆ S) : Refines T S' :=
  fun σ hσ => h σ (hTS hσ)

/-- **Every locally rational decomposition refines the facial decomposition `Σ(bb)`** (Looijenga,
Definition 4.2, p. 17, text line 483: "The coarsest locally rational decomposition of `C` is the
collection of faces of `C₊`"). Each member of `S` lies in `C₊ = rationalClosure C`, which is a face
of itself, so the refinement is immediate; this is the refinement hypothesis of Lemma 6.6, p. 30, in
the source's own principal case ("This applies in particular to the case when `Σ'` is the
Baily-Borel decomposition", text line 823), and it shows that the hypothesis is not vacuous. -/
theorem refines_facialDecomposition {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S) :
    Refines S (facialDecomposition (rationalClosure C)) :=
  fun _ hσ => ⟨_, PointedCone.IsFaceOf.refl _, hS.le hσ⟩

/-! ## The least containing coarse member

The next declarations do not mention refinement: they use only that *some* member of `S'` contains
`σ`, together with the face axioms of Definition 4.2 and finite dimensionality. Splitting the
argument this way keeps the leastness claim independent of how the containing member was produced.
-/

/-- **`σ'` is the least member of `S'` containing `σ`**: it is a member of `S'`, it contains `σ`,
and it lies below every member of `S'` that contains `σ`. This is the "smallest member of `Σ'` that
contains `σ`" of Looijenga, Lemma 6.6, p. 30, with the leastness carried as data rather than
assumed, so that `exists_least_mem_of_le` can produce it and `IsLeastMem.eq` can turn it into a
function of `σ`. -/
structure IsLeastMem (S' : Set (PointedCone ℝ (realified V)))
    (σ σ' : PointedCone ℝ (realified V)) : Prop where
  /-- `σ'` is a member of the coarse family. -/
  mem : σ' ∈ S'
  /-- `σ'` contains `σ`. -/
  le : σ ≤ σ'
  /-- `σ'` lies below every member of the coarse family that contains `σ`. -/
  least : ∀ ⦃τ⦄, τ ∈ S' → σ ≤ τ → σ' ≤ τ

theorem isLeastMem_iff {S' : Set (PointedCone ℝ (realified V))}
    {σ σ' : PointedCone ℝ (realified V)} :
    IsLeastMem S' σ σ' ↔ σ' ∈ S' ∧ σ ≤ σ' ∧ ∀ ⦃τ⦄, τ ∈ S' → σ ≤ τ → σ' ≤ τ :=
  ⟨fun h => ⟨h.mem, h.le, fun _ hτ hστ => h.least hτ hστ⟩,
    fun h => ⟨h.1, h.2.1, fun _ hτ hστ => h.2.2 hτ hστ⟩⟩

/-- The least containing member, if it exists, is unique: two members of `S'` containing `σ`, each
below the other, are equal. This is what makes `σ ↦ σ'` a function of `σ`, as Lemma 6.6 uses it. -/
theorem IsLeastMem.eq {S' : Set (PointedCone ℝ (realified V))}
    {σ σ₁ σ₂ : PointedCone ℝ (realified V)}
    (h₁ : IsLeastMem S' σ σ₁) (h₂ : IsLeastMem S' σ σ₂) : σ₁ = σ₂ :=
  le_antisymm (h₁.least h₂.mem h₂.le) (h₂.least h₁.mem h₁.le)

/-- The least member of a family containing one of its own members is that member. -/
theorem isLeastMem_self {S' : Set (PointedCone ℝ (realified V))}
    {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ S') : IsLeastMem S' σ σ :=
  ⟨hσ, le_rfl, fun _ _ hστ => hστ⟩

/-- **Existence of the least member of `S'` containing `σ`**, for `S'` a locally rational
decomposition of `C₊ = rationalClosure C` (Looijenga, Definition 4.2, p. 17) and `σ` a cone
contained in some member of `S'`.

This is the argument the source leaves implicit in Lemma 6.6, p. 30. Among the members of `S'` above
`σ` pick one, `τ₀`, of least linear-span rank. The rank is a natural number, so it exists in finite
dimensionality (`Module.Finite ℚ V`); the family `S'` itself is *not* assumed finite. For any other
such member `τ`, the intersection
`τ₀ ⊓ τ` is a face of `τ₀`, because two members of a locally rational decomposition meet along a
common face (`inf_isFaceOf_of_isLocallyRationalDecomposition`); it is a member of `S'`
(`mem_of_isFaceOf`); and it still contains `σ`. So its rank is that of `τ₀`, while a proper face has
strictly smaller rank (`finrank_span_lt_of_isFaceOf_of_ne`). Hence `τ₀ ⊓ τ = τ₀`, that is
`τ₀ ≤ τ`: the single minimal-rank member lies below every member containing `σ`.

Nothing here intersects an infinite family and nothing assumes a least member; leastness comes from
the pairwise meet axiom. LC-09: `content:fan refinement every cone contained in a cone of the
coarser fan`, `content:smallest cone containing a given cone fan`, `content:minimal face containing
a cone` and `content:least element face lattice of a cone` found no Lean statement for a family that
is not finite; the nearest is `TauCeti.Toric.FanHom.exists_isLeast_cone`, whose proof this one
follows with `Fan.finite_cones` replaced by the rank `finrank_span_lt_of_isFaceOf_of_ne` of this
repository. -/
theorem exists_least_mem_of_le [Module.Finite ℚ V] {C : PointedCone ℝ (realified V)}
    {S' : Set (PointedCone ℝ (realified V))}
    (hS' : IsLocallyRationalDecomposition (rationalClosure C) S')
    {σ : PointedCone ℝ (realified V)} (hex : ∃ σ' ∈ S', σ ≤ σ') :
    ∃ σ' : PointedCone ℝ (realified V), IsLeastMem S' σ σ' := by
  classical
  let r : PointedCone ℝ (realified V) → ℕ :=
    fun τ => Module.finrank ℝ (Submodule.span ℝ (τ : Set (realified V)))
  let T : Set (PointedCone ℝ (realified V)) := {τ | τ ∈ S' ∧ σ ≤ τ}
  have hTne : T.Nonempty := hex
  obtain ⟨n, hnT, hnmin⟩ := Nat.lt_wfRel.wf.has_min (r '' T) (hTne.image r)
  obtain ⟨τ₀, hτ₀T, hτ₀n⟩ := hnT
  have hmin : ∀ τ ∈ T, r τ₀ ≤ r τ := by
    intro τ hτ
    rw [hτ₀n]
    exact not_lt.1 (hnmin (r τ) (Set.mem_image_of_mem r hτ))
  refine ⟨τ₀, hτ₀T.1, hτ₀T.2, ?_⟩
  intro τ hτ hστ
  have hface : (τ₀ ⊓ τ).IsFaceOf τ₀ :=
    inf_isFaceOf_of_isLocallyRationalDecomposition hS' hτ₀T.1 hτ
  have hinfT : τ₀ ⊓ τ ∈ T :=
    ⟨hS'.mem_of_isFaceOf hτ₀T.1 hface, le_inf hτ₀T.2 hστ⟩
  have hnotlt : ¬r (τ₀ ⊓ τ) < r τ₀ := not_lt.2 (hmin _ hinfT)
  have hchain : τ₀ ⊓ τ = τ₀ := by
    by_contra hne
    exact hnotlt (finrank_span_lt_of_isFaceOf_of_ne hface hne)
  rw [← hchain]
  exact inf_le_right

/-- **The least member of a genuine refinement**: for `S` refining `S'` and `σ ∈ S`, the least
member of `S'` containing `σ` exists. This is the availability half of Looijenga, Lemma 6.6, p. 30 —
"let `σ'` be the smallest member of `Σ'` that contains `σ`" — with the refinement hypothesis used
only to produce one containing member. -/
theorem exists_least_mem_of_refines [Module.Finite ℚ V] {C : PointedCone ℝ (realified V)}
    {S S' : Set (PointedCone ℝ (realified V))}
    (hS' : IsLocallyRationalDecomposition (rationalClosure C) S')
    (href : Refines S S') {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ S) :
    ∃ σ' : PointedCone ℝ (realified V), IsLeastMem S' σ σ' :=
  exists_least_mem_of_le hS' (href σ hσ)

/-- **The source's instance `Σ' = Σ(bb)`** (Looijenga, Lemma 6.6, p. 30, text line 823: "This
applies in particular to the case when `Σ'` is the Baily-Borel decomposition"): every member of a
locally rational decomposition of `C₊` has a least *face* of `C₊` containing it. The coarse family
is `facialDecomposition (rationalClosure C)`, a locally rational decomposition of `C₊` when `C₊` is
nondegenerate (`facialDecomposition_isLocallyRational`), and `S` refines it because every member of
`S` lies in `C₊ = rationalClosure C`, which is a face of itself. This shows that the refinement
hypothesis of `exists_least_mem_of_refines` is not vacuous. -/
theorem exists_least_mem_facialDecomposition [Module.Finite ℚ V]
    {C : PointedCone ℝ (realified V)}
    (hsal : ((rationalClosure C : PointedCone ℝ (realified V)) :
      ConvexCone ℝ (realified V)).Salient)
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ S) :
    ∃ F : PointedCone ℝ (realified V),
      IsLeastMem (facialDecomposition (rationalClosure C)) σ F :=
  exists_least_mem_of_refines (facialDecomposition_isLocallyRational _ hsal)
    (refines_facialDecomposition hS) hσ

end General

/-! ## The fibre-wise form: two decompositions of one conical fibre

Definition 6.1 (i), p. 28, requires that for every `ℚ`-isotropic line `I` the members of the
admissible decomposition inside `C_{I,+}` form a locally rational decomposition of `C_{I,+}`. The
fibre of `I` is `ConicalLine.closure`, so two admissible decompositions restrict on each fibre to
two locally rational decompositions of the same cone, and the refinement relation of Lemma 6.6 is
fibre-wise. The ambient space is `Type` here, as in `ConicalLocus.lean`.
-/

section Fibre

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- **A refinement of two decompositions of the conical locus**: on every conical fibre, the members
of the finer family lie in members of the coarser one. Looijenga, Lemma 6.6, p. 30, assumes exactly
this, fibre by fibre, of "`Σ'` ... refined by `Σ`"; Definition 6.1 (i), p. 28, is what makes a
conical-locus decomposition a family of decompositions of the fibres. -/
def RefinesLocus {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    (locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) : Prop :=
  ∀ F : ConicalLine BQ Q, Refines (locus F) (locus' F)

omit [Module.Finite ℚ V] in
theorem refinesLocus_iff {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))} :
    RefinesLocus locus locus' ↔
      ∀ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)),
        σ ∈ locus F → ∃ σ' ∈ locus' F, σ ≤ σ' :=
  Iff.rfl

/-- **The least coarse member, in a conical fibre** (Looijenga, Lemma 6.6, p. 30, first sentence): a
member `σ` of a locally rational decomposition `locus F` of the fibre of a `ℚ`-isotropic line, and a
coarser family `locus' F` refined by it, have a least member `σ'` of `locus' F` containing `σ`. Both
families are locally rational decompositions of the *same* carrier `F.closure = C_{I,+}`, which is
Definition 6.1 (i) at the fibre. Here `locus' F` is the source's `Σ'` *restricted* to the fibre,
"the members of `Σ'` contained in `C_{I,+}`", which is exactly how Definition 6.1 (i) presents a
conical-locus decomposition; the least member is sought there, as the source's "smallest member of
`Σ'`" requires. -/
theorem exists_least_mem_of_refines_fibre
    {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hcoarse : ∀ F : ConicalLine BQ Q, IsLocallyRationalDecomposition F.closure (locus' F))
    (href : RefinesLocus locus locus') (F : ConicalLine BQ Q)
    {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F) :
    ∃ σ' : PointedCone ℝ (realified ↥F.space), IsLeastMem (locus' F) σ σ' :=
  exists_least_mem_of_refines (hcoarse F) (href F) hσ

/-- **`V_σ ⊆ V_{σ'}` for the least containing coarse member in one fibre** (Looijenga, Lemma 6.6,
p. 30, the inclusion `V_σ ⊂ V_{σ'}`): the `Σ`-support space of a member of the finer decomposition
is contained in that of its least containing member in the coarser one, by monotonicity of the
support space in the member (`vSigma_mono`). The support space `vSigma` is Definition 6.1 (i)'s
formula; the inclusion is unconditional, and `vSigma_le_of_refines_of_not_isotropicHalfLine` below
records the source's case restriction. -/
theorem vSigma_le_of_refines
    {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hcoarse : ∀ F : ConicalLine BQ Q, IsLocallyRationalDecomposition F.closure (locus' F))
    (href : RefinesLocus locus locus') (F : ConicalLine BQ Q)
    {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F) :
    ∃ σ' : PointedCone ℝ (realified ↥F.space),
      IsLeastMem (locus' F) σ σ' ∧ vSigma F σ ≤ vSigma F σ' := by
  obtain ⟨σ', hσ'⟩ := exists_least_mem_of_refines_fibre hcoarse href F hσ
  exact ⟨σ', hσ', vSigma_mono hσ'.le⟩

/-- **Looijenga, Lemma 6.6, p. 30, for the members that Definition 6.1 (i) covers**: if `σ` is a
member of the finer fibre decomposition that is *not* an isotropic half line — so that its
`Σ`-support space is `V_σ = I ⊕ ⟨σ⟩` of Definition 6.1 (i), which is `vSigma` — then the least
member `σ'` of the coarser family containing it satisfies `V_σ ⊆ V_{σ'}`.

The hypothesis is the source's: Definition 6.1, p. 28, defines `V_σ` by case (i) only when `σ` is
not an isotropic half line in `C_{I,+}`. For an isotropic half line the support space is the one of
Lemma-Definition 4.5 (`sigmaSupportSpace`), not the span-based formula, and the comparison there is
`Semifan.sigmaSupportSpace_le_of_refines`. The inclusion proved here does not consume the hypothesis
(`vSigma_mono` is unconditional); it is carried so that the conclusion is not attributed to a member
whose support space the source defines by the other case. -/
theorem vSigma_le_of_refines_of_not_isotropicHalfLine
    {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hcoarse : ∀ F : ConicalLine BQ Q, IsLocallyRationalDecomposition F.closure (locus' F))
    (href : RefinesLocus locus locus') (F : ConicalLine BQ Q)
    {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F)
    (_hray : ¬ IsIsotropicHalfLine (fibreForm Q F.space) σ) :
    ∃ σ' : PointedCone ℝ (realified ↥F.space),
      IsLeastMem (locus' F) σ σ' ∧ vSigma F σ ≤ vSigma F σ' :=
  vSigma_le_of_refines hcoarse href F hσ

/-- **Lemma 6.6, p. 30, from the source's hypothesis**: the coarse family is an *admissible*
decomposition of the conical locus (Looijenga, Definition 6.1, p. 28), so condition (i) of
Definition 6.1 supplies its locally rational decomposition on every fibre; with a genuine refinement
of the finer family by it, every member `σ` of a fibre has a least coarse member `σ'` containing it,
and `V_σ ⊆ V_{σ'}`. This is the shape in which the refinement step is consumed downstream: neither
`Γ`-invariance nor condition (ii) of Definition 6.1 enters, only condition (i) and the refinement.
-/
theorem vSigma_le_of_refines_of_isAdmissibleDecomposition
    {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    {Γ : Set (V ≃ₗ[ℚ] V)}
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hcoarse : IsAdmissibleDecomposition BQ Q Γ locus')
    (href : RefinesLocus locus locus') (F : ConicalLine BQ Q)
    {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F) :
    ∃ σ' : PointedCone ℝ (realified ↥F.space),
      IsLeastMem (locus' F) σ σ' ∧ vSigma F σ ≤ vSigma F σ' :=
  vSigma_le_of_refines (fun F => hcoarse.condition_i F) href F hσ

end Fibre

end LeanCategories.Lattices.Valued
