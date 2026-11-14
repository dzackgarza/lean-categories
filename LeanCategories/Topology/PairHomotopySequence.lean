/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path

@[expose] public section

/-!
# The extended exact sequence of a pair, and Hatcher Exercise 4.1.9(a)

Hatcher, *Algebraic Topology* (2002), §4.1 defines the relative homotopy groups
`πₙ(X, A, x₀)` of a pair as the homotopy classes of maps of triples
`(Iⁿ, ∂Iⁿ, J^{n-1}) → (X, A, x₀)`, homotopies through maps of the same form (p. 343).
For `n = 1` the `0`-end of `I` is constrained only to lie in `A`, so two relative classes
with *different* start points may agree: `π₁(X, A, x₀)` is not `Σ a : A, π₁(X, a)`-shaped.
This file's `RelativePiOne` is that quotient, and it is the point on which the disputed
reading of Exercise 9(a) turned.

Exercise 9 (printed p. 358) extends the sequence of the pair by
`π₀(X, A, x₀) := π₀(X, x₀) / i_* π₀(A, x₀)` and asserts that the five lemma holds for the
map of sequences induced by a map of pairs `(X, A, x₀) → (Y, B, y₀)`:

> One of the maps between the two sequences is a bijection if the four surrounding maps are
> bijections for all choices of `x₀`.

This file settles both terms where the sequence stops being one of groups, on the affirmative
side, by proof — no counterexample is needed:

* `relativePiOne_map_bijective` — at `π₁(X, A, x₀)`, from bijectivity of
  `π₁(A, a) → π₁(B, f a)`, `π₁(X, a) → π₁(Y, f a)` (all `a ∈ A`), `π₀(A) → π₀(B)` and
  `π₀(X) → π₀(Y)`;
* `zerothHomotopySubtypeMap_bijective` — at `π₀(A, x₀)`, from bijectivity of
  `π₁(X, A, a) → π₁(Y, B, f a)`, `π₁(X, a) → π₁(Y, f a)` (all `a ∈ A`),
  `π₀(X) → π₀(Y)` and `π₀(X, A, x₀) → π₀(Y, B, f x₀)`.

## The sequence

`RelativePiOne.ofLoop` is `π₁(X, x₀) → π₁(X, A, x₀)`, `RelativePiOne.boundary` is
`∂ : π₁(X, A, x₀) → π₀(A, x₀)`, `zerothHomotopySubtypeMap` is `π₀(A) → π₀(X)`,
`PairZerothHomotopy.mk` is `π₀(X) → π₀(X, A, x₀)`. Exactness at the two joins that are not
group statements is `RelativePiOne.boundary_eq_base_iff` (kernel of `∂` is the image of
`π₁(X, x₀)`, Hatcher Exercise 8) and `RelativePiOne.zerothHomotopyMk_eq_iff` (kernel of
`π₀(A) → π₀(X)` is the image of `∂`); exactness at `π₀(X, A, x₀)` is
`PairZerothHomotopy.mk_eq_mk_base_iff`, which is the definition of the quotient.

## LC-09 search record

`scripts/formalization_corpus.py search` (2026-11-14) with the queries
`content:ZerothHomotopy`, `content:relative homotopy`, `content:Path.Homotopic`,
`content:FundamentalGroupoid`, `content:"relative homotopy group"`,
`content:"long exact sequence" file:Homotopy`, `content:"five lemma"`,
`content:"π_rel" content:"def "`, `content:RelativeHomotopyGroup`, `repo:TauCeti file:Relative`,
plus local Mathlib.  Hits: Mathlib's `ZerothHomotopy` (with `mk`, `sound`, `lift`),
`Path.Homotopic.Quotient` with `mk_trans`/`mk_symm`/`mk_refl`/`map_comp`, the groupoid laws
`Path.Homotopic.Quotient.trans_assoc`/`refl_trans`/`trans_refl`/`symm_trans`/`trans_symm`
(`Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean`), `Path.map_trans`/`map_symm`/
`map_map`, and `FundamentalGroup`; all are imported and used.  The corpus holds no
formalization of `π₁(X, A, x₀)` for `n = 1`, of the `π₀` tail of the sequence, or of the
five lemma at a set-valued term: the nearest hits are `Vilin97/lean-pool`'s `π_rel` (relative
homotopy groups of disks, inside a Whitehead-theorem development, for `n ≥ 1` with no `π₀`
tail) and TauCeti's relative Hurewicz homomorphism, neither of which supplies a definition the
`π₀(A)` term can consume, so the definitions here are written rather than ported.  Mathlib's
`five lemma` results (`CategoryTheory.FiveLemma`) are for abelian categories and do not apply
to pointed sets.

## References

* Hatcher, *Algebraic Topology*, §4.1, p. 343 (relative homotopy groups), Exercise 8 and
  Exercise 9 (printed p. 358). In the project's copy of the source,
  `.tmp-sources/hatcher-2002-algebraic-topology.md`, the definition is line 7195, Exercise 8 is
  line 7485 and Exercise 9 is line 7489.
* R. Brown, "Fibrations of groupoids", *J. Algebra* 15 (1970), Theorem 4.9 and Corollary 4.11
  (pp. 121–123): the groupoid form of the same five lemma, which is why Hatcher's statement
  needs basepoints varying over `A`.
-/

noncomputable section
open scoped Topology

namespace LeanCategories.Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- Postcomposition of path homotopy classes is additive with respect to concatenation. -/
theorem pathClassMap_trans (f : C(X, Y)) {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      exact congrArg Path.Homotopic.Quotient.mk (Path.map_trans p q f.continuous)

/-- Postcomposition of path homotopy classes commutes with reversal. -/
theorem pathClassMap_symm (f : C(X, Y)) {x y : X} (p : Path.Homotopic.Quotient x y) :
    p.symm.map f = (p.map f).symm := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => exact congrArg Path.Homotopic.Quotient.mk (Path.map_symm p f.continuous)

/-- Postcomposition of path homotopy classes preserves the constant class. -/
theorem pathClassMap_refl (f : C(X, Y)) (x : X) :
    (Path.Homotopic.Quotient.refl x).map f = Path.Homotopic.Quotient.refl (f x) := by
  rfl

/-- The inclusion of a subspace as a continuous map. -/
def subtypeIncl (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem subtypeIncl_apply (A : Set X) (a : A) : subtypeIncl A a = (a : X) := rfl

/-- A path homotopy class inside a subspace, pushed into the ambient space. -/
def subspacePathClass {A : Set X} {a a' : A} (γ : Path.Homotopic.Quotient a a') :
    Path.Homotopic.Quotient (a : X) (a' : X) :=
  γ.map (subtypeIncl A)

theorem subspacePathClass_mk {A : Set X} {a a' : A} (γ : Path a a') :
    subspacePathClass (A := A) (Path.Homotopic.Quotient.mk γ) =
      Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val) := rfl

theorem subspacePathClass_trans {A : Set X} {a a' a'' : A}
    (γ : Path.Homotopic.Quotient a a') (γ' : Path.Homotopic.Quotient a' a'') :
    subspacePathClass (A := A) (γ.trans γ') =
      (subspacePathClass (A := A) γ).trans (subspacePathClass (A := A) γ') :=
  pathClassMap_trans (subtypeIncl A) γ γ'

theorem subspacePathClass_symm {A : Set X} {a a' : A} (γ : Path.Homotopic.Quotient a a') :
    subspacePathClass (A := A) γ.symm = (subspacePathClass (A := A) γ).symm :=
  pathClassMap_symm (subtypeIncl A) γ

theorem subspacePathClass_refl {A : Set X} (a : A) :
    subspacePathClass (A := A) (Path.Homotopic.Quotient.refl a) =
      Path.Homotopic.Quotient.refl (a : X) :=
  pathClassMap_refl (subtypeIncl A) a

theorem subspacePathClass_mk_refl {A : Set X} (a : A) :
    subspacePathClass (A := A) (Path.Homotopic.Quotient.mk (Path.refl a)) =
      Path.Homotopic.Quotient.refl (a : X) := by
  rw [Path.Homotopic.Quotient.mk_refl]
  exact subspacePathClass_refl a

theorem subspacePathClass_mk_trans {A : Set X} {a a' a'' : A}
    (δ : Path a a') (δ' : Path a' a'') :
    subspacePathClass (A := A) (Path.Homotopic.Quotient.mk (δ.trans δ')) =
      (subspacePathClass (A := A) (Path.Homotopic.Quotient.mk δ)).trans
        (subspacePathClass (A := A) (Path.Homotopic.Quotient.mk δ')) := by
  rw [Path.Homotopic.Quotient.mk_trans]
  exact subspacePathClass_trans _ _

theorem subspacePathClass_mk_symm {A : Set X} {a a' : A} (δ : Path a a') :
    subspacePathClass (A := A) (Path.Homotopic.Quotient.mk δ.symm) =
      (subspacePathClass (A := A) (Path.Homotopic.Quotient.mk δ)).symm := by
  rw [Path.Homotopic.Quotient.mk_symm]
  exact subspacePathClass_symm _

/-- A path homotopy class is joining: its endpoints are in the same path component. -/
theorem pathClass_joined {x y : X} (γ : Path.Homotopic.Quotient x y) :
    ZerothHomotopy.mk x = ZerothHomotopy.mk y := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ => exact ZerothHomotopy.sound γ


/-! #### The induced map on path components -/

/-- The map on path components induced by a continuous map. -/
def zerothHomotopyMap (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun _ _ p => ZerothHomotopy.sound (p.map f.continuous))

@[simp] theorem zerothHomotopyMap_mk (f : C(X, Y)) (x : X) :
    zerothHomotopyMap f (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) := rfl

/-- The map on path components induced by the inclusion of a subspace. -/
def zerothHomotopySubtypeMap (A : Set X) : ZerothHomotopy A → ZerothHomotopy X :=
  zerothHomotopyMap (subtypeIncl A)

@[simp] theorem zerothHomotopySubtypeMap_mk (A : Set X) (a : A) :
    zerothHomotopySubtypeMap A (ZerothHomotopy.mk a) = ZerothHomotopy.mk (a : X) := rfl

/-- A path component of `X` that meets the subspace `A`. -/
def InSubspace (A : Set X) (p : ZerothHomotopy X) : Prop :=
  ∃ a : A, ZerothHomotopy.mk (a : X) = p

theorem inSubspace_mk_iff {A : Set X} {x : X} :
    InSubspace A (ZerothHomotopy.mk x) ↔ ∃ a : A, Joined (a : X) x := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Quotient.exact ha⟩
  · rintro ⟨a, h⟩
    exact ⟨a, Quotient.sound h⟩

theorem inSubspace_mk_of_mem {A : Set X} {x : X} (h : x ∈ A) :
    InSubspace A (ZerothHomotopy.mk x) :=
  ⟨⟨x, h⟩, rfl⟩

/-! #### `π₀(X, A, x₀)` -/

/-- The setoid on `π₀(X)` that collapses the path components meeting `A`, giving `π₀(X, A, x₀)`
as defined in Hatcher §4.1 Exercise 9. -/
def pairZerothHomotopySetoid (A : Set X) : Setoid (ZerothHomotopy X) where
  r p q := p = q ∨ (InSubspace A p ∧ InSubspace A q)
  iseqv :=
    ⟨fun _ => Or.inl rfl,
      fun {_ _} h => h.elim (fun h' => Or.inl h'.symm) fun h => Or.inr ⟨h.2, h.1⟩,
      fun {_ _ _} h₁ h₂ => h₁.elim (fun h' => h'.symm ▸ h₂) fun h =>
        h₂.elim (fun h' => Or.inr ⟨h.1, h' ▸ h.2⟩) fun h' => Or.inr ⟨h.1, h'.2⟩⟩

/-- `π₀(X, A, x₀) = π₀(X, x₀) / i_* π₀(A, x₀)`: the path components of `X` with those meeting
`A` identified.  Source: Hatcher, *Algebraic Topology*, §4.1 Exercise 9 (printed p. 358). -/
def PairZerothHomotopy (A : Set X) :=
  Quotient (pairZerothHomotopySetoid A)

namespace PairZerothHomotopy

variable {A : Set X}

/-- The class of a path component of `X` in `π₀(X, A, x₀)`. -/
def mk (p : ZerothHomotopy X) : PairZerothHomotopy A :=
  Quotient.mk _ p

theorem mk_eq_mk_iff {p q : ZerothHomotopy X} :
    (mk p : PairZerothHomotopy A) = mk q ↔ p = q ∨ (InSubspace A p ∧ InSubspace A q) :=
  Quotient.eq

theorem mk_eq_mk_of_mem {p q : ZerothHomotopy X} (hp : InSubspace A p) (hq : InSubspace A q) :
    (mk p : PairZerothHomotopy A) = mk q :=
  (mk_eq_mk_iff).2 (Or.inr ⟨hp, hq⟩)

theorem mk_eq_mk_base_iff {x₀ : X} (hx₀ : x₀ ∈ A) (p : ZerothHomotopy X) :
    (mk p : PairZerothHomotopy A) = mk (ZerothHomotopy.mk x₀) ↔ InSubspace A p := by
  rw [mk_eq_mk_iff]
  exact ⟨fun h => h.elim (fun h' => h' ▸ inSubspace_mk_of_mem hx₀) fun h => h.1,
    fun hp => Or.inr ⟨hp, inSubspace_mk_of_mem hx₀⟩⟩

theorem mk_eq_mk_of_mk_eq {p q : ZerothHomotopy X} (h : p = q) :
    (mk p : PairZerothHomotopy A) = mk q :=
  congrArg mk h

theorem ind {motive : PairZerothHomotopy A → Prop} (h : ∀ p, motive (mk p))
    (q : PairZerothHomotopy A) : motive q :=
  Quotient.ind h q

/-- The map `π₀(X, A, x₀) → π₀(Y, B, y₀)` induced by a map of pairs. -/
def map (f : C(X, Y)) {B : Set Y} (hAB : ∀ x ∈ A, f x ∈ B) :
    PairZerothHomotopy A → PairZerothHomotopy B :=
  Quotient.map (zerothHomotopyMap f) (fun p q hpq => by
    rcases hpq with hpq | ⟨hp, hq⟩
    · exact Or.inl (congrArg (zerothHomotopyMap f) hpq)
    · refine Or.inr ⟨?_, ?_⟩
      · obtain ⟨a, ha⟩ := hp
        refine ⟨⟨f a, hAB a a.2⟩, ?_⟩
        rw [← ha, zerothHomotopyMap_mk]
      · obtain ⟨a, ha⟩ := hq
        refine ⟨⟨f a, hAB a a.2⟩, ?_⟩
        rw [← ha, zerothHomotopyMap_mk])

@[simp] theorem map_mk (f : C(X, Y)) {B : Set Y} (hAB : ∀ x ∈ A, f x ∈ B)
    (p : ZerothHomotopy X) :
    map f hAB (mk p) = mk (A := B) (zerothHomotopyMap f p) := rfl

end PairZerothHomotopy


/-! #### Maps of pairs on fundamental groups -/

/-- The map `A → B` induced by a map of pairs, as a continuous map. -/
def restrictMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hAB : ∀ x ∈ A, f x ∈ B) : C(A, B) :=
  ⟨fun a => ⟨f a, hAB a a.2⟩,
    (f.comp (subtypeIncl A)).continuous.codRestrict fun a => hAB a a.2⟩

@[simp] theorem restrictMap_apply (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) (a : A) : (restrictMap f hAB a : Y) = f a := rfl

@[simp] theorem restrictMap_apply_subtype (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) (a : A) :
    (restrictMap f hAB a : B) = ⟨f a, hAB a a.2⟩ := rfl

/-- The map on `π₁` induced by a continuous map, as a function between loop classes. -/
abbrev fundamentalGroupMap (f : C(X, Y)) {x₀ : X} :
    Path.Homotopic.Quotient x₀ x₀ → Path.Homotopic.Quotient (f x₀) (f x₀) :=
  fun γ => γ.map f

@[simp] theorem fundamentalGroupMap_trans (f : C(X, Y)) {x₀ : X}
    (p q : Path.Homotopic.Quotient x₀ x₀) :
    fundamentalGroupMap f (p.trans q) = (fundamentalGroupMap f p).trans (fundamentalGroupMap f q) :=
  pathClassMap_trans f p q

@[simp] theorem fundamentalGroupMap_refl (f : C(X, Y)) (x₀ : X) :
    fundamentalGroupMap f (Path.Homotopic.Quotient.refl x₀) =
      Path.Homotopic.Quotient.refl (f x₀) :=
  pathClassMap_refl f x₀

/-- The map on `π₁(A, a)` induced by a map of pairs. -/
abbrev pairFundamentalGroupMap (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) (a : A) :
    Path.Homotopic.Quotient a a →
      Path.Homotopic.Quotient (restrictMap f hAB a) (restrictMap f hAB a) :=
  fun γ => γ.map (restrictMap f hAB)

/-- Pushing a path inside a subspace into the target of a map of pairs agrees with mapping
the path along `f` and then restricting to the codomain. -/
theorem pathMap_subspacePathClass (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) {a a' : A} (γ : Path a a') :
    (γ.map continuous_subtype_val).map f.continuous =
      (γ.map (restrictMap f hAB).continuous).map continuous_subtype_val := by
  rw [Path.map_map, Path.map_map]
  rfl

/-- The fundamental-group map of a map of pairs, pushed into the ambient space of the target,
agrees with the fundamental-group map of the ambient map through the inclusion of `A`. -/
theorem fundamentalGroupMap_subspacePathClass (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) {a a' : A} (γ : Path.Homotopic.Quotient a a') :
    (subspacePathClass (A := A) γ).map f =
      (γ.map (restrictMap f hAB)).map (subtypeIncl B) := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ => exact congrArg Path.Homotopic.Quotient.mk (pathMap_subspacePathClass f hAB γ)


/-! #### `π₁(X, A, x₀)` -/

/-- The relation on relative path classes: two pairs are related when a path inside `A` joins
their start points and carries one path class to the other. -/
def relativePiOneRel {A : Set X} (x₀ : X) :
    (Σ a : A, Path.Homotopic.Quotient (a : X) x₀) →
      (Σ a : A, Path.Homotopic.Quotient (a : X) x₀) → Prop :=
  fun p q => ∃ δ : Path p.1 q.1, (subspacePathClass (Path.Homotopic.Quotient.mk δ)).trans q.2 = p.2

theorem relativePiOneRel_refl {A : Set X} {x₀ : X}
    (p : Σ a : A, Path.Homotopic.Quotient (a : X) x₀) : relativePiOneRel x₀ p p :=
  ⟨Path.refl p.1, by rw [subspacePathClass_mk_refl, Path.Homotopic.Quotient.refl_trans]⟩

theorem relativePiOneRel_symm {A : Set X} {x₀ : X}
    {p q : Σ a : A, Path.Homotopic.Quotient (a : X) x₀} (h : relativePiOneRel x₀ p q) :
    relativePiOneRel x₀ q p := by
  obtain ⟨δ, hδ⟩ := h
  refine ⟨δ.symm, ?_⟩
  rw [subspacePathClass_mk_symm, ← hδ, ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

theorem relativePiOneRel_trans {A : Set X} {x₀ : X}
    {p q r : Σ a : A, Path.Homotopic.Quotient (a : X) x₀}
    (h₁ : relativePiOneRel x₀ p q) (h₂ : relativePiOneRel x₀ q r) :
    relativePiOneRel x₀ p r := by
  obtain ⟨δ₁, hδ₁⟩ := h₁
  obtain ⟨δ₂, hδ₂⟩ := h₂
  exact ⟨δ₁.trans δ₂,
    by rw [subspacePathClass_mk_trans, Path.Homotopic.Quotient.trans_assoc, hδ₂, hδ₁]⟩

/-- The setoid whose quotient is `π₁(X, A, x₀)`. -/
def relativePiOneSetoid (A : Set X) (x₀ : X) :
    Setoid (Σ a : A, Path.Homotopic.Quotient (a : X) x₀) :=
  ⟨relativePiOneRel x₀, relativePiOneRel_refl, relativePiOneRel_symm, relativePiOneRel_trans⟩

/-- `π₁(X, A, x₀)`: homotopy classes of paths starting in `A` and ending at `x₀`, modulo
homotopies through such paths — the start point may move inside `A` during the homotopy.

Source: Hatcher, *Algebraic Topology*, §4.1, p. 343: `πₙ(X, A, x₀)` is the set of homotopy classes
of maps of triples `(Iⁿ, ∂Iⁿ, J^{n-1}) → (X, A, x₀)`; for `n = 1` the `0`-end of `I` is only
constrained to lie in `A`, so two classes with different start points may agree. -/
def RelativePiOne (A : Set X) (x₀ : X) : Type u :=
  Quotient (relativePiOneSetoid A x₀)

namespace RelativePiOne

variable {A : Set X} {x₀ : X}

/-- The class of a path starting at `a ∈ A` and ending at the basepoint. -/
abbrev mk (a : A) (γ : Path.Homotopic.Quotient (a : X) x₀) : RelativePiOne A x₀ :=
  Quotient.mk _ ⟨a, γ⟩

/-- Elimination for `π₁(X, A, x₀)`. -/
theorem ind {motive : RelativePiOne A x₀ → Prop}
    (h : ∀ p : Σ a : A, Path.Homotopic.Quotient (a : X) x₀, motive (Quotient.mk _ p))
    (q : RelativePiOne A x₀) : motive q :=
  Quotient.ind h q

theorem mk_eq_mk_iff {a a' : A} {γ : Path.Homotopic.Quotient (a : X) x₀}
    {γ' : Path.Homotopic.Quotient (a' : X) x₀} :
    (mk a γ : RelativePiOne A x₀) = mk a' γ' ↔
      ∃ δ : Path a a', (subspacePathClass (Path.Homotopic.Quotient.mk δ)).trans γ' = γ :=
  Quotient.eq

/-- Two relative classes whose start points are joined inside `A` agree. -/
theorem mk_eq_mk_of_path {a a' : A} (δ : Path a a')
    (γ' : Path.Homotopic.Quotient (a' : X) x₀) :
    (mk a ((subspacePathClass (Path.Homotopic.Quotient.mk δ)).trans γ') :
        RelativePiOne A x₀) = mk a' γ' :=
  mk_eq_mk_iff.2 ⟨δ, rfl⟩

/-- Two relative classes whose start points are joined inside `A` agree, for a joining class. -/
theorem mk_eq_mk_of_pathClass {a a' : A} (δ : Path.Homotopic.Quotient a a')
    (γ' : Path.Homotopic.Quotient (a' : X) x₀) :
    (mk a ((subspacePathClass δ).trans γ') : RelativePiOne A x₀) = mk a' γ' := by
  induction δ using Path.Homotopic.Quotient.ind with
  | mk δ => exact mk_eq_mk_of_path δ γ'

/-- Moving the start point of a relative class backwards along a path inside `A`. -/
theorem mk_eq_mk_of_left {a a' : A} (δ : Path a a')
    (γ : Path.Homotopic.Quotient (a : X) x₀) :
    (mk a γ : RelativePiOne A x₀) =
      mk a' ((subspacePathClass (Path.Homotopic.Quotient.mk δ)).symm.trans γ) := by
  rw [← subspacePathClass_mk_symm, mk_eq_mk_of_path]


/-- `∂ : π₁(X, A, x₀) → π₀(A, x₀)`: the path component of the start point. -/
def boundary {A : Set X} {x₀ : X} : RelativePiOne A x₀ → ZerothHomotopy A :=
  Quotient.lift (fun p => ZerothHomotopy.mk p.1) fun _ q h => by
    obtain ⟨δ, _⟩ := h
    exact ZerothHomotopy.sound δ

@[simp] theorem boundary_mk {A : Set X} {x₀ : X} (a : A)
    (γ : Path.Homotopic.Quotient (a : X) x₀) :
    boundary (mk a γ) = ZerothHomotopy.mk a := rfl

/-- `π₁(X, x₀) → π₁(X, A, x₀)`: a loop at `x₀ ∈ A` is a path starting in `A`. -/
def ofLoop {A : Set X} {x₀ : X} (hx₀ : x₀ ∈ A)
    (γ : Path.Homotopic.Quotient x₀ x₀) : RelativePiOne A x₀ :=
  mk ⟨x₀, hx₀⟩ γ

@[simp] theorem boundary_ofLoop {A : Set X} {x₀ : X} (hx₀ : x₀ ∈ A)
    (γ : Path.Homotopic.Quotient x₀ x₀) :
    boundary (ofLoop hx₀ γ) = ZerothHomotopy.mk ⟨x₀, hx₀⟩ := rfl

/-- Exactness of the pair sequence at `π₁(X, A, x₀)`: the kernel of `∂` is the image of `π₁(X, x₀)`.

Source: Hatcher, *Algebraic Topology*, §4.1 Exercise 8 (printed p. 358), the exact sequence
`π₁(X, x₀) → π₁(X, A, x₀) → π₀(A, x₀) → π₀(X, x₀)`. -/
theorem boundary_eq_base_iff {A : Set X} {x₀ : X} (hx₀ : x₀ ∈ A) (p : RelativePiOne A x₀) :
    boundary p = ZerothHomotopy.mk ⟨x₀, hx₀⟩ ↔
      ∃ γ : Path.Homotopic.Quotient x₀ x₀, p = ofLoop hx₀ γ := by
  refine Quotient.inductionOn p (fun p => ?_)
  obtain ⟨a, γ⟩ := p
  constructor
  · intro h
    have hj : Joined a ⟨x₀, hx₀⟩ := Quotient.exact h
    exact ⟨_, mk_eq_mk_of_left hj.somePath γ⟩
  · rintro ⟨γ', hγ'⟩
    rw [hγ']
    rfl

/-- Exactness of the pair sequence at `π₀(A, x₀)`: two points of `A` lie in the same path
component of `X` exactly when one of them is the start point of a relative class.

Source: Hatcher, *Algebraic Topology*, §4.1 Exercise 8 (printed p. 358). -/
theorem zerothHomotopyMk_eq_iff {A : Set X} {x₀ : X} (a : A) :
    ZerothHomotopy.mk (a : X) = ZerothHomotopy.mk x₀ ↔
      ∃ p : RelativePiOne A x₀, boundary p = ZerothHomotopy.mk a := by
  constructor
  · intro h
    exact ⟨mk a (Path.Homotopic.Quotient.mk (Quotient.exact h).somePath), rfl⟩
  · rintro ⟨p, hp⟩
    revert hp
    refine Quotient.inductionOn p (fun p => ?_)
    obtain ⟨a', γ⟩ := p
    intro hp
    simp only [boundary_mk] at hp
    have hj : Joined (a : X) (a' : X) := ((Quotient.exact hp).symm).map continuous_subtype_val
    exact (ZerothHomotopy.sound hj.somePath).trans (pathClass_joined (X := X) γ)

/-- The map `π₁(X, A, x₀) → π₁(Y, B, y₀)` induced by a map of pairs. -/
def map {A : Set X} {x₀ : X} (f : C(X, Y)) {B : Set Y} (hAB : ∀ x ∈ A, f x ∈ B) :
    RelativePiOne A x₀ → RelativePiOne B (f x₀) :=
  Quotient.map (fun p => ⟨⟨f p.1, hAB p.1 p.1.2⟩, p.2.map f⟩) fun p q hpq => by
    obtain ⟨a, γ⟩ := p
    obtain ⟨a', γ'⟩ := q
    obtain ⟨δ, hδ⟩ := hpq
    refine ⟨δ.map (restrictMap f hAB).continuous, ?_⟩
    rw [← hδ, pathClassMap_trans, fundamentalGroupMap_subspacePathClass]
    rfl

@[simp] theorem map_mk {A : Set X} {x₀ : X} (f : C(X, Y)) {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) (a : A)
    (γ : Path.Homotopic.Quotient (a : X) x₀) :
    map f hAB (mk a γ) =
      mk ⟨f a, hAB a a.2⟩ (γ.map f) := rfl

/-- `∂` of the class induced by a map of pairs, on a class with a chosen start point. -/
@[simp] theorem boundary_map_mk {A : Set X} {x₀ : X} (f : C(X, Y)) {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) (a : A) (γ : Path.Homotopic.Quotient (a : X) x₀) :
    boundary (map f hAB (mk a γ)) = ZerothHomotopy.mk ⟨f a, hAB a a.2⟩ := rfl

/-- Naturality of `∂` with respect to a map of pairs. -/
theorem boundary_map {A : Set X} {x₀ : X} (f : C(X, Y)) {B : Set Y}
    (hAB : ∀ x ∈ A, f x ∈ B) (p : RelativePiOne A x₀) :
    boundary (map f hAB p) = zerothHomotopyMap (restrictMap f hAB) (boundary p) := by
  refine Quotient.inductionOn p (fun p => ?_)
  obtain ⟨a, γ⟩ := p
  rfl


end RelativePiOne

open RelativePiOne

/-- Postcomposition by a continuous map is injective on path classes starting at `x` as soon as
it is injective on loops at `x`. -/
theorem pathClassMap_injective_of_loop {f : C(X, Y)} {x : X}
    (h : Function.Injective (fundamentalGroupMap f (x₀ := x))) {y : X}
    {p q : Path.Homotopic.Quotient x y} (hpq : p.map f = q.map f) : p = q := by
  have hloop : (p.trans q.symm).map f = Path.Homotopic.Quotient.refl (f x) := by
    rw [pathClassMap_trans, pathClassMap_symm, hpq, Path.Homotopic.Quotient.trans_symm]
  have h1 : p.trans q.symm = Path.Homotopic.Quotient.refl x := h hloop
  calc p = p.trans (Path.Homotopic.Quotient.refl y) :=
        (Path.Homotopic.Quotient.trans_refl p).symm
    _ = p.trans (q.symm.trans q) := by rw [Path.Homotopic.Quotient.symm_trans]
    _ = (p.trans q.symm).trans q := (Path.Homotopic.Quotient.trans_assoc p q.symm q).symm
    _ = (Path.Homotopic.Quotient.refl x).trans q := by rw [h1]
    _ = q := Path.Homotopic.Quotient.refl_trans q

/-! #### Hatcher Exercise 4.1.9(a) -/

/-- **Hatcher §4.1 Exercise 9(a), at the term `π₁(X, A, x₀)`.**  A map of pairs whose four
surrounding maps in the sequence of the pair are bijections at every basepoint induces a
bijection `π₁(X, A, x₀) → π₁(Y, B, f x₀)`.

The four surrounding maps of the `π₁(X, A, x₀)` term are `π₁(A, a) → π₁(B, f a)`,
`π₁(X, a) → π₁(Y, f a)`, `π₀(A) → π₀(B)` and `π₀(X) → π₀(Y)`, the first two required for all
`a ∈ A`.

Source: Hatcher, *Algebraic Topology*, §4.1 Exercise 9(a) (printed p. 358). -/
theorem relativePiOne_map_bijective {A : Set X} {B : Set Y} (f : C(X, Y))
    (hAB : ∀ x ∈ A, f x ∈ B) {x₀ : X} (hx₀ : x₀ ∈ A)
    (hA₀ : Function.Bijective (zerothHomotopyMap (restrictMap f hAB)))
    (hX : ∀ a : A, Function.Bijective (fundamentalGroupMap f (x₀ := (a : X))))
    (hA : ∀ a : A, Function.Bijective (pairFundamentalGroupMap f hAB a))
    (hX₀ : Function.Bijective (zerothHomotopyMap f)) :
    Function.Bijective (map (x₀ := x₀) f hAB) := by
  refine ⟨?_, ?_⟩
  · rintro p q hpq
    revert hpq
    refine Quotient.inductionOn p (fun p => ?_)
    obtain ⟨a, γ⟩ := p
    refine Quotient.inductionOn q (fun q => ?_)
    obtain ⟨a', γ'⟩ := q
    intro hpq
    -- the two start points lie in the same path component of `B`
    have hb : ZerothHomotopy.mk ((restrictMap f hAB) a) =
        ZerothHomotopy.mk ((restrictMap f hAB) a') := by
      have h := congrArg (boundary (A := B) (x₀ := f x₀)) hpq
      simpa using h
    -- hence in the same path component of `A`
    have hjA : Joined a a' := Quotient.exact (hA₀.injective hb)
    -- rewrite the first class to start at `a'`
    have hp : (mk a γ : RelativePiOne A x₀) =
        mk a' ((subspacePathClass (Path.Homotopic.Quotient.mk hjA.somePath)).symm.trans γ) :=
      mk_eq_mk_of_left hjA.somePath γ
    have hmap : map (x₀ := x₀) f hAB
        (mk a' ((subspacePathClass (Path.Homotopic.Quotient.mk hjA.somePath)).symm.trans γ)) =
        map (x₀ := x₀) f hAB (mk a' γ') := by
      rw [← hp]
      exact hpq
    rw [map_mk, map_mk] at hmap
    obtain ⟨δB, hδB⟩ := (mk_eq_mk_iff (x₀ := f x₀)).1 hmap
    -- lift the difference loop from `B` back to `A`
    obtain ⟨ε, hε⟩ := (hA a').surjective (Path.Homotopic.Quotient.mk δB)
    have hsp : (subspacePathClass (Path.Homotopic.Quotient.mk δB) :
        Path.Homotopic.Quotient (f a') (f a')) =
        fundamentalGroupMap f (subspacePathClass (A := A) ε) := by
      have h1 : subspacePathClass (pairFundamentalGroupMap f hAB a' ε) =
          fundamentalGroupMap f (subspacePathClass (A := A) ε) :=
        (fundamentalGroupMap_subspacePathClass f hAB ε).symm
      rwa [hε] at h1
    -- the two path classes at `a'` agree after the loop correction
    have key : ((subspacePathClass (Path.Homotopic.Quotient.mk hjA.somePath)).symm.trans γ).map f =
        ((subspacePathClass (A := A) ε).trans γ').map f := by
      rw [← hδB, hsp, pathClassMap_trans]
    have hγeq : (subspacePathClass (Path.Homotopic.Quotient.mk hjA.somePath)).symm.trans γ =
        (subspacePathClass (A := A) ε).trans γ' :=
      pathClassMap_injective_of_loop (hX a').injective key
    have hfin : (mk a'
        ((subspacePathClass (Path.Homotopic.Quotient.mk hjA.somePath)).symm.trans γ) :
        RelativePiOne A x₀) = mk a' γ' := by
      rw [hγeq]
      exact mk_eq_mk_of_pathClass ε γ'
    exact hp.trans hfin
  · intro q
    refine Quotient.inductionOn q (fun q => ?_)
    obtain ⟨b, σ⟩ := q
    -- a point of `A` above the component of `b`
    obtain ⟨c, hc⟩ := hA₀.surjective (ZerothHomotopy.mk b)
    obtain ⟨a, rfl⟩ := ZerothHomotopy.mk_surjective c
    have hc' : ZerothHomotopy.mk (⟨f a, hAB a a.2⟩ : B) = ZerothHomotopy.mk b := hc
    have hjoinB : Joined (⟨f a, hAB a a.2⟩ : B) b := Quotient.exact hc'
    -- the joining path in `B`, seen in `Y`
    set hjoinY : Path.Homotopic.Quotient (f a) (b : Y) :=
      subspacePathClass (A := B) (a := (⟨f a, hAB a a.2⟩ : B)) (a' := b)
        (Path.Homotopic.Quotient.mk hjoinB.somePath) with hjoinYdef
    -- the target class rewritten to start at `f a`
    set τ : Path.Homotopic.Quotient (f a) (f x₀) := hjoinY.trans σ with hτdef
    have hq : (mk b σ : RelativePiOne B (f x₀)) = mk (⟨f a, hAB a a.2⟩ : B) τ := by
      rw [hτdef, hjoinYdef]
      exact (mk_eq_mk_of_path hjoinB.somePath σ).symm
    -- the component of `a` in `X` is that of the basepoint
    have hzx : ZerothHomotopy.mk (a : X) = ZerothHomotopy.mk x₀ := by
      refine hX₀.injective ?_
      exact (pathClass_joined (X := Y) hjoinY).trans (pathClass_joined (X := Y) σ)
    -- adjust a path from `a` to `x₀` by a loop so that it maps to the target path
    set γ : Path.Homotopic.Quotient (a : X) x₀ :=
      Path.Homotopic.Quotient.mk (Quotient.exact hzx).somePath with hγdef
    obtain ⟨lam, hlam⟩ := (hX ⟨x₀, hx₀⟩).surjective ((γ.map f).symm.trans τ)
    have hlam' : lam.map f = (γ.map f).symm.trans τ := hlam
    have hτeq : (γ.trans lam).map f = τ := by
      rw [pathClassMap_trans, hlam', ← Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
    refine ⟨mk a (γ.trans lam), ?_⟩
    rw [map_mk, hτeq]
    exact hq.symm

/-- **Hatcher §4.1 Exercise 9(a), at the term `π₀(A, x₀)`.**  A map of pairs whose four
surrounding maps in the sequence of the pair are bijections at every basepoint induces a
bijection `π₀(A) → π₀(B)`.

The four surrounding maps of the `π₀(A, x₀)` term are `π₁(X, A, a) → π₁(Y, B, f a)`,
`π₁(X, a) → π₁(Y, f a)`, `π₀(X) → π₀(Y)` and `π₀(X, A, x₀) → π₀(Y, B, f x₀)`, the first two
for all `a ∈ A`.

Source: Hatcher, *Algebraic Topology*, §4.1 Exercise 9(a) (printed p. 358). -/
theorem zerothHomotopySubtypeMap_bijective {A : Set X} {B : Set Y} (f : C(X, Y))
    (hAB : ∀ x ∈ A, f x ∈ B) {x₀ : X} (hx₀ : x₀ ∈ A)
    (hA : ∀ a : A, Function.Bijective (map (x₀ := (a : X)) f hAB))
    (hX : ∀ a : A, Function.Bijective (fundamentalGroupMap f (x₀ := (a : X))))
    (hX₀ : Function.Bijective (zerothHomotopyMap f))
    (hQ : Function.Bijective (PairZerothHomotopy.map (B := B) f hAB)) :
    Function.Bijective (zerothHomotopyMap (restrictMap f hAB)) := by
  refine ⟨?_, ?_⟩
  · rintro p q hpq
    revert hpq
    refine Quotient.inductionOn p (fun a => ?_)
    refine Quotient.inductionOn q (fun a' => ?_)
    intro hpq
    have hpq' : ZerothHomotopy.mk (⟨f a, hAB a a.2⟩ : B) =
        ZerothHomotopy.mk (⟨f a', hAB a' a'.2⟩ : B) := hpq
    obtain ⟨η⟩ := Quotient.exact hpq'
    -- the two points lie in the same component of `X`
    have hX0inj : ZerothHomotopy.mk (a : X) = ZerothHomotopy.mk (a' : X) := by
      refine hX₀.injective ?_
      exact ZerothHomotopy.sound (η.map continuous_subtype_val)
    set σ : Path.Homotopic.Quotient (a : X) (a' : X) :=
      Path.Homotopic.Quotient.mk (Quotient.exact hX0inj).somePath with hσdef
    set ηc : Path.Homotopic.Quotient (f a) (f a') :=
      Path.Homotopic.Quotient.mk (η.map continuous_subtype_val) with hηcdef
    -- adjust the path in `X` so that it maps to the joining path in `B`
    obtain ⟨lam, hlam⟩ := (hX a).surjective (ηc.trans (σ.map f).symm)
    have hlam' : lam.map f = ηc.trans (σ.map f).symm := hlam
    have hσ' : (lam.trans σ).map f = ηc := by
      rw [pathClassMap_trans, hlam', Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
    -- the two relative classes at the basepoint `a`
    have hmap : map (x₀ := (a : X)) f hAB
        (mk ⟨a, a.2⟩ (Path.Homotopic.Quotient.refl (a : X))) =
        map (x₀ := (a : X)) f hAB (mk ⟨a', a'.2⟩ (lam.trans σ).symm) := by
      rw [map_mk, map_mk]
      refine (mk_eq_mk_iff (x₀ := f (a : X))).2 ⟨η, ?_⟩
      rw [pathClassMap_symm, hσ', hηcdef, subspacePathClass_mk, pathClassMap_refl,
        Path.Homotopic.Quotient.trans_symm]
    have huw := (hA a).injective hmap
    have := congrArg (boundary (A := A) (x₀ := (a : X))) huw
    exact this
  · intro b
    refine Quotient.inductionOn b (fun b => ?_)
    -- a point of `X` mapping into the component of `b`
    obtain ⟨c, hc⟩ := hX₀.surjective (ZerothHomotopy.mk (b : Y))
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    have hx : ZerothHomotopy.mk (f x) = ZerothHomotopy.mk (b : Y) := hc
    -- the component of `x` is already met by `A`
    have hcls : PairZerothHomotopy.mk (A := A) (ZerothHomotopy.mk x) =
        PairZerothHomotopy.mk (A := A) (ZerothHomotopy.mk x₀) := by
      refine hQ.injective ?_
      rw [PairZerothHomotopy.map_mk, PairZerothHomotopy.map_mk]
      refine PairZerothHomotopy.mk_eq_mk_of_mem ?_ ?_
      · exact ⟨b, hx.symm⟩
      · exact inSubspace_mk_of_mem (hAB x₀ hx₀)
    obtain ⟨a, ha⟩ := (PairZerothHomotopy.mk_eq_mk_base_iff hx₀ _).1 hcls
    -- a path in `Y` from `b` to `f a`
    have hbx : Joined (f x) (b : Y) := Quotient.exact hx
    have hax : Joined (a : X) x := Quotient.exact ha
    have hba : Joined (b : Y) (f a) := hbx.symm.trans (hax.map f.continuous).symm
    -- its relative class is hit by the map of pairs, and `∂` of the preimage is the answer
    obtain ⟨v, hv⟩ := (hA a).surjective
      (mk (x₀ := f (a : X)) b (Path.Homotopic.Quotient.mk hba.somePath))
    obtain ⟨a', ha'⟩ := ZerothHomotopy.mk_surjective (boundary (A := A) (x₀ := (a : X)) v)
    refine ⟨ZerothHomotopy.mk a', ?_⟩
    have hb1 : boundary (A := B) (x₀ := f (a : X)) (map (x₀ := (a : X)) f hAB v) =
        boundary (A := B) (x₀ := f (a : X))
          (mk (x₀ := f (a : X)) b (Path.Homotopic.Quotient.mk hba.somePath)) := by
      rw [hv]
    rw [boundary_map, boundary_mk, ← ha'] at hb1
    exact hb1

end LeanCategories.Topology
