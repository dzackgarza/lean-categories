/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.Group

/-!
# Nonabelian first-cohomology data

Definition-level realization of Serre FC10-C07-U039.

Only the source's raw data are recorded here: fixed points, the crossed-cocycle
predicate, the cohomology relation, and the unit representative. Packaging the
relation as a setoid/quotient and installing the distinguished point requires
proofs that the relation is an equivalence and that the unit function is a
cocycle, so those steps are intentionally outside Sweep III.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable (G : Type u) (A : Type v)
variable [Group G] [Group A] [MulDistribMulAction G A]

/-- Serre's nonabelian degree-zero cohomology data: the fixed-point locus
`A^G` (FC10-C07-U039). -/
def serreNonabelianH0Data : Set A :=
  MulAction.fixedPoints G A

/-- Serre's multiplicative crossed-cocycle predicate
`a_(st) = a_s * s(a_t)` (FC10-C07-U039). -/
def serreIsNonabelianOneCocycleData (f : G → A) : Prop :=
  ∀ s t : G, f (s * t) = f s * (s • f t)

/-- Serre's cohomology relation on raw one-cocycle functions
`b_s = a⁻¹ a_s s(a)` (FC10-C07-U039).

Whether this relation is reflexive, symmetric, and transitive on the cocycle
locus is result content and is not bundled here. -/
def serreNonabelianCohomologousData (f g : G → A) : Prop :=
  ∃ a : A, ∀ s : G, g s = a⁻¹ * f s * (s • a)

/-- The unit-function representative used for the distinguished class in
Serre's nonabelian `H¹` (FC10-C07-U039).

The fact that it satisfies the cocycle predicate is deliberately not proved or
stored in this Sweep-III datum. -/
def serreNonabelianUnitCocycleData : G → A :=
  fun _ => 1

def SerreNonabelianOneCocycle : Type _ :=
  {f : G → A // serreIsNonabelianOneCocycleData G A f}

namespace SerreNonabelianOneCocycle

instance : CoeFun (SerreNonabelianOneCocycle G A) (fun _ => G → A) :=
  ⟨fun f => f.1⟩

instance : One (SerreNonabelianOneCocycle G A) :=
  ⟨⟨serreNonabelianUnitCocycleData G A, by
    intro s t
    simp [serreNonabelianUnitCocycleData, MulDistribMulAction.smul_one]⟩⟩

def cohomologySetoid : Setoid (SerreNonabelianOneCocycle G A) where
  r f g := serreNonabelianCohomologousData G A f.1 g.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      refine ⟨1, ?_⟩
      intro s
      simp [MulDistribMulAction.smul_one]
    · intro f g h
      rcases h with ⟨a, ha⟩
      refine ⟨a⁻¹, ?_⟩
      intro s
      have hinv : s • a⁻¹ = (s • a)⁻¹ := by
        simpa only [MulDistribMulAction.toMonoidHom_apply] using
          map_inv (MulDistribMulAction.toMonoidHom A s) a
      rw [hinv, ha s]
      group
    · intro f g h hfg hgh
      rcases hfg with ⟨a, ha⟩
      rcases hgh with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      intro s
      rw [hb s, ha s]
      rw [smul_mul']
      group

end SerreNonabelianOneCocycle

def SerreNonabelianH1 : Type _ :=
  Quotient (SerreNonabelianOneCocycle.cohomologySetoid G A)

namespace SerreNonabelianH1

def mk (z : SerreNonabelianOneCocycle G A) : SerreNonabelianH1 G A := ⟦z⟧

instance : One (SerreNonabelianH1 G A) := ⟨mk G A 1⟩

lemma mk_eq_iff (x y : SerreNonabelianOneCocycle G A) :
    mk G A x = mk G A y ↔
      serreNonabelianCohomologousData G A x.1 y.1 :=
  Quotient.eq_iff_equiv

end SerreNonabelianH1

def SerreNonabelianH0 : Type _ :=
  {a : A // ∀ g : G, g • a = a}

structure SerreNonabelianExactSequenceData
    (B C : Type*) [Group B] [Group C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] where
  i : A →* B
  p : B →* C
  i_equivariant : ∀ g : G, ∀ a : A, i (g • a) = g • i a
  p_equivariant : ∀ g : G, ∀ b : B, p (g • b) = g • p b
  i_injective : Function.Injective i
  p_surjective : Function.Surjective p
  exact : ∀ b : B, p b = 1 ↔ ∃ a : A, i a = b

namespace SerreNonabelianExactSequenceData

variable {B C : Type*} [Group B] [Group C]
variable [MulDistribMulAction G B] [MulDistribMulAction G C]

lemma boundary_mem_kernel
    (E : SerreNonabelianExactSequenceData G A B C)
    (c : SerreNonabelianH0 G C) (b : B) (hb : E.p b = c.1) (s : G) :
    E.p (b⁻¹ * (s • b)) = 1 := by
  rw [map_mul, map_inv, E.p_equivariant s b, hb, c.2 s]
  group

noncomputable def connectingBoundaryLift
    (E : SerreNonabelianExactSequenceData G A B C)
    (c : SerreNonabelianH0 G C) (b : B) (hb : E.p b = c.1)
    (s : G) : A :=
  Classical.choose ((E.exact _).mp
    (boundary_mem_kernel (G := G) (A := A) E c b hb s))

@[simp]
lemma i_connectingBoundaryLift
    (E : SerreNonabelianExactSequenceData G A B C)
    (c : SerreNonabelianH0 G C) (b : B) (hb : E.p b = c.1)
    (s : G) :
    E.i (connectingBoundaryLift (G := G) (A := A) E c b hb s) = b⁻¹ * (s • b) :=
  Classical.choose_spec ((E.exact _).mp
    (boundary_mem_kernel (G := G) (A := A) E c b hb s))

noncomputable def connectingCocycle
    (E : SerreNonabelianExactSequenceData G A B C)
    (c : SerreNonabelianH0 G C) (b : B) (hb : E.p b = c.1) :
    SerreNonabelianOneCocycle G A :=
  ⟨fun s => connectingBoundaryLift (G := G) (A := A) E c b hb s, by
    intro s t
    apply E.i_injective
    rw [map_mul, E.i_equivariant,
      i_connectingBoundaryLift (G := G) (A := A) E,
      i_connectingBoundaryLift (G := G) (A := A) E,
      i_connectingBoundaryLift (G := G) (A := A) E]
    have hinv : s • b⁻¹ = (s • b)⁻¹ := by
      simpa only [MulDistribMulAction.toMonoidHom_apply] using
        map_inv (MulDistribMulAction.toMonoidHom B s) b
    rw [smul_mul', hinv, mul_smul]
    group⟩

noncomputable def fixedPointLift
    (E : SerreNonabelianExactSequenceData G A B C)
    (c : SerreNonabelianH0 G C) : B :=
  Classical.choose (E.p_surjective c.1)

@[simp]
lemma p_fixedPointLift
    (E : SerreNonabelianExactSequenceData G A B C)
    (c : SerreNonabelianH0 G C) :
    E.p (fixedPointLift (G := G) (A := A) E c) = c.1 :=
  Classical.choose_spec (E.p_surjective c.1)

noncomputable def connecting
    (E : SerreNonabelianExactSequenceData G A B C) :
    SerreNonabelianH0 G C → SerreNonabelianH1 G A :=
  fun c =>
    SerreNonabelianH1.mk G A
      (connectingCocycle (G := G) (A := A) E c
        (fixedPointLift (G := G) (A := A) E c)
        (p_fixedPointLift (G := G) (A := A) E c))

end SerreNonabelianExactSequenceData

/-- Raw degree-zero functoriality data for a homomorphism of coefficient
groups (FC10-C07-U040).

Restricting this function to fixed-point loci requires equivariance of f;
that preservation statement is result content. -/
def serreNonabelianH0MapData {B : Type*} [Group B] (f : A →* B) : A → B :=
  f

/-- Raw pointwise map on nonabelian one-cocycle functions
(FC10-C07-U040).

For an equivariant homomorphism f, proving that this sends cocycles to
cocycles, respects Serre's cohomology relation, and descends to the pointed
quotient is result content. -/
def serreNonabelianH1CocycleMapData {B : Type*} [Group B]
    (f : A →* B) (c : G → A) : G → B :=
  fun s => f (c s)

/-- The ambient B-valued boundary associated to a chosen lift b in a
nonabelian extension (FC10-C07-U044), namely s ↦ b⁻¹ * s • b.

The source's exact-sequence hypotheses imply that these values lie in the
embedded kernel A, form a cocycle there, and determine a lift-independent
class in H¹(G,A). Those implications are result content. -/
def serreNonabelianConnectingAmbientData {B : Type*} [Group B]
    [MulDistribMulAction G B] (b : B) : G → B :=
  fun s => b⁻¹ * (s • b)

/-- Raw predicate selecting an A-valued lift of Serre's ambient connecting
boundary through a supplied inclusion A → B (FC10-C07-U044).

Existence and independence of such a lift are not construction fields. -/
def serreIsNonabelianConnectingLiftData {B : Type*} [Group B]
    [MulDistribMulAction G B] (i : A →* B) (b : B) (a : G → A) : Prop :=
  ∀ s : G, i (a s) = serreNonabelianConnectingAmbientData G b s

/-- The ambient B-valued factor set associated to chosen lifts of a
nonabelian one-cocycle (FC10-C07-U045):
  (s,t) ↦ b_s * s(b_t) * b_(st)⁻¹.

Under Serre's central exact-extension hypotheses these values lie in the
embedded subgroup A and define an abelian two-cocycle there. Those statements
are result content. -/
def serreNonabelianConnectingTwoAmbientData {B : Type*} [Group B]
    [MulDistribMulAction G B] (b : G → B) : G → G → B :=
  fun s t => b s * (s • b t) * (b (s * t))⁻¹

/-- Raw predicate selecting an A-valued lift of the ambient factor set through
the supplied inclusion A → B (FC10-C07-U045).

Existence, the two-cocycle equation, independence of the chosen lifts, and
descent to H²(G,A) remain theorem-layer obligations. -/
def serreIsNonabelianConnectingTwoLiftData {B : Type*} [Group B]
    [MulDistribMulAction G B] (i : A →* B) (b : G → B)
    (a : G → G → A) : Prop :=
  ∀ s t : G, i (a s t) = serreNonabelianConnectingTwoAmbientData G b s t

end LeanCategories.Homological
