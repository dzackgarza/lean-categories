/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-!
# Local models of complex analytic spaces

An analytic subset of an open `U ⊆ ℂⁿ` is the common zero locus in `U` of finitely many functions
analytic on a neighbourhood of `U`. This file gives the local model of a reduced complex analytic
space concretely: charts onto analytic subsets, the germ ring at a point (functions that extend
holomorphically near the point, modulo those vanishing near it on the subset), normality
(integrally closed germ ring), germ dimension (Krull dimension of the germ ring) and the
Baily–Borel dimension stratification `V_(d)` with its admissibility hypothesis.

Provenance: migrated from `dzackgarza/research`,
`computations/scripts/sterk-enriques-cusps/lean/Atoms.lean` (sections `AnalyticSets`,
`Normality`, `DimensionStratification`; Sterk graph nodes AF10, AF14, AF17–AF19), unchanged
in content.

LC-12. *Needed*: reduced complex analytic spaces as locally ringed spaces locally isomorphic to
`(Z, (𝒪_U / ℐ_Z)|_Z)`. *Searched*: the formalization corpus ("analytic subset zero locus germ
ring normal complex analytic space") and Mathlib; there is no sheaf of holomorphic functions
on `ℂⁿ` as a sheaf of rings and no analytic space. *Did instead*: pointwise germ rings of
functions that extend holomorphically, with charts as homeomorphisms onto analytic subsets;
this records no transition-map condition, so `IsLocallyAnalyticSpace` is weaker than being an
analytic space. *Optimal*: the structure sheaf `𝒪_Z` as a sheaf of local rings, a complex
analytic space as a `LocallyRingedSpace` locally isomorphic to the model, and `germRing` as the
stalk. *Tracked*: TODO(LC-12) below and COMPLAINTS ("Complex analytic spaces").
-/

namespace LeanCategories.Analytic

universe u

variable {n : ℕ}

/-- **AF10, the local model.**  An *analytic subset* of an open set `U` in `ℂⁿ`:
the common zero locus in `U` of finitely many functions analytic on a
neighbourhood of `U`.

This is the object a reduced analytic space is locally isomorphic to, and the
reason AF10's chain does not need a sheaf quotient: the local model can be given
as a zero locus, with the structure sheaf described concretely below as the
functions that extend holomorphically. -/
def IsAnalyticSubset (U Z : Set (Fin n → ℂ)) : Prop :=
  IsOpen U ∧ ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
    (∀ j, AnalyticOnNhd ℂ (f j) U) ∧ Z = U ∩ {z | ∀ j, f j z = 0}

/-- An analytic subset is closed in its ambient open set. -/
theorem IsAnalyticSubset.subset {U Z : Set (Fin n → ℂ)} (h : IsAnalyticSubset U Z) :
    Z ⊆ U := by
  obtain ⟨-, m, f, -, rfl⟩ := h
  exact Set.inter_subset_left

/-- The whole open set is an analytic subset of itself, cut out by no equations. -/
theorem isAnalyticSubset_self {U : Set (Fin n → ℂ)} (hU : IsOpen U) :
    IsAnalyticSubset U U := by
  refine ⟨hU, 0, Fin.elim0, fun j => j.elim0, ?_⟩
  ext z
  simp

/-- **AF10, the structure sheaf, concretely.**  A function on an analytic subset
is *holomorphic at a point* when it agrees near that point with a function
analytic on a neighbourhood in the ambient space.

Stating the structure sheaf this way — as functions that extend, rather than as a
quotient of the ambient sheaf by an ideal sheaf — is what keeps the definition
inside what the pinned Mathlib supplies. -/
def HolomorphicAtOnSubset (Z : Set (Fin n → ℂ)) (g : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) : Prop :=
  ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ∃ G : (Fin n → ℂ) → ℂ,
    AnalyticOnNhd ℂ G V ∧ ∀ w ∈ Z ∩ V, g w = G w

/-- A function analytic on an ambient neighbourhood is holomorphic on the subset. -/
theorem holomorphicAtOnSubset_of_analyticOnNhd {Z V : Set (Fin n → ℂ)}
    (hV : IsOpen V) {z : Fin n → ℂ} (hz : z ∈ V) {G : (Fin n → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G V) : HolomorphicAtOnSubset Z G z :=
  ⟨V, hV, hz, G, hG, fun _ _ => rfl⟩

/-- **AF10, the space.**  A *local model chart* on a topological space: a
homeomorphism of an open set of the space onto an analytic subset of an open set
of some `ℂⁿ`. -/
structure AnalyticChart (X : Type u) [TopologicalSpace X] where
  /-- The dimension of the ambient space of the model. -/
  ambientDim : ℕ
  /-- The open set of `X` the chart is defined on. -/
  source : Set X
  /-- The ambient open set of the model. -/
  ambient : Set (Fin ambientDim → ℂ)
  /-- The analytic subset the chart lands in. -/
  model : Set (Fin ambientDim → ℂ)
  source_open : IsOpen source
  model_analytic : IsAnalyticSubset ambient model
  /-- The chart itself, a homeomorphism onto the model. -/
  toHomeomorph : source ≃ₜ model

/-- **AF10.**  A space is *locally analytic* when its points are covered by local
model charts.  With `IsIrreducible` from `Mathlib/Topology/Irreducible.lean` this
gives "irreducible analytic space"; **normality is what remains** — it is a
condition on the local ring at a point, so it needs the structure sheaf as a
sheaf of rings rather than the pointwise predicate above, and that is the one
piece of AF10 still unwritten. -/
def IsLocallyAnalyticSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ c : AnalyticChart X, x ∈ c.source


/-- **AF10, the local ring.**  The functions holomorphic at `z` on `Z` form a
subring of all `ℂ`-valued functions: sums and products of functions that extend
holomorphically extend holomorphically, on the intersection of the two
neighbourhoods. -/
def holomorphicSubring (Z : Set (Fin n → ℂ)) (z : Fin n → ℂ) :
    Subring ((Fin n → ℂ) → ℂ) where
  carrier := {g | HolomorphicAtOnSubset Z g z}
  one_mem' := ⟨Set.univ, isOpen_univ, Set.mem_univ z, 1, analyticOnNhd_const, fun _ _ => rfl⟩
  zero_mem' := ⟨Set.univ, isOpen_univ, Set.mem_univ z, 0, analyticOnNhd_const, fun _ _ => rfl⟩
  add_mem' := by
    rintro g h ⟨V, hV, hzV, G, hG, hgG⟩ ⟨W, hW, hzW, H, hH, hhH⟩
    refine ⟨V ∩ W, hV.inter hW, ⟨hzV, hzW⟩, G + H,
      (hG.mono Set.inter_subset_left).add (hH.mono Set.inter_subset_right), ?_⟩
    rintro w ⟨hwZ, hwV, hwW⟩
    simp only [Pi.add_apply]
    rw [hgG w ⟨hwZ, hwV⟩, hhH w ⟨hwZ, hwW⟩]
  neg_mem' := by
    rintro g ⟨V, hV, hzV, G, hG, hgG⟩
    refine ⟨V, hV, hzV, -G, hG.neg, ?_⟩
    intro w hw
    simp only [Pi.neg_apply]
    rw [hgG w hw]
  mul_mem' := by
    rintro g h ⟨V, hV, hzV, G, hG, hgG⟩ ⟨W, hW, hzW, H, hH, hhH⟩
    refine ⟨V ∩ W, hV.inter hW, ⟨hzV, hzW⟩, G * H,
      (hG.mono Set.inter_subset_left).mul (hH.mono Set.inter_subset_right), ?_⟩
    rintro w ⟨hwZ, hwV, hwW⟩
    simp only [Pi.mul_apply]
    rw [hgG w ⟨hwZ, hwV⟩, hhH w ⟨hwZ, hwW⟩]

/-- **AF10, the local ring.**  The functions vanishing on a neighbourhood of `z`
in `Z` form an ideal of the above.  Quotienting by it is what makes germs germs,
and it replaces the sheafification a sheaf-theoretic construction would need. -/
def vanishingIdeal (Z : Set (Fin n → ℂ)) (z : Fin n → ℂ) :
    Ideal (holomorphicSubring Z z) where
  carrier := {g | ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧
    ∀ w ∈ Z ∩ V, (g : (Fin n → ℂ) → ℂ) w = 0}
  zero_mem' := ⟨Set.univ, isOpen_univ, Set.mem_univ z, fun _ _ => rfl⟩
  add_mem' := by
    rintro g h ⟨V, hV, hzV, hg⟩ ⟨W, hW, hzW, hh⟩
    refine ⟨V ∩ W, hV.inter hW, ⟨hzV, hzW⟩, ?_⟩
    rintro w ⟨hwZ, hwV, hwW⟩
    have : ((g + h : holomorphicSubring Z z) : (Fin n → ℂ) → ℂ) w
        = (g : (Fin n → ℂ) → ℂ) w + (h : (Fin n → ℂ) → ℂ) w := rfl
    rw [this, hg w ⟨hwZ, hwV⟩, hh w ⟨hwZ, hwW⟩, add_zero]
  smul_mem' := by
    rintro r g ⟨V, hV, hzV, hg⟩
    refine ⟨V, hV, hzV, ?_⟩
    intro w hw
    have : ((r • g : holomorphicSubring Z z) : (Fin n → ℂ) → ℂ) w
        = (r : (Fin n → ℂ) → ℂ) w * (g : (Fin n → ℂ) → ℂ) w := rfl
    rw [this, hg w hw, mul_zero]

/-- **AF10.**  The local ring of germs at a point of an analytic subset. -/
abbrev germRing (Z : Set (Fin n → ℂ)) (z : Fin n → ℂ) : Type :=
  (holomorphicSubring Z z) ⧸ (vanishingIdeal Z z)

/-- **AF10, normality.**  An analytic subset is *normal at a point* when its germ
ring there is integrally closed.

The domain hypothesis is an instance argument, which is the setting AF10 uses: it
speaks of *irreducible* normal analytic spaces, and irreducibility of the germ is
what makes the germ ring a domain. -/
def IsNormalAtPoint (Z : Set (Fin n → ℂ)) (z : Fin n → ℂ)
    [IsDomain (germRing Z z)] : Prop :=
  IsIntegrallyClosed (germRing Z z)


/-- **AF10, the dimension of a germ.**  The dimension of an analytic subset at a
point is the Krull dimension of its germ ring.

`ringKrullDim` is `Order.krullDim` of the prime spectrum, so the dimension
function AF10's stratification is indexed by needs no new notion. -/
noncomputable def germDim (Z : Set (Fin n → ℂ)) (z : Fin n → ℂ) : WithBot ℕ∞ :=
  ringKrullDim (germRing Z z)

/-- **AF10, the stratification.**  The `d`-th stratum: the points of `Z` whose
germ has dimension at most `d`.  This is Baily–Borel's `V_(d)`. -/
def dimStratum (Z : Set (Fin n → ℂ)) (d : ℕ) : Set (Fin n → ℂ) :=
  {z ∈ Z | germDim Z z ≤ (d : WithBot ℕ∞)}

/-- The points where the germ has dimension exactly `d`. -/
def dimStratumExact (Z : Set (Fin n → ℂ)) (d : ℕ) : Set (Fin n → ℂ) :=
  {z ∈ Z | germDim Z z = (d : WithBot ℕ∞)}

theorem dimStratum_subset (Z : Set (Fin n → ℂ)) (d : ℕ) : dimStratum Z d ⊆ Z :=
  fun _ hz => hz.1

theorem dimStratum_mono (Z : Set (Fin n → ℂ)) {d e : ℕ} (h : d ≤ e) :
    dimStratum Z d ⊆ dimStratum Z e := by
  rintro z ⟨hzZ, hzd⟩
  refine ⟨hzZ, hzd.trans ?_⟩
  exact_mod_cast WithBot.coe_le_coe.mpr (by exact_mod_cast Nat.cast_le.mpr h)

/-- **AF10, condition (i).**  Baily–Borel's first hypothesis on the
stratification: every stratum is closed, and the top-dimensional part is dense of
full dimension.

This is a **hypothesis** of Theorem 9.2, not a conclusion, so what AF10 needed
from this graph was the ability to *state* it — which needed the dimension
function and the strata, and now has both. -/
structure StratificationAdmissible (Z : Set (Fin n → ℂ)) (top : ℕ) : Prop where
  /-- Each stratum is closed in the ambient space. -/
  stratum_closed : ∀ d : ℕ, IsClosed (dimStratum Z d)
  /-- The top-dimensional part is dense in the subset. -/
  top_dense : closure (dimStratumExact Z top) ⊇ Z
  /-- The top dimension is attained. -/
  top_attained : (dimStratumExact Z top).Nonempty

-- TODO(LC-12): the structure sheaf of an analytic subset as a sheaf of local rings, analytic
-- spaces as locally ringed spaces locally isomorphic to it, and `germRing` as its stalk.

end LeanCategories.Analytic
