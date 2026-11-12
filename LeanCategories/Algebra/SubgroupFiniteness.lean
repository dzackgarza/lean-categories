/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Generators
public import Mathlib.Data.Fintype.EquivFin

/-!
# Finitely many subgroups of a given finite index

Card `E-HAT-1.A-8` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 1.A, exercise 8 — "a finitely generated group has only a
finite number of subgroups of a given finite index" — as checked on the card
(new-qual-site `corpus/collections/SRC-TEXT-HAT02/1-a/E-HAT-1.A-8.md`).
Certificate: new-qual-site `proofs/cards/SubgroupFiniteness.lean` at main
`16c09abaa4`.

The card's proof encodes a based connected n-sheeted cover of a rose by the
monodromy permutations of a labelled n-point fibre.  Algebraically, that is the
coset action of the group on `G ⧸ H`, and the two ingredients are:

* a homomorphism out of a group with a finite generating family into a fixed
  finite group is determined by its values on the generators, so there are only
  finitely many of them (`finite_hom`);

* a subgroup of index `m` is the stabilizer of the coset of `1` under its own
  coset action transported to `Fin m` (`subgroup_eq_stabilizer_comap`).

Hence the subgroups of index `m` form the image of a finite set.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): `finite_hom` (corpus: 55 files, generic name matches only),
"finitely many subgroups finite index" (corpus: 39 files, generic; Mathlib's
`GroupTheory/Index.lean` covers index arithmetic, not this finiteness statement),
`subgroup_eq_stabilizer_comap` (corpus: 0 hits).  Route: written — the
coset-action stabilization is the card's own argument, certified here as the
settled proof.
-/

set_option linter.style.haveILetI false

namespace LeanCategories.Algebra.SubgroupFiniteness

open MulAction

/-- Conjugation of permutations by an equivalence. -/
def permCongr {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toFun f := e.symm.trans (f.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' f g := by ext x; simp [Equiv.Perm.mul_apply]

@[simp]
theorem permCongr_apply {α β : Type*} (e : α ≃ β) (f : Equiv.Perm α) (x : β) :
    permCongr e f x = e (f (e.symm x)) := rfl

/-- Homomorphisms from a group with a finite generating family into a finite monoid
form a finite set. -/
theorem finite_hom {G : Type*} [Group G] {ι : Type*} [Finite ι]
    (P : Group.Generators G ι) (M : Type*) [Monoid M] [Finite M] :
    (Set.univ : Set (G →* M)).Finite := by
  have inj : Function.Injective (fun (φ : G →* M) => fun (i : ι) => φ (P.val i)) := by
    intro φ ψ h
    exact P.hom_ext φ ψ (fun i => congrFun h i)
  haveI : Finite (G →* M) := Finite.of_injective _ inj
  exact Set.finite_univ

/-- A subgroup of index `m ≠ 0` is the stabilizer of a point under a homomorphism into
`Equiv.Perm (Fin m)`: its own coset action, transported to `Fin m`. -/
theorem subgroup_eq_stabilizer_comap {G : Type*} [Group G] {H : Subgroup G} {m : ℕ}
    (hm : H.index = m) (hm0 : m ≠ 0) :
    ∃ (φ : G →* Equiv.Perm (Fin m)) (i : Fin m),
      H = (MulAction.stabilizer (Equiv.Perm (Fin m)) i).comap φ := by
  classical
  have hcard0 : Nat.card (G ⧸ H) ≠ 0 := by
    rw [← Subgroup.index_eq_card, hm]; exact hm0
  haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero hcard0
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ H) = m := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hm]
  let e : G ⧸ H ≃ Fin m := Fintype.equivFinOfCardEq hcard
  let φ : G →* Equiv.Perm (Fin m) :=
    (permCongr e).toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  let i : Fin m := e ((1 : G) : G ⧸ H)
  refine ⟨φ, i, ?_⟩
  have hact : ∀ g : G, φ g i = e (g • ((1 : G) : G ⧸ H)) := by
    intro g
    simp [φ, i, permCongr_apply, MulAction.toPermHom_apply]
  have hmem : ∀ g : G, (g ∈ H ↔ g • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)) := by
    intro g
    rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  ext g
  have hsmul : φ g • i = φ g i := by simp
  simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    have h1 : g • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := (hmem g).mp hg
    show φ g • i = i
    rw [hsmul, hact, h1]
  · intro hg
    apply (hmem g).mpr
    have h2 : e (g • ((1 : G) : G ⧸ H)) = e ((1 : G) : G ⧸ H) := by
      rw [← hact, ← hsmul]
      exact hg
    exact e.injective h2

/-- A finitely generated group has only finitely many subgroups of a given nonzero index. -/
theorem finite_subgroups_of_index {G : Type*} [Group G] (hG : Group.FG G) {m : ℕ}
    (hm0 : m ≠ 0) : {H : Subgroup G | H.index = m}.Finite := by
  classical
  obtain ⟨n, ⟨P⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp hG
  haveI : Finite (G →* Equiv.Perm (Fin m)) := by
    refine Finite.of_injective (fun (φ : G →* Equiv.Perm (Fin m)) => fun (i : Fin n) => φ (P.val i)) ?_
    intro φ ψ h
    exact P.hom_ext φ ψ (fun i => congrFun h i)
  set F : (G →* Equiv.Perm (Fin m)) × Fin m → Subgroup G :=
    fun p => (MulAction.stabilizer (Equiv.Perm (Fin m)) p.2).comap p.1 with hF
  have himg : (Set.univ.image F).Finite := Set.finite_univ.image F
  refine himg.subset ?_
  intro H hH
  have hindex : H.index = m := hH
  obtain ⟨φ, i, hφ⟩ := subgroup_eq_stabilizer_comap hindex hm0
  refine ⟨(φ, i), Set.mem_univ _, ?_⟩
  rw [hφ]

end LeanCategories.Algebra.SubgroupFiniteness
