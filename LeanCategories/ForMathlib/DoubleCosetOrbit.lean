/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Double cosets as orbits, and the inversion equivalence of double-coset spaces

For subgroups `H` and `K` of a group `G`:

* inversion is an anti-automorphism, so it carries the double coset `K g H` onto `H g⁻¹ K` and
  induces an equivalence `K \ G / H ≃ H \ G / K` (`DoubleCoset.quotientInvEquiv`);
* `x ∈ K g H` exactly when the class of `x` in `G ⧸ H` lies in the `K`-orbit of the class of `g`
  (`DoubleCoset.mem_doubleCoset_iff_mk_mem_orbit`);
* for any `G`-set `α`, a point `p` and `K ≤ G`, two translates `x • p` and `y • p` lie in one
  `K`-orbit exactly when `x` and `y` lie in one double coset of `K` and the stabilizer of `p`
  (`DoubleCoset.orbitRel_smul_iff_mem_doubleCoset_stabilizer`), so the `K`-orbits inside the
  `G`-orbit of `p` are the double cosets `K \ G / Stab_G(p)`
  (`DoubleCoset.orbitRelQuotientEquivDoubleCoset`).

From these: a finite-index subgroup has finitely many orbits on a pretransitive `G`-set, at most
its index in `G` (`DoubleCoset.finite_orbitRelQuotient_of_finiteIndex`,
`DoubleCoset.natCard_orbitRelQuotient_le_index`), and a double-coset space `K \ G / H` with `K` of
finite index is finite with at most `[G : K]` elements
(`DoubleCoset.finite_quotient_of_finiteIndex`, `DoubleCoset.natCard_quotient_le_index`).

## Search record (LC-09)

`scripts/formalization_corpus.py search` at the manifest head `6d97e8ad`, under the formulations
`DoubleCoset.Quotient`, `double coset inversion`, `orbitRelQuotient double coset equivalence` and
`point stabilizer Schreier transversal`. Hits used: TauCeti `GroupTheory/DoubleCoset/Inv.lean` and
`.../Orbits.lean` (ported, above). Hits inspected and not used: `yawara/odd-order`
`GroupTheory/HallWielandt.lean` (Mackey's double-coset sum for indices), `Vilin97/lean-pool`
`LeanPool/Kurosh/Kurosh.lean` (double cosets of free-product factors). `orbitRelQuotient double
coset equivalence` returned no files; Mathlib's `Mathlib/GroupTheory/DoubleCoset.lean` was read
directly and has the setoid and `DoubleCoset.eq` but neither the inversion nor the orbit dictionary.

The set identity for inversion, the membership criterion and the relation
`orbitRel_smul_iff_mem_doubleCoset_stabilizer` are ported from TauCeti
(`https://github.com/TauCetiProject/TauCeti`, commit `7b4d5f7`, Apache 2.0,
`TauCeti/GroupTheory/DoubleCoset/Inv.lean`, `TauCeti/GroupTheory/DoubleCoset/Orbits.lean`);
the equivalences of quotient types, the orbit-set form and the cardinality bounds are this
repository's glue. Mathlib's `Mathlib/GroupTheory/DoubleCoset.lean` supplies the setoid,
`DoubleCoset.mk`, `DoubleCoset.eq` and `DoubleCoset.rel_iff`, and has neither the inversion nor the
orbit dictionary.
-/

@[expose] public section

open MulAction
open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-! ## Inversion exchanges the two flanking subgroups -/

/-- **Inverting a double coset exchanges its flanking subgroups.** As sets,
`(K g H)⁻¹ = H g⁻¹ K`. -/
@[simp]
lemma doubleCoset_inv (H K : Subgroup G) (g : G) :
    (doubleCoset g (K : Set G) (H : Set G))⁻¹ = doubleCoset g⁻¹ (H : Set G) (K : Set G) := by
  rw [doubleCoset, doubleCoset, mul_inv_rev, mul_inv_rev, Set.inv_singleton, inv_coe_set,
    inv_coe_set, ← mul_assoc]

/-- **Inverting a double coset exchanges its flanking subgroups**: `x⁻¹ ∈ H g⁻¹ K` if and only if
`x ∈ K g H`. The membership form of `doubleCoset_inv`. -/
lemma inv_mem_doubleCoset_inv_iff {H K : Subgroup G} {g x : G} :
    x⁻¹ ∈ doubleCoset g⁻¹ (H : Set G) (K : Set G) ↔ x ∈ doubleCoset g (K : Set G) (H : Set G) := by
  rw [← doubleCoset_inv, Set.mem_inv, inv_inv]

/-- **The inversion equivalence of double-coset spaces.** Inversion carries `K \ G / H` to
`H \ G / K`; the two flanking subgroups are exchanged. -/
noncomputable def quotientInvEquiv (H K : Subgroup G) :
    Quotient (H : Set G) K ≃ Quotient (K : Set G) H where
  toFun := Quotient.map (· ⁻¹) fun _ _ hab => by
    obtain ⟨h, hh, k, hk, rfl⟩ := (rel_iff (H := H) (K := K)).mp hab
    exact (rel_iff (H := K) (K := H)).mpr ⟨k⁻¹, K.inv_mem hk, h⁻¹, H.inv_mem hh, by group⟩
  invFun := Quotient.map (· ⁻¹) fun _ _ hab => by
    obtain ⟨k, hk, h, hh, rfl⟩ := (rel_iff (H := K) (K := H)).mp hab
    exact (rel_iff (H := H) (K := K)).mpr ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, by group⟩
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ g =>
      simp only [Quotient.map_mk, inv_inv]
      rfl
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ g =>
      simp only [Quotient.map_mk, inv_inv]
      rfl

@[simp]
theorem quotientInvEquiv_mk (H K : Subgroup G) (g : G) :
    quotientInvEquiv H K (mk H K g) = mk K H g⁻¹ := (rfl)

/-! ## Double cosets as orbits -/

/-- The double coset `K s H` is the preimage, under `G → G ⧸ H`, of the `K`-orbit of the class of
`s`: the partition of `G` into `K`-`H` double cosets is the partition of `G ⧸ H` into `K`-orbits. -/
theorem mem_doubleCoset_iff_mk_mem_orbit (s : G) (H K : Subgroup G) {x : G} :
    x ∈ doubleCoset s (K : Set G) (H : Set G) ↔
      ((x : G ⧸ H)) ∈ orbit K ((s : G ⧸ H)) := by
  rw [mem_doubleCoset, mem_orbit_iff]
  constructor
  · rintro ⟨k, hk, h, hh, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [Submonoid.smul_def, Quotient.smul_mk, QuotientGroup.eq]
    simpa [mul_assoc] using hh
  · rintro ⟨k, hkx⟩
    rw [Submonoid.smul_def, Quotient.smul_mk, QuotientGroup.eq] at hkx
    exact ⟨k, k.2, ((k : G) * s)⁻¹ * x, hkx, (mul_inv_cancel_left _ _).symm⟩

/-- **Two translates of a point lie in one `K`-orbit exactly when the translating elements lie in
one double coset of `K` and the stabilizer of the point.** -/
theorem orbitRel_smul_iff_mem_doubleCoset_stabilizer (K : Subgroup G) (p : α) (x y : G) :
    orbitRel K α (x • p) (y • p) ↔
      x ∈ doubleCoset y (K : Set G) (stabilizer G p : Set G) := by
  rw [orbitRel_apply, mem_orbit_iff, mem_doubleCoset]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k : G), k.2, y⁻¹ * ((k : G)⁻¹ * x), ?_, by group⟩
    rw [SetLike.mem_coe, mem_stabilizer_iff, mul_smul, mul_smul, ← hk, Submonoid.smul_def,
      inv_smul_smul, inv_smul_smul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [Submonoid.smul_def, mul_smul, mul_smul,
      mem_stabilizer_iff.mp (SetLike.mem_coe.mp hb)]

/-- The double coset relation of `K` and the stabilizer of `p` is the relation of lying in one
`K`-orbit: `setoid K (Stab_G p) x y` exactly when `x • p` and `y • p` are `K`-translates. -/
theorem setoid_iff_orbitRel (K : Subgroup G) (p : α) (x y : G) :
    setoid (K : Set G) (stabilizer G p) x y ↔ orbitRel K α (x • p) (y • p) := by
  rw [rel_iff]
  constructor
  · rintro hmem
    exact (orbitRel K α).symm
      ((orbitRel_smul_iff_mem_doubleCoset_stabilizer K p y x).mpr (mem_doubleCoset.mpr hmem))
  · intro h
    exact mem_doubleCoset.mp ((orbitRel_smul_iff_mem_doubleCoset_stabilizer K p y x).mp
      ((orbitRel K α).symm h))

/-- **The double cosets `K \ G / Stab_G(p)` are the `K`-orbits inside the `G`-orbit of `p`.**

The codomain is the subtype of the `K`-orbit quotient that meets the `G`-orbit of `p`: the orbits of
`K` on `α` in which a translate of `p` lies. Taking that subtype rather than a `MulAction` on the
orbit avoids choosing a second action of `K` on `orbit G p`. -/
noncomputable def orbitRelQuotientEquivDoubleCoset (K : Subgroup G) (p : α) :
    Quotient (K : Set G) (stabilizer G p) ≃
      {o : orbitRel.Quotient K α // ∃ q, q ∈ orbit G p ∧ Quotient.mk'' q = o} := by
  classical
  refine Equiv.ofBijective
    (Quotient.lift (fun g => (⟨Quotient.mk'' (g • p), g • p, mem_orbit p g, rfl⟩ :
      {o : orbitRel.Quotient K α // ∃ q, q ∈ orbit G p ∧ Quotient.mk'' q = o})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    refine Subtype.ext ?_
    exact _root_.Quotient.sound ((setoid_iff_orbitRel K p a b).mp hab)
  · -- injectivity
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        have h : (Quotient.mk'' (a • p) : orbitRel.Quotient K α) = Quotient.mk'' (b • p) := by
          have := congrArg Subtype.val hxy
          simpa only [Quotient.lift_mk, Subtype.mk.injEq] using this
        exact _root_.Quotient.sound ((setoid_iff_orbitRel K p a b).mpr (Quotient.exact h))
  · -- surjectivity
    rintro ⟨o, q, hq, hqo⟩
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hq
    exact ⟨Quotient.mk'' g, Subtype.ext hqo⟩

/-! ## Finiteness and the index bound -/

/-- The map from the left-coset space `G ⧸ K` to the `K`-orbits on `α`, sending the class of `g` to
the orbit of `g⁻¹ • p`. It is a map of left cosets because replacing `g` by `g k` with `k ∈ K`
moves the point by `k⁻¹ ∈ K`. -/
def orbitMap (K : Subgroup G) (p : α) : G ⧸ K → orbitRel.Quotient K α :=
  Quotient.lift (fun g => Quotient.mk'' (g⁻¹ • p)) fun a b hab => by
    have hk : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
    exact _root_.Quotient.sound ⟨⟨a⁻¹ * b, hk⟩, by
      change ((⟨a⁻¹ * b, hk⟩ : ↥K) • (b⁻¹ • p)) = a⁻¹ • p
      rw [Submonoid.smul_def, smul_smul]
      congr 1
      group⟩

@[simp]
theorem orbitMap_mk (K : Subgroup G) (p : α) (g : G) :
    orbitMap K p (Quotient.mk'' g : G ⧸ K) = Quotient.mk'' (g⁻¹ • p) := (rfl)

theorem surjective_orbitMap (K : Subgroup G) (p : α) [MulAction.IsPretransitive G α] :
    Function.Surjective (orbitMap K p) := by
  rintro ⟨q⟩
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) p q
  exact ⟨Quotient.mk'' g⁻¹, by rw [orbitMap_mk, inv_inv]; exact congrArg Quotient.mk'' hg⟩

/-- **A finite-index subgroup has finitely many orbits on a pretransitive `G`-set.** -/
theorem finite_orbitRelQuotient_of_finiteIndex (K : Subgroup G) (p : α)
    [MulAction.IsPretransitive G α] [K.FiniteIndex] : Finite (orbitRel.Quotient K α) :=
  Finite.of_surjective _ (surjective_orbitMap K p)

/-- **A finite-index subgroup has at most `[G : K]` orbits on a pretransitive `G`-set.** -/
theorem natCard_orbitRelQuotient_le_index (K : Subgroup G) (p : α)
    [MulAction.IsPretransitive G α] [K.FiniteIndex] :
    Nat.card (orbitRel.Quotient K α) ≤ K.index :=
  (Nat.card_le_card_of_surjective _ (surjective_orbitMap K p)).trans_eq
    (Subgroup.index_eq_card K)

/-- The map from the left-coset space `G ⧸ K` onto the double-coset space `K \ G / H`, sending the
class of `g` to `K g⁻¹ H`. Inversion is what makes it a map of left cosets: replacing `g` by `g k`
with `k ∈ K` multiplies on the left by `k⁻¹ ∈ K`, which the left flanker absorbs. -/
def mkInv (H K : Subgroup G) : G ⧸ K → Quotient (K : Set G) H :=
  Quotient.lift (fun g => mk K H g⁻¹) fun a b hab => by
    have hk : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
    exact _root_.Quotient.sound ((rel_iff (H := K) (K := H)).mpr
      ⟨(a⁻¹ * b)⁻¹, K.inv_mem hk, 1, H.one_mem, by group⟩)

@[simp]
theorem mkInv_mk (H K : Subgroup G) (g : G) : mkInv H K (Quotient.mk'' g : G ⧸ K) = mk K H g⁻¹ :=
  (rfl)

theorem surjective_mkInv (H K : Subgroup G) : Function.Surjective (mkInv H K) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ g => exact ⟨Quotient.mk'' g⁻¹, by rw [mkInv_mk, inv_inv]⟩

/-- **A double-coset space `K \ G / H` with `K` of finite index is finite.** -/
theorem finite_quotient_of_finiteIndex (H K : Subgroup G) [K.FiniteIndex] :
    Finite (Quotient (K : Set G) H) :=
  Finite.of_surjective _ (surjective_mkInv H K)

/-- **A double-coset space `K \ G / H` has at most `[G : K]` elements.** -/
theorem natCard_quotient_le_index (H K : Subgroup G) [K.FiniteIndex] :
    Nat.card (Quotient (K : Set G) H) ≤ K.index :=
  (Nat.card_le_card_of_surjective _ (surjective_mkInv H K)).trans_eq (Subgroup.index_eq_card K)

end DoubleCoset
