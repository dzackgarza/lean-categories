/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Discriminant
public import LeanCategories.Modules.Bilinear.Valued.Witt
public import Mathlib.Algebra.Module.Injective
public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Ideal.Int

/-!
# The finite character count and the orthogonal-complement order formula

See the accompanying `README.md` for the statement of the results proved here:

* `integerPairingRestrict_surjective`, `integerPairingRestrict_ker`,
  `natCard_mul_natCard_orthogonal`, `natCard_quotient_orthogonal_mul_sq`;
* the character count `natCard_charGroup_of_finite`, whose non-formal input is the count of the
  `m`-torsion of `ℚ/ℤ` (`natCard_fractionValueQuotient_torsion`).
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

open LeanCategories.Modules.Bilinear.Valued

attribute [local instance 10000] Algebra.toModule

local instance (priority := 10000) moduleIntFractionValueQuotientLocal :
    Module ℤ (FractionValueQuotient ℤ) :=
  Submodule.Quotient.module (LinearMap.range (Algebra.linearMap ℤ (FractionRing ℤ)))

/-! ## Baer's criterion for `ℤ` from divisibility -/

/-- Baer's criterion over `ℤ`: a divisible abelian group is injective as a `ℤ`-module. -/
theorem module_baer_of_divisible (D : Type) [AddCommGroup D] [DivisibleBy D ℤ] :
    Module.Baer ℤ D := fun I g => by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn => ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  · let gm := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
    refine ⟨LinearMap.toSpanSingleton ℤ D (DivisibleBy.div gm m), fun n hn => ?_⟩
    rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
    rw [map_zsmul, LinearMap.toSpanSingleton_apply, DivisibleBy.div_cancel gm h0,
      ← map_zsmul g, SetLike.mk_smul_mk]

/-! ## `ℚ/ℤ` in the model `FractionRing ℤ / ℤ` -/

/-- The defining relation of `ℚ/ℤ = FractionRing ℤ / ℤ`. -/
theorem fractionValueQuotient_mk_eq_zero_iff (z : FractionRing ℤ) :
    ((Submodule.Quotient.mk z : FractionValueQuotient ℤ) = 0) ↔
      ∃ w : ℤ, algebraMap ℤ (FractionRing ℤ) w = z := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp h
    exact ⟨w, by rw [← hw, Algebra.linearMap_apply]⟩
  · rintro ⟨w, hw⟩
    exact LinearMap.mem_range.mpr ⟨w, by rw [Algebra.linearMap_apply, hw]⟩

/-- Every class of `ℚ/ℤ` has a representative. -/
theorem fractionValueQuotient_exists_rep (x : FractionValueQuotient ℤ) :
    ∃ q : FractionRing ℤ, (Submodule.Quotient.mk q : FractionValueQuotient ℤ) = x :=
  Submodule.Quotient.mk_surjective
    (p := LinearMap.range (Algebra.linearMap ℤ (FractionRing ℤ))) x

/-- Integer scalars pass through the quotient map of `ℚ/ℤ`. -/
theorem fractionValueQuotient_mk_zsmul (k : ℤ) (q : FractionRing ℤ) :
    (Submodule.Quotient.mk (k • q) : FractionValueQuotient ℤ) =
      k • (Submodule.Quotient.mk q : FractionValueQuotient ℤ) :=
  Submodule.Quotient.mk_smul (LinearMap.range (Algebra.linearMap ℤ (FractionRing ℤ))) k q

/-- `ℚ/ℤ` is divisible. -/
noncomputable instance divisibleBy_fractionValueQuotient_int :
    DivisibleBy (FractionValueQuotient ℤ) ℤ :=
  divisibleByOfSMulRightSurj (FractionValueQuotient ℤ) ℤ fun {n} hn => by
    intro x
    obtain ⟨q, hq⟩ := fractionValueQuotient_exists_rep x
    refine ⟨Submodule.Quotient.mk ((n : FractionRing ℤ)⁻¹ * q), ?_⟩
    rw [← hq]
    change n • (Submodule.Quotient.mk ((n : FractionRing ℤ)⁻¹ * q) : FractionValueQuotient ℤ) =
      Submodule.Quotient.mk q
    have hn' : (n : FractionRing ℤ) ≠ 0 := by exact_mod_cast hn
    rw [← fractionValueQuotient_mk_zsmul,
      show (n • ((n : FractionRing ℤ)⁻¹ * q)) = q from by
        rw [zsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]]

/-- Integer casts in a `ℤ`-algebra agree with `algebraMap`. -/
theorem int_cast_algebraMap_eq (j : ℤ) :
    ((j : FractionRing ℤ)) = algebraMap ℤ (FractionRing ℤ) j :=
  (map_intCast (algebraMap ℤ (FractionRing ℤ)) j).symm

/-- `ℤ ⧸ mℤ` has `m` elements. -/
theorem natCard_intQuotient_span (m : ℕ) (hm : 0 < m) :
    Nat.card (ℤ ⧸ Submodule.span ℤ {(m : ℤ)}) = m := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod m).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card]

/-- The `m`-torsion of the rational circle has exactly `m` elements. -/
theorem natCard_addCircle_torsion (m : ℕ) (hm : 0 < m) :
    Nat.card {u : AddCircle (1 : ℚ) // m • u = 0} = m := by
  classical
  set g : AddCircle (1 : ℚ) := ↑((1 : ℚ) / (m : ℚ) * 1) with hg
  have hgord : addOrderOf g = m := by
    have h := AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℚ)) (m := 1) (n := m) hm
      (by simp)
    simpa [hg] using h
  have hgm : m • g = 0 := by
    rw [← hgord]
    exact addOrderOf_nsmul_eq_zero g
  have hmem : ∀ k : ℕ, m • (k • g) = 0 := by
    intro k
    rw [smul_comm, hgm, smul_zero]
  have hsurj : Function.Surjective
      (fun k : Fin m => (⟨(k : ℕ) • g, hmem k⟩ : {u : AddCircle (1 : ℚ) // m • u = 0})) := by
    rintro ⟨u, hu⟩
    obtain ⟨k, hk, hku⟩ := (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) hm).mp hu
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    change (k : ℕ) • g = u
    rw [← hku]
    have hg' : g = ↑((1 : ℚ) / (m : ℚ)) := by rw [hg]; simp
    rw [hg']
    exact (AddCircle.natCast_div_mul_eq_nsmul (1 : ℚ) (m : ℚ) 1 k).symm
  have hinj : Function.Injective
      (fun k : Fin m => (⟨(k : ℕ) • g, hmem k⟩ : {u : AddCircle (1 : ℚ) // m • u = 0})) := by
    intro k₁ k₂ h
    have h' : (k₁ : ℕ) • g = (k₂ : ℕ) • g := congrArg Subtype.val h
    refine Fin.ext (nsmul_injOn_Iio_addOrderOf ?_ ?_ h')
    · rw [hgord]; exact k₁.2
    · rw [hgord]; exact k₂.2
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-! ## Characters of a finite abelian group -/

section CharGroup

variable {D : Type} [AddCommGroup D]

/-- The character group `A →+ D`. -/
abbrev CharGroup (A : Type*) [AddCommGroup A] := A →+ D

/-- Restriction of characters along a subgroup. -/
def charRes {A : Type} [AddCommGroup A] (C : Submodule ℤ A) :
    CharGroup (D := D) A →+ CharGroup (D := D) ↥C where
  toFun f := f.comp (Submodule.subtype C).toAddMonoidHom
  map_zero' := by ext x; simp
  map_add' f g := by ext x; simp

/-- Inflation of characters along the quotient map. -/
def charInfl {A : Type} [AddCommGroup A] (C : Submodule ℤ A) :
    CharGroup (D := D) (A ⧸ C) →+ CharGroup (D := D) A where
  toFun f := f.comp (Submodule.mkQ C).toAddMonoidHom
  map_zero' := by ext x; simp
  map_add' f g := by ext x; simp

theorem charInfl_injective {A : Type} [AddCommGroup A] (C : Submodule ℤ A) :
    Function.Injective (charInfl (D := D) C) := by
  intro f g h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective C x
  exact DFunLike.congr_fun h y

theorem charInfl_range_le_ker {A : Type} [AddCommGroup A] (C : Submodule ℤ A) :
    (charInfl (D := D) C).range ≤ (charRes (D := D) C).ker := by
  rintro _ ⟨g, rfl⟩
  ext x
  change g ((Submodule.mkQ C) (x : A)) = 0
  have hx0 : (Submodule.mkQ C) (x : A) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2
  rw [hx0, map_zero]

theorem ker_le_charInfl_range {A : Type} [AddCommGroup A] (C : Submodule ℤ A) :
    (charRes (D := D) C).ker ≤ (charInfl (D := D) C).range := by
  intro f hf
  have hzero : ∀ x ∈ C, f x = 0 := by
    intro x hx
    have h := DFunLike.congr_fun hf ⟨x, hx⟩
    simpa [charRes] using h
  have hker : C ≤ LinearMap.ker f.toIntLinearMap := by
    intro x hx
    rw [LinearMap.mem_ker]
    simpa using hzero x hx
  refine ⟨(Submodule.liftQ C f.toIntLinearMap hker).toAddMonoidHom, ?_⟩
  apply AddMonoidHom.ext
  intro x
  change (Submodule.liftQ C f.toIntLinearMap hker) (Submodule.Quotient.mk x) = f x
  rw [Submodule.liftQ_apply]
  rfl

/-- Restriction of characters to a subgroup is surjective: Baer's criterion. -/
theorem charRes_surjective [DivisibleBy D ℤ] {A : Type} [AddCommGroup A]
    (C : Submodule ℤ A) : Function.Surjective (charRes (D := D) C) := by
  intro c
  obtain ⟨d, hd⟩ := (module_baer_of_divisible D).extension_property_addMonoidHom
    (Submodule.subtype C).toAddMonoidHom (Submodule.injective_subtype C) c
  exact ⟨d, hd⟩

/-- Characters of `ℤ ⧸ mℤ` are exactly the `m`-torsion elements of `D`. -/
theorem natCard_charGroup_intQuotient [DivisibleBy D ℤ]
    (htors : ∀ m : ℕ, 0 < m → Nat.card {x : D // m • x = 0} = m)
    (m : ℕ) (hm : 0 < m) :
    Nat.card (CharGroup (D := D) (ℤ ⧸ Submodule.span ℤ {(m : ℤ)})) = m := by
  classical
  -- the character attached to an `m`-torsion element
  have lh : ∀ (x : D) (h : (LinearMap.toSpanSingleton ℤ D x) (m : ℤ) = 0) (k : ℤ),
      (Submodule.liftQSpanSingleton (R := ℤ) (m : ℤ) (LinearMap.toSpanSingleton ℤ D x) h)
        (Submodule.Quotient.mk k) = k • x := by
    intro x h k
    rw [Submodule.liftQSpanSingleton_apply, LinearMap.toSpanSingleton_apply]
  have hvan : ∀ x : D, m • x = 0 → (LinearMap.toSpanSingleton ℤ D x) (m : ℤ) = 0 := by
    intro x hx
    rw [LinearMap.toSpanSingleton_apply]
    change ((m : ℤ) • x) = 0
    rw [show ((m : ℤ) • x) = m • x from by simp]
    exact hx
  have hf0 : ∀ f : CharGroup (D := D) (ℤ ⧸ Submodule.span ℤ {(m : ℤ)}),
      m • f (Submodule.Quotient.mk (1 : ℤ)) = 0 := by
    intro f
    have h : (m : ℕ) • (Submodule.Quotient.mk (1 : ℤ) :
        ℤ ⧸ Submodule.span ℤ {(m : ℤ)}) = 0 := by
      rw [← Submodule.Quotient.mk_smul (Submodule.span ℤ {(m : ℤ)}) (m : ℕ) (1 : ℤ)]
      refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
      rw [Submodule.mem_span_singleton]
      refine ⟨1, ?_⟩
      change (1 : ℤ) • (m : ℤ) = (m : ℕ) • (1 : ℤ)
      simp
    calc m • f (Submodule.Quotient.mk (1 : ℤ))
        = f ((m : ℕ) • (Submodule.Quotient.mk (1 : ℤ) :
            ℤ ⧸ Submodule.span ℤ {(m : ℤ)})) := (map_nsmul f m _).symm
      _ = f 0 := by rw [h]
      _ = 0 := map_zero f
  have hbij : Nat.card (CharGroup (D := D) (ℤ ⧸ Submodule.span ℤ {(m : ℤ)})) =
      Nat.card {x : D // m • x = 0} := by
    refine Nat.card_congr
      { toFun := fun f => ⟨f (Submodule.Quotient.mk (1 : ℤ)), hf0 f⟩
        invFun := fun x =>
          (Submodule.liftQSpanSingleton (R := ℤ) (m : ℤ)
            (LinearMap.toSpanSingleton ℤ D x.1) (hvan x.1 x.2)).toAddMonoidHom
        left_inv := ?_
        right_inv := ?_ }
    · intro f
      apply AddMonoidHom.ext
      intro y
      obtain ⟨k, hk⟩ := Submodule.mkQ_surjective (Submodule.span ℤ {(m : ℤ)}) y
      rw [← hk, Submodule.mkQ_apply]
      change (Submodule.liftQSpanSingleton (R := ℤ) (m : ℤ)
          (LinearMap.toSpanSingleton ℤ D (f (Submodule.Quotient.mk (1 : ℤ))))
          (hvan (f (Submodule.Quotient.mk (1 : ℤ))) (hf0 f))) (Submodule.Quotient.mk k) =
        f (Submodule.Quotient.mk k)
      rw [lh]
      have hsym : (Submodule.Quotient.mk k : ℤ ⧸ Submodule.span ℤ {(m : ℤ)}) =
          k • Submodule.Quotient.mk (1 : ℤ) := by
        rw [← Submodule.Quotient.mk_smul (Submodule.span ℤ {(m : ℤ)}) k (1 : ℤ)]
        congr 1
        rw [zsmul_eq_mul, mul_one]
        simp
      rw [hsym, map_zsmul]
    · intro x
      apply Subtype.ext
      change (Submodule.liftQSpanSingleton (R := ℤ) (m : ℤ)
          (LinearMap.toSpanSingleton ℤ D x.1) (hvan x.1 x.2))
          (Submodule.Quotient.mk (1 : ℤ)) = x.1
      rw [lh, one_smul]
  rw [hbij, htors m hm]


/-- Characters transport along an isomorphism of groups. -/
def charGroupCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    CharGroup (D := D) A ≃ CharGroup (D := D) B where
  toFun f := f.comp e.symm.toAddMonoidHom
  invFun g := g.comp e.toAddMonoidHom
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp

/-- A cyclic subgroup generated by `a` is `ℤ ⧸ mℤ` with `m` the order of `a`. -/
noncomputable def spanEquivIntQuotient (A : Type) [AddCommGroup A] (a : A) :
    ↥(Submodule.span ℤ {a}) ≃ₗ[ℤ] (ℤ ⧸ Submodule.span ℤ {((addOrderOf a : ℕ) : ℤ)}) := by
  have hker : (LinearMap.toSpanSingleton ℤ A a).ker =
      Submodule.span ℤ {((addOrderOf a : ℕ) : ℤ)} := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Submodule.mem_span_singleton,
      ← addOrderOf_dvd_iff_zsmul_eq_zero, dvd_def]
    constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩
    · rw [zsmul_eq_mul]; simpa [mul_comm] using hc.symm
    · rw [← hc, zsmul_eq_mul, mul_comm]
      simp
  exact (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range ℤ A a)).trans
    ((LinearMap.quotKerEquivRange (LinearMap.toSpanSingleton ℤ A a)).symm.trans
      (Submodule.quotEquivOfEq _ _ hker))

/-- The character group of a cyclic subgroup has the cardinality of the subgroup. -/
theorem natCard_charGroup_span [DivisibleBy D ℤ]
    (htors : ∀ m : ℕ, 0 < m → Nat.card {x : D // m • x = 0} = m)
    {A : Type} [AddCommGroup A] {a : A} (hm : 0 < addOrderOf a) :
    Nat.card (CharGroup (D := D) ↥(Submodule.span ℤ {a})) =
      Nat.card ↥(Submodule.span ℤ {a}) := by
  classical
  calc Nat.card (CharGroup (D := D) ↥(Submodule.span ℤ {a}))
      = Nat.card (CharGroup (D := D)
          (ℤ ⧸ Submodule.span ℤ {((addOrderOf a : ℕ) : ℤ)})) :=
        Nat.card_congr (charGroupCongr (D := D) (spanEquivIntQuotient A a).toAddEquiv)
    _ = addOrderOf a := natCard_charGroup_intQuotient htors (addOrderOf a) hm
    _ = Nat.card ↥(Submodule.span ℤ {a}) := by
        rw [Nat.card_congr (spanEquivIntQuotient A a).toAddEquiv.toEquiv,
          natCard_intQuotient_span (addOrderOf a) hm]

end CharGroup

/-! ## The character count -/

/-- The exact sequence `0 → (A⧸C)⋆ → A⋆ → C⋆ → 0` on characters of a finite group. -/
theorem natCard_charGroup_mul (D : Type) [AddCommGroup D] [DivisibleBy D ℤ] {A : Type}
    [AddCommGroup A] [Finite A] (C : Submodule ℤ A) :
    Nat.card (CharGroup (D := D) A) =
      Nat.card (CharGroup (D := D) (A ⧸ C)) * Nat.card (CharGroup (D := D) ↥C) := by
  classical
  have : Finite ↥C := Finite.of_injective _ Subtype.val_injective
  have hrange : (charRes (D := D) C).range = ⊤ := by
    rw [AddMonoidHom.range_eq_top]
    exact charRes_surjective C
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (charRes (D := D) C).ker
  have hquot : Nat.card (CharGroup (D := D) A ⧸ (charRes (D := D) C).ker) =
      Nat.card (CharGroup (D := D) ↥C) :=
    (by
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange
        (charRes (D := D) C)).toEquiv, hrange]
      exact Nat.card_congr
        { toFun := fun x => x.1
          invFun := fun y => ⟨y, AddSubgroup.mem_top y⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun y => rfl })
  have hranges : (charInfl (D := D) C).range = (charRes (D := D) C).ker :=
    le_antisymm (charInfl_range_le_ker C) (ker_le_charInfl_range C)
  have hker : Nat.card ↥(charRes (D := D) C).ker =
      Nat.card (CharGroup (D := D) (A ⧸ C)) := by
    rw [← hranges]
    exact Nat.card_congr (Equiv.ofInjective _ (charInfl_injective C)).symm
  rw [hcard, hquot, hker, mul_comm]

/-- **Character count.** The character group of a finite abelian group has the cardinality of the
group, provided the target is divisible and its `m`-torsion has `m` elements. -/
theorem natCard_charGroup_of_finite (D : Type) [AddCommGroup D] [DivisibleBy D ℤ]
    (htors : ∀ m : ℕ, 0 < m → Nat.card {x : D // m • x = 0} = m)
    (A : Type) [AddCommGroup A] [Finite A] :
    Nat.card (CharGroup (D := D) A) = Nat.card A := by
  classical
  suffices H : ∀ n, ∀ (B : Type) [AddCommGroup B] [Finite B], Nat.card B = n →
      Nat.card (CharGroup (D := D) B) = n from H _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B _ _ hB
    by_cases hsub : Subsingleton B
    · have := hsub
      have htriv : Subsingleton (CharGroup (D := D) B) :=
        ⟨fun f g => AddMonoidHom.ext fun x => by
          rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      rw [Nat.card_of_subsingleton (0 : CharGroup (D := D) B), ← hB,
        Nat.card_of_subsingleton (0 : B)]
    · have : Nontrivial B := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨a, ha⟩ : ∃ a : B, a ≠ 0 := exists_ne 0
      set C : Submodule ℤ B := Submodule.span ℤ {a} with hC
      have hmpos : 0 < addOrderOf a := (isOfFinAddOrder_of_finite a).addOrderOf_pos
      have hCcard : Nat.card ↥C = addOrderOf a := by
        rw [Nat.card_congr (spanEquivIntQuotient B a).toAddEquiv.toEquiv,
          natCard_intQuotient_span (addOrderOf a) hmpos]
      have hCchar : Nat.card (CharGroup (D := D) ↥C) = Nat.card ↥C := by
        rw [hC]
        exact natCard_charGroup_span htors hmpos
      have hlag : Nat.card B = Nat.card ↥C * Nat.card (B ⧸ C) :=
        Submodule.card_eq_card_quotient_mul_card C
      have h2 : 2 ≤ Nat.card ↥C := by
        rw [hCcard]
        have hne1 : addOrderOf a ≠ 1 := by
          intro h1
          apply ha
          have h0 := addOrderOf_nsmul_eq_zero a
          rw [h1, one_nsmul] at h0
          exact h0
        omega
      have : Finite ↥C := Finite.of_injective _ Subtype.val_injective
      have : Finite (B ⧸ C) := Finite.of_surjective _ (Submodule.mkQ_surjective C)
      have hpos : 0 < Nat.card (B ⧸ C) := Nat.card_pos
      have hlt : Nat.card (B ⧸ C) < n := by
        have h1 : Nat.card (B ⧸ C) < Nat.card ↥C * Nat.card (B ⧸ C) := by
          calc Nat.card (B ⧸ C) = 1 * Nat.card (B ⧸ C) := (one_mul _).symm
            _ < Nat.card ↥C * Nat.card (B ⧸ C) :=
                Nat.mul_lt_mul_of_pos_right (by omega) hpos
        omega
      have hih := ih (Nat.card (B ⧸ C)) hlt (B ⧸ C) rfl
      rw [natCard_charGroup_mul D C, hih, hCchar, ← hB, hlag, mul_comm]

/-! ## The restriction of a discriminant pairing to a submodule -/

section Pairing

variable (A : BilinModuleCat ℤ (FractionValueQuotient ℤ))

/-- Restriction of the pairing to a submodule, as a character of the whole carrier. -/
noncomputable def integerPairingRestrict [Finite A.carrier] (H : Submodule ℤ A.carrier) :
    A.carrier →+ (↥H →+ FractionValueQuotient ℤ) where
  toFun x :=
    { toFun := fun y => A.pairing x (y : A.carrier)
      map_zero' := by simp
      map_add' := fun y z => by simp }
  map_zero' := by ext z; simp
  map_add' x y := by ext z; simp

/-- **The kernel of the restriction is the orthogonal complement.** -/
theorem integerPairingRestrict_ker [Finite A.carrier] (hA : A.IsSymmetric)
    (H : Submodule ℤ A.carrier) (x : A.carrier) :
    integerPairingRestrict A H x = 0 ↔ ∀ y ∈ H, A.pairing y x = 0 := by
  constructor
  · intro hx y hy
    have h := DFunLike.congr_fun hx ⟨y, hy⟩
    rw [show A.pairing y x = A.pairing x y from hA y x]
    exact h
  · intro hx
    apply AddMonoidHom.ext
    intro y
    change A.pairing x (y : A.carrier) = 0
    rw [show A.pairing x (y : A.carrier) = A.pairing (y : A.carrier) x from hA x y]
    exact hx (y : A.carrier) y.2

end Pairing

/-- The integral image in the canonical fraction field is the integers under the rational
equivalence. -/
theorem range_algebraMap_eq_zmultiples :
    ((LinearMap.range (Algebra.linearMap ℤ (FractionRing ℤ))).toAddSubgroup).map
        (FractionRing.algEquiv ℤ ℚ).toAddEquiv = AddSubgroup.zmultiples (1 : ℚ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨z, ?_⟩
    calc z • (1 : ℚ) = (z : ℚ) := by simp
      _ = (FractionRing.algEquiv ℤ ℚ) (algebraMap ℤ (FractionRing ℤ) z) :=
        ((FractionRing.algEquiv ℤ ℚ).commutes z).symm
      _ = ((FractionRing.algEquiv ℤ ℚ).toAddEquiv) ((Algebra.linearMap ℤ (FractionRing ℤ)) z) := by
        rw [Algebra.linearMap_apply]
        symm
        rfl
  · intro hy
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    refine ⟨algebraMap ℤ (FractionRing ℤ) z, ⟨z, by rw [Algebra.linearMap_apply]⟩, ?_⟩
    rw [← hz]
    calc ((FractionRing.algEquiv ℤ ℚ).toAddEquiv) (algebraMap ℤ (FractionRing ℤ) z)
        = (FractionRing.algEquiv ℤ ℚ) (algebraMap ℤ (FractionRing ℤ) z) := rfl
      _ = (z : ℚ) := (FractionRing.algEquiv ℤ ℚ).commutes z
      _ = z • (1 : ℚ) := by simp

/-- The repository's `FractionRing ℤ / ℤ` is the additive circle. -/
noncomputable def fractionValueQuotientEquivAddCircle :
    FractionValueQuotient ℤ ≃+ AddCircle (1 : ℚ) :=
  QuotientAddGroup.congr
    ((LinearMap.range (Algebra.linearMap ℤ (FractionRing ℤ))).toAddSubgroup)
    (AddSubgroup.zmultiples (1 : ℚ))
    (FractionRing.algEquiv ℤ ℚ).toAddEquiv range_algebraMap_eq_zmultiples

/-- The `m`-torsion of the repository's model of `ℚ/ℤ` has exactly `m` elements. -/
theorem natCard_fractionValueQuotient_torsion (m : ℕ) (hm : 0 < m) :
    Nat.card {x : FractionValueQuotient ℤ // m • x = 0} = m := by
  calc Nat.card {x : FractionValueQuotient ℤ // m • x = 0}
      = Nat.card {u : AddCircle (1 : ℚ) // m • u = 0} :=
    Nat.card_congr (Equiv.subtypeEquiv fractionValueQuotientEquivAddCircle (fun x => by
      constructor
      · intro hx
        calc m • fractionValueQuotientEquivAddCircle x
            = fractionValueQuotientEquivAddCircle (m • x) :=
          (map_nsmul fractionValueQuotientEquivAddCircle.toAddMonoidHom m x).symm
        _ = fractionValueQuotientEquivAddCircle 0 := congrArg _ hx
        _ = 0 := map_zero _
      · intro hx
        apply fractionValueQuotientEquivAddCircle.injective
        calc fractionValueQuotientEquivAddCircle (m • x)
            = m • fractionValueQuotientEquivAddCircle x :=
          map_nsmul fractionValueQuotientEquivAddCircle.toAddMonoidHom m x
        _ = 0 := hx
        _ = fractionValueQuotientEquivAddCircle 0 := (map_zero _).symm))
    _ = m := natCard_addCircle_torsion m hm

/-- Every character on a submodule extends to a discriminant representative. -/
theorem integerPairingRestrict_surjective (A : BilinModuleCat ℤ (FractionValueQuotient ℤ))
    [Finite A.carrier] (hA : A.IsPerfect) (H : Submodule ℤ A.carrier) :
    Function.Surjective (integerPairingRestrict A H) := by
  intro c
  obtain ⟨d, hd⟩ :=
    (module_baer_of_divisible (FractionValueQuotient ℤ)).extension_property_addMonoidHom
      H.subtype.toAddMonoidHom H.injective_subtype c
  let d' : A.carrier →ₗ[ℤ] FractionValueQuotient ℤ :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := fun n x => by
        change d (A.carrier.isModule.smul n x) =
          moduleIntFractionValueQuotientLocal.smul n (d x)
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
        exact d.map_zsmul n x }
  obtain ⟨x, hx⟩ := hA.1.2 d'
  refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
  change A.pairing x (y : A.carrier) = c y
  calc A.pairing x (y : A.carrier) = d y := DFunLike.congr_fun hx (y : A.carrier)
    _ = d (H.subtype y) := rfl
    _ = c y := DFunLike.congr_fun hd y

/-- The restriction kernel is the categorical orthogonal submodule. -/
theorem integerPairingRestrict_ker_eq (A : BilinModuleCat ℤ (FractionValueQuotient ℤ))
    [Finite A.carrier] (hA : A.IsSymmetric) (H : Submodule ℤ A.carrier) :
    AddMonoidHom.ker (integerPairingRestrict A H) =
      (BilinModuleCat.orthogonalSubmodule A H).toAddSubgroup := by
  ext x
  change (integerPairingRestrict A H) x = 0 ↔ ∀ y ∈ H, A.pairing y x = 0
  exact integerPairingRestrict_ker A hA H x

/-- The orthogonal-complement cardinality identity, from character restriction. -/
theorem natCard_mul_natCard_orthogonal (A : BilinModuleCat ℤ (FractionValueQuotient ℤ))
    [Finite A.carrier] (hA : A.IsPerfect) (hS : A.IsSymmetric)
    (H : Submodule ℤ A.carrier) :
    Nat.card H * Nat.card (BilinModuleCat.orthogonalSubmodule A H) = Nat.card A.carrier := by
  have hs := integerPairingRestrict_surjective A hA H
  let e : ↥(BilinModuleCat.orthogonalSubmodule A H) ≃ (integerPairingRestrict A H).ker :=
    { toFun := fun x => ⟨x.1, (integerPairingRestrict_ker A hS H x).mpr x.2⟩
      invFun := fun x => ⟨x.1, (integerPairingRestrict_ker A hS H x).mp x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hindex : (integerPairingRestrict A H).ker.index = Nat.card H := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs,
      Nat.card_congr AddSubgroup.topEquiv.toEquiv]
    exact natCard_charGroup_of_finite (FractionValueQuotient ℤ)
      natCard_fractionValueQuotient_torsion ↥H
  calc Nat.card H * Nat.card (BilinModuleCat.orthogonalSubmodule A H)
      = Nat.card (integerPairingRestrict A H).ker * (integerPairingRestrict A H).ker.index := by
        rw [← hindex, Nat.card_congr e, mul_comm]
    _ = Nat.card A.carrier := (integerPairingRestrict A H).ker.card_mul_index

attribute [local instance 10000] Submodule.Quotient.module
attribute [local instance 10000] Submodule.module

/-- An isotropic subgroup has the complementary orthogonal-subquotient order. -/
theorem natCard_quotient_orthogonal_mul_sq (A : BilinModuleCat ℤ (FractionValueQuotient ℤ))
    [Finite A.carrier] (hA : A.IsPerfect) (hS : A.IsSymmetric)
    (H : Submodule ℤ A.carrier)
    (hH : BilinModuleCat.IsTotallyIsotropic A H) :
    Nat.card (↥(BilinModuleCat.orthogonalSubmodule A H) ⧸
      Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) * Nat.card H ^ 2 =
      Nat.card A.carrier := by
  let _ : Module ℤ (BilinModuleCat.orthogonalSubmodule A H) :=
    (BilinModuleCat.orthogonalSubmodule A H).module
  let eH : ↥H ≃ ↥(Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) :=
    { toFun := fun y => ⟨⟨y.1, hH y.2⟩, y.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Nat.card (↥(BilinModuleCat.orthogonalSubmodule A H) ⧸
      Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) * Nat.card H =
      Nat.card (BilinModuleCat.orthogonalSubmodule A H) := by
    calc Nat.card (↥(BilinModuleCat.orthogonalSubmodule A H) ⧸
        Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) * Nat.card H
        = Nat.card ↥(Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) *
          Nat.card (↥(BilinModuleCat.orthogonalSubmodule A H) ⧸
            Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) := by
          rw [Nat.card_congr eH, mul_comm]
      _ = Nat.card (BilinModuleCat.orthogonalSubmodule A H) :=
        (Submodule.card_eq_card_quotient_mul_card
          (Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H)).symm
  have horth := natCard_mul_natCard_orthogonal A hA hS H
  calc Nat.card (↥(BilinModuleCat.orthogonalSubmodule A H) ⧸
        Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) * Nat.card H ^ 2
      = (Nat.card (↥(BilinModuleCat.orthogonalSubmodule A H) ⧸
          Submodule.comap (BilinModuleCat.orthogonalSubmodule A H).subtype H) * Nat.card H) *
        Nat.card H := by rw [pow_two, mul_assoc]
    _ = Nat.card (BilinModuleCat.orthogonalSubmodule A H) * Nat.card H := by rw [hcard]
    _ = Nat.card A.carrier := by rw [mul_comm]; exact horth

end LeanCategories.Lattices.Valued
