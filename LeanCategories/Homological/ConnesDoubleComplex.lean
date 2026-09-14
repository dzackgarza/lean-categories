/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.MixedComplex
public import LeanCategories.Homological.DoubleComplexFirstPages
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Connes' double complex of a mixed complex

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.8.2,
pp. 344--353 (FC05-C09-U115).

For a mixed complex `(M,b,B)`, Connes' first-quadrant double complex has
entry `M_{q-p}` in bidegree `(p,q)` when `p≤q`, and zero otherwise.  Its
vertical differential is `b` and its horizontal differential is `B`.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Shift the nonnegative chain-complex shape upward by `p` degrees.  Extending
along this embedding puts a complex `K` in rows `q ≥ p`, with row `p+n`
identified with `K_n`, and puts the zero object below row `p`. -/
def connesShiftEmbedding (p : ℕ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => p + n)
    (fun _ _ h => Nat.add_left_cancel h)
    (by
      intro i j
      simp only [ComplexShape.down_Rel]
      omega)

/-- Column `p` of Connes' double complex.  It is the underlying chain complex
of `M`, shifted so that row `q` is `M_{q-p}` for `p ≤ q`, and is zero above
the diagonal `q < p`. -/
noncomputable def connesColumn (M : MixedComplex C) (p : ℕ) : ChainComplex C ℕ :=
  M.chain.extend (connesShiftEmbedding p)

/-- The canonical identification of row `q=p+n` in column `p` with `M_n`.
This witness-indexed form is the internal API: it avoids inserting transports
between `M_n`, `M_{n+1}`, and their shifted copies. -/
noncomputable def connesColumnIsoAt (M : MixedComplex C) (p n q : ℕ)
    (h : p + n = q) : (connesColumn M p).X q ≅ M.chain.X n :=
  M.chain.extendXIso (connesShiftEmbedding p) h

/-- The canonical identification of the nonzero bidegree `(p,q)` with
`M_{q-p}`. -/
noncomputable def connesColumnIso (M : MixedComplex C) (p q : ℕ) (hpq : p ≤ q) :
    (connesColumn M p).X q ≅ M.chain.X (q - p) :=
  connesColumnIsoAt M p (q - p) q (by omega)

lemma connesColumn_d_eq_of_eq (M : MixedComplex C) (p n i j : ℕ)
    (hi : p + (n + 1) = i) (hj : p + n = j) :
    (connesColumn M p).d i j =
      (connesColumnIsoAt M p (n + 1) i hi).hom ≫
        M.chain.d (n + 1) n ≫
        (connesColumnIsoAt M p n j hj).inv := by
  unfold connesColumn connesColumnIsoAt
  exact HomologicalComplex.extend_d_eq M.chain (connesShiftEmbedding p) hi hj

lemma connesColumn_d_eq_at (M : MixedComplex C) (p n : ℕ) :
    (connesColumn M p).d (p + n + 1) (p + n) =
      (connesColumnIsoAt M p (n + 1) (p + n + 1) (by omega)).hom ≫
        M.chain.d (n + 1) n ≫
        (connesColumnIsoAt M p n (p + n) rfl).inv :=
  connesColumn_d_eq_of_eq M p n (p + n + 1) (p + n) (by omega) rfl

lemma connesColumn_isZero (M : MixedComplex C) (p q : ℕ) (hqp : q < p) :
    IsZero ((connesColumn M p).X q) := by
  apply M.chain.isZero_extend_X (connesShiftEmbedding p) q
  intro n hn
  change p + n = q at hn
  omega

/-- The horizontal `B`-map from column `p+1` to column `p`, with the parity
sign required by Mathlib's nested-chain-complex encoding.  At row `q ≥ p+1`
this is `(-1)^q B : M_{q-p-1} → M_{q-p}`; below that range it is zero.

The sign converts the mixed-complex identity `bB + Bb = 0` into ordinary
commutation with the inner chain differential.  Mathlib's totalization then
uses its standard column sign on the vertical differential. -/
noncomputable def connesHorizontalF (M : MixedComplex C) (p q : ℕ) :
    (connesColumn M (p + 1)).X q ⟶ (connesColumn M p).X q :=
  match h : (connesShiftEmbedding (p + 1)).r q with
  | some n =>
      (connesColumnIsoAt M (p + 1) n q (by
          have hq := (connesShiftEmbedding (p + 1)).f_eq_of_r_eq_some h
          change p + 1 + n = q at hq
          exact hq)).hom ≫
        ((-1 : ℤ) ^ q • M.B n) ≫
        (connesColumnIsoAt M p (n + 1) q (by
          have hq := (connesShiftEmbedding (p + 1)).f_eq_of_r_eq_some h
          change p + 1 + n = q at hq
          omega)).inv
  | none => 0

lemma connesHorizontalF_eq_of_eq (M : MixedComplex C) (p n q : ℕ)
    (hq : p + 1 + n = q) :
    connesHorizontalF M p q =
      (connesColumnIsoAt M (p + 1) n q hq).hom ≫
        ((-1 : ℤ) ^ q • M.B n) ≫
        (connesColumnIsoAt M p (n + 1) q (by omega)).inv := by
  unfold connesHorizontalF
  split
  next k hk =>
    have hq := (connesShiftEmbedding (p + 1)).f_eq_of_r_eq_some hk
    change p + 1 + k = q at hq
    have hkn : k = n := by omega
    subst k
    rfl
  next hn =>
    have hs := (connesShiftEmbedding (p + 1)).r_eq_some
      (show (connesShiftEmbedding (p + 1)).f n = q by exact hq)
    rw [hn] at hs
    contradiction

lemma connesHorizontalF_eq_at (M : MixedComplex C) (p n : ℕ) :
    connesHorizontalF M p (p + 1 + n) =
      (connesColumnIsoAt M (p + 1) n (p + 1 + n) rfl).hom ≫
        ((-1 : ℤ) ^ (p + 1 + n) • M.B n) ≫
        (connesColumnIsoAt M p (n + 1) (p + 1 + n) (by omega)).inv :=
  connesHorizontalF_eq_of_eq M p n (p + 1 + n) rfl

lemma connesHorizontalF_eq_zero (M : MixedComplex C) (p q : ℕ) (hqp : q < p + 1) :
    connesHorizontalF M p q = 0 := by
  unfold connesHorizontalF
  split
  next n hn =>
    have hq := (connesShiftEmbedding (p + 1)).f_eq_of_r_eq_some hn
    change p + 1 + n = q at hq
    omega
  next => rfl

/-- The horizontal differential as a chain map between adjacent columns. -/
noncomputable def connesHorizontal (M : MixedComplex C) (p : ℕ) :
    connesColumn M (p + 1) ⟶ connesColumn M p where
  f q := connesHorizontalF M p q
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst i
    by_cases hpj : p ≤ j
    · by_cases hspj : p + 1 ≤ j
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hspj
        have hf₁ : connesHorizontalF M p (p + 1 + n + 1) =
            (connesColumnIsoAt M (p + 1) (n + 1) (p + 1 + n + 1) (by omega)).hom ≫
              ((-1 : ℤ) ^ (p + 1 + n + 1) • M.B (n + 1)) ≫
              (connesColumnIsoAt M p (n + 2) (p + 1 + n + 1) (by omega)).inv := by
          exact connesHorizontalF_eq_of_eq M p (n + 1) (p + 1 + n + 1) (by omega)
        have hf₀ : connesHorizontalF M p (p + 1 + n) =
            (connesColumnIsoAt M (p + 1) n (p + 1 + n) rfl).hom ≫
              ((-1 : ℤ) ^ (p + 1 + n) • M.B n) ≫
              (connesColumnIsoAt M p (n + 1) (p + 1 + n) (by omega)).inv :=
          connesHorizontalF_eq_at M p n
        have hdₜ : (connesColumn M p).d (p + 1 + n + 1) (p + 1 + n) =
            (connesColumnIsoAt M p (n + 2) (p + 1 + n + 1) (by omega)).hom ≫
              M.chain.d (n + 2) (n + 1) ≫
              (connesColumnIsoAt M p (n + 1) (p + 1 + n) (by omega)).inv := by
          exact connesColumn_d_eq_of_eq M p (n + 1) (p + 1 + n + 1) (p + 1 + n)
            (by omega) (by omega)
        have hdₛ : (connesColumn M (p + 1)).d (p + 1 + n + 1) (p + 1 + n) =
            (connesColumnIsoAt M (p + 1) (n + 1) (p + 1 + n + 1) (by omega)).hom ≫
              M.chain.d (n + 1) n ≫
              (connesColumnIsoAt M (p + 1) n (p + 1 + n) rfl).inv := by
          exact connesColumn_d_eq_of_eq M (p + 1) n (p + 1 + n + 1) (p + 1 + n)
            (by omega) rfl
        rw [hf₁, hf₀, hdₜ, hdₛ]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        have hm := M.mixed_succ n
        have hneg :
            M.B (n + 1) ≫ M.chain.d (n + 2) (n + 1) =
              -(M.chain.d (n + 1) n ≫ M.B n) :=
          eq_neg_of_add_eq_zero_right (by simpa [add_comm] using hm)
        rw [cancel_epi
          (connesColumnIsoAt M (p + 1) (n + 1) (p + 1 + n + 1) (by omega)).hom]
        rw [← Category.assoc, ← Category.assoc]
        rw [cancel_mono
          (connesColumnIsoAt M p (n + 1) (p + 1 + n) (by omega)).inv]
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
        rw [hneg]
        simp [pow_succ]
      · have hjp : j = p := by omega
        subst j
        have hf : connesHorizontalF M p (p + 1) =
            (connesColumnIsoAt M (p + 1) 0 (p + 1) (by omega)).hom ≫
              ((-1 : ℤ) ^ (p + 1) • M.B 0) ≫
              (connesColumnIsoAt M p 1 (p + 1) (by omega)).inv := by
          simpa using connesHorizontalF_eq_at M p 0
        rw [hf]
        rw [connesHorizontalF_eq_zero M p p (by omega), comp_zero]
        have hd : (connesColumn M p).d (p + 1) p =
            (connesColumnIsoAt M p 1 (p + 1) (by omega)).hom ≫ M.chain.d 1 0 ≫
              (connesColumnIsoAt M p 0 p rfl).inv := by
          simpa using connesColumn_d_eq_at M p 0
        rw [hd]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← comp_zero,
          cancel_epi (connesColumnIsoAt M (p + 1) 0 (p + 1) (by omega)).hom]
        rw [← Category.assoc, ← zero_comp,
          cancel_mono (connesColumnIsoAt M p 0 p rfl).inv]
        simp only [Preadditive.zsmul_comp]
        rw [M.mixed_zero, smul_zero]
    · have hz := connesColumn_isZero M p j (by omega)
      exact hz.eq_of_tgt _ _

/-- Connes' first-quadrant double complex associated canonically to a mixed
complex.  Column `p` is the shifted copy of `M` beginning in row `p`; the
outer differential is the signed `B`-map above. -/
noncomputable def connesDoubleComplex (M : MixedComplex C) : FirstQuadrantDoubleComplex C :=
  ChainComplex.of (connesColumn M) (connesHorizontal M) (fun p => by
    ext q
    change (connesHorizontal M (p + 1)).f q ≫ (connesHorizontal M p).f q = 0
    by_cases hpq : p + 2 ≤ q
    · change connesHorizontalF M (p + 1) q ≫ connesHorizontalF M p q = 0
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hpq
      have hf₁ : connesHorizontalF M (p + 1) (p + 2 + n) =
          (connesColumnIsoAt M (p + 2) n (p + 2 + n) rfl).hom ≫
            ((-1 : ℤ) ^ (p + 2 + n) • M.B n) ≫
            (connesColumnIsoAt M (p + 1) (n + 1) (p + 2 + n) (by omega)).inv := by
        exact connesHorizontalF_eq_of_eq M (p + 1) n (p + 2 + n) (by omega)
      have hf₀ : connesHorizontalF M p (p + 2 + n) =
          (connesColumnIsoAt M (p + 1) (n + 1) (p + 2 + n) (by omega)).hom ≫
            ((-1 : ℤ) ^ (p + 2 + n) • M.B (n + 1)) ≫
            (connesColumnIsoAt M p (n + 2) (p + 2 + n) (by omega)).inv := by
        exact connesHorizontalF_eq_of_eq M p (n + 1) (p + 2 + n) (by omega)
      rw [hf₁, hf₀]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← comp_zero,
        cancel_epi (connesColumnIsoAt M (p + 2) n (p + 2 + n) rfl).hom]
      rw [← Category.assoc, ← zero_comp,
        cancel_mono (connesColumnIsoAt M p (n + 2) (p + 2 + n) (by omega)).inv]
      simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
        ← mul_smul]
      rw [M.B_sq n]
      simp
    · have hz := connesColumn_isZero M (p + 2) q (by omega)
      exact hz.eq_of_src _ _)

@[simp]
lemma connesDoubleComplex_d (M : MixedComplex C) (p : ℕ) :
    (connesDoubleComplex M).d (p + 1) p = connesHorizontal M p := by
  unfold connesDoubleComplex
  exact ChainComplex.of_d _ _ p

/-- Backwards-compatible name for the realized object.  The realization is no
longer a wrapper carrying caller-supplied construction data: it is the actual
canonical first-quadrant double complex. -/
abbrev ConnesDoubleComplexRealization (_M : MixedComplex C) := FirstQuadrantDoubleComplex C

/-- The canonical realization of Weibel Definition 9.8.2. -/
noncomputable def connesDoubleComplexRealization (M : MixedComplex C) :
    ConnesDoubleComplexRealization M :=
  connesDoubleComplex M

/-- Source-facing identification of bidegree `(p,q)` with `M_n` when
`q = p+n`. -/
noncomputable def connesDoubleComplexIsoAt (M : MixedComplex C) (p n q : ℕ)
    (h : p + n = q) : ((connesDoubleComplex M).X p).X q ≅ M.chain.X n := by
  change (connesColumn M p).X q ≅ M.chain.X n
  exact connesColumnIsoAt M p n q h

/-- Entries strictly above the diagonal vanish. -/
lemma connesDoubleComplex_isZero (M : MixedComplex C) (p q : ℕ) (hqp : q < p) :
    IsZero (((connesDoubleComplex M).X p).X q) := by
  change IsZero ((connesColumn M p).X q)
  exact connesColumn_isZero M p q hqp

/-- Under the source-facing identifications, the vertical differential is the
mixed-complex differential `b`. -/
lemma connesDoubleComplex_vertical (M : MixedComplex C) (p n : ℕ) :
    (connesDoubleComplexIsoAt M p (n + 1) (p + n + 1) (by omega)).hom ≫
        M.chain.d (n + 1) n =
      ((connesDoubleComplex M).X p).d (p + n + 1) (p + n) ≫
        (connesDoubleComplexIsoAt M p n (p + n) rfl).hom := by
  change (connesColumnIsoAt M p (n + 1) (p + n + 1) (by omega)).hom ≫
        M.chain.d (n + 1) n =
      (connesColumn M p).d (p + n + 1) (p + n) ≫
        (connesColumnIsoAt M p n (p + n) rfl).hom
  rw [connesColumn_d_eq_of_eq M p n (p + n + 1) (p + n) (by omega) rfl]
  simp

/-- Under the source-facing identifications, the horizontal differential is
`B`, with the parity sign required by the nested-chain-complex encoding. -/
lemma connesDoubleComplex_horizontal (M : MixedComplex C) (p n : ℕ) :
    (connesDoubleComplexIsoAt M (p + 1) n (p + 1 + n) rfl).hom ≫
        ((-1 : ℤ) ^ (p + 1 + n) • M.B n) =
      ((connesDoubleComplex M).d (p + 1) p).f (p + 1 + n) ≫
        (connesDoubleComplexIsoAt M p (n + 1) (p + 1 + n) (by omega)).hom := by
  rw [connesDoubleComplex_d M p]
  change (connesColumnIsoAt M (p + 1) n (p + 1 + n) rfl).hom ≫
        ((-1 : ℤ) ^ (p + 1 + n) • M.B n) =
      connesHorizontalF M p (p + 1 + n) ≫
        (connesColumnIsoAt M p (n + 1) (p + 1 + n) (by omega)).hom
  rw [connesHorizontalF_eq_at M p n]
  simp

end LeanCategories.Homological
