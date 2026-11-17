/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.Cusps
public import LeanCategories.ForMathlib.CosetTable
public import LeanCategories.ForMathlib.ModularCuspsFiniteIndex

/-!
# Cusps of a finite-index subgroup of `GL(2, ℤ)`

A cusp of a subgroup `𝒢 ≤ GL(2, ℝ)` is a fixed point of a parabolic element (`IsCusp`), and
`CuspOrbits 𝒢` is the set of `𝒢`-orbits of its cusps
(`Mathlib/NumberTheory/ModularForms/Cusps.lean`). The module
`LeanCategories.ForMathlib.ModularCuspsFiniteIndex` proves the finiteness of the cusps of a
finite-index subgroup of `SL(2, ℤ)` and the bound `Nat.card (CuspOrbits Γ) ≤ Γ.index`, from the
surjection `cosetToCuspOrbit` of Mathlib.

This file removes the `SL(2, ℤ)` restriction. For `Γ ≤ GL(2, ℤ)` of finite index, the image of `Γ`
in `GL(2, ℝ)` (`gl2Image`) has finitely many cusp orbits, at most `Γ.index` of them
(`finite_cuspOrbits_of_finiteIndex`, `natCard_cuspOrbits_le_index`).

## The route

The determinant-one part `Γ.detOnePart = Γ ⊓ SL(2, ℤ)` is the intersection of `Γ` with the modular
group. Three facts about it are proved here rather than assumed:

* it has finite relative index in `Γ` (`detOnePart_relIndex_ne_zero`), because the determinant of an
  invertible integer matrix is a unit of `ℤ`, so the quotient `Γ ⧸ Γ.detOnePart` embeds in `ℤˣ` —
  the relative index is at most two, and is not a hypothesis;
* its inverse image in `SL(2, ℤ)` (`sl2Part`) has index at most `Γ.index` (`sl2Part_index_le`): the
  injection of the `SL(2, ℤ)`-cosets of `Γ` into the `GL(2, ℤ)`-cosets of `Γ`, through
  `Subgroup.index_comap` and `Subgroup.relIndex_le_of_le_right`, not a commensurability assumption;
* hence it is `Mathlib.IsArithmetic` in `GL(2, ℝ)`, through `Subgroup.isArithmetic_iff_finiteIndex`.

`CuspOrbits.map_surjective` then carries the `SL(2, ℤ)`-bound of
`natCard_cuspOrbits_le_index` (`LeanCategories.ForMathlib.ModularCuspsFiniteIndex`) along the
inclusion `Γ.detOnePart ≤ Γ` to the image of `Γ` in `GL(2, ℝ)`.

Nothing here is assumed arithmetic or cusp-finite: both are proved from the finite-index hypothesis.
The real parabolic cusp semantics is Mathlib's (`IsCusp`, `CuspOrbits`); the image `gl2Image Γ` is a
subgroup of `GL(2, ℝ)`, and its cusp orbits are those of its own parabolic elements.

## The certified coset table

`natCard_cuspOrbits_le_of_cosetTable` states the same bound with `k` supplied by a certified
transitive coset table for `Γ` (`LeanCategories.ForMathlib.CosetTable`): a certificate on `k` points
gives `Γ.index ≤ k` and hence `Nat.card (CuspOrbits (gl2Image Γ)) ≤ k`, without naming an element of
`Γ`.

## Search record (LC-09)

`scripts/formalization_corpus.py search` at the manifest head `9fdc1827` under
`cusp orbits finite index subgroup general linear group`: the only hit is TauCeti
`GroupTheory/DoubleCoset/Orbits.lean`, the double-coset orbit dictionary, which is not this theorem.
The Mathlib owners used are `Mathlib/NumberTheory/ModularForms/Cusps.lean` (`CuspOrbits.map`,
`map_surjective`), `.../ArithmeticSubgroups.lean` (`detOnePart`, `isArithmetic_iff_finiteIndex`) and
`Mathlib/GroupTheory/Index.lean` (`index_comap`, `relIndex_le_of_le_right`); none of them contains
the `GL(2, ℤ)` statement, whose missing input is the determinant-one index bound proved below.
-/

@[expose] public section

namespace LeanCategories.ForMathlib

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

variable {Γ : Subgroup (GL (Fin 2) ℤ)}

/-- The coefficient map `GL(2, ℤ) → GL(2, ℝ)`. -/
def gl2ToReal : GL (Fin 2) ℤ →* GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℤ ℝ)

/-- The image of a subgroup `Γ ≤ GL(2, ℤ)` in `GL(2, ℝ)`. -/
def gl2Image (Γ : Subgroup (GL (Fin 2) ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  Γ.map gl2ToReal

@[simp]
theorem gl2Image_def (Γ : Subgroup (GL (Fin 2) ℤ)) : gl2Image Γ = Γ.map gl2ToReal := rfl

theorem mem_gl2Image {Γ : Subgroup (GL (Fin 2) ℤ)} {x : GL (Fin 2) ℝ} :
    x ∈ gl2Image Γ ↔ ∃ g ∈ Γ, gl2ToReal g = x :=
  Iff.rfl

theorem gl2ToReal_injective : Function.Injective gl2ToReal := by
  intro A B h
  ext i j
  have h' : (algebraMap ℤ ℝ) (A i j) = (algebraMap ℤ ℝ) (B i j) := by
    simpa [gl2ToReal] using congrArg (fun M : GL (Fin 2) ℝ => (M : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  exact Int.cast_injective h'

theorem gl2ToReal_comp_toGL : gl2ToReal.comp toGL = mapGL (R := ℤ) ℝ := by
  ext g i j
  simp [gl2ToReal]

/-! ### The `SL(2, ℤ)`-part of a subgroup of `GL(2, ℤ)` -/

/-- The inverse image of `Γ` in `SL(2, ℤ)`: the determinant-one elements of `Γ`. -/
def sl2Part (Γ : Subgroup (GL (Fin 2) ℤ)) : Subgroup SL(2, ℤ) :=
  Γ.comap toGL

theorem sl2Part_map_toGL (Γ : Subgroup (GL (Fin 2) ℤ)) :
    (sl2Part Γ).map toGL = Γ.detOnePart := by
  rw [sl2Part, Subgroup.map_comap_eq, Subgroup.detOnePart, inf_comm]

theorem detOnePart_relIndex_ne_zero (Γ : Subgroup (GL (Fin 2) ℤ)) :
    Γ.detOnePart.relIndex Γ ≠ 0 := by
  have hker : ((GeneralLinearGroup.det (n := Fin 2) (R := ℤ)).comp Γ.subtype).ker
      = Γ.detOnePart.subgroupOf Γ := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_detOnePart]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact Nat.card_ne_zero.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩

theorem detOnePart_index_ne_zero (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    Γ.detOnePart.index ≠ 0 := by
  have h := Subgroup.relIndex_mul_index (Subgroup.detOnePart_le Γ)
  rw [← h]
  exact mul_ne_zero (detOnePart_relIndex_ne_zero Γ) (Subgroup.index_ne_zero)

/-- The `SL(2, ℤ)`-part of `Γ` has index at most the index of `Γ`: the `SL(2, ℤ)`-cosets of `Γ`
inject into the `GL(2, ℤ)`-cosets of `Γ`. -/
theorem sl2Part_index_le (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    (sl2Part Γ).index ≤ Γ.index := by
  rw [sl2Part, Subgroup.index_comap]
  refine (Subgroup.relIndex_le_of_le_right (H := Γ) (K := toGL.range) (L := ⊤) le_top ?_).trans_eq
    (Subgroup.relIndex_top_right Γ)
  rw [Subgroup.relIndex_top_right]
  exact Subgroup.index_ne_zero

/-- `SL(2, ℤ)`, as the subgroup of `GL(2, ℤ)` of matrices of determinant one. -/
def sl2ZImage : Subgroup (GL (Fin 2) ℤ) :=
  toGL.range

theorem sl2ZImage_eq_ker :
    sl2ZImage = (GeneralLinearGroup.det (n := Fin 2) (R := ℤ)).ker := by
  ext g
  rw [sl2ZImage, MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    exact SpecialLinearGroup.coeToGL_det x
  · intro hg
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) ℤ), ?_⟩, Units.ext rfl⟩
    rw [← GeneralLinearGroup.val_det_apply, hg, Units.val_one]

theorem sl2ZImage_index_ne_zero : sl2ZImage.index ≠ 0 := by
  rw [sl2ZImage_eq_ker, Subgroup.index_ker]
  exact Nat.card_ne_zero.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩

instance sl2ZImage_finiteIndex : sl2ZImage.FiniteIndex :=
  ⟨sl2ZImage_index_ne_zero⟩

/-- **The modular group is the index-two determinant-one subgroup**: the determinant of an
invertible integer matrix is a unit of `ℤ`, and `ℤ` has two of them. -/
theorem sl2ZImage_index_le_two : sl2ZImage.index ≤ 2 := by
  rw [sl2ZImage_eq_ker, Subgroup.index_ker]
  refine (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans ?_
  simp

instance sl2Part_finiteIndex (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    (sl2Part Γ).FiniteIndex := by
  have hidx := Subgroup.index_map_of_injective (sl2Part Γ)
    (f := toGL (n := Fin 2) (R := ℤ)) SpecialLinearGroup.toGL_injective
  rw [sl2Part_map_toGL] at hidx
  refine ⟨fun h => ?_⟩
  have h0 := detOnePart_index_ne_zero Γ
  rw [hidx, h] at h0
  simp at h0

theorem sl2Part_map_real (Γ : Subgroup (GL (Fin 2) ℤ)) :
    (sl2Part Γ).map (mapGL (R := ℤ) ℝ) = Γ.detOnePart.map gl2ToReal := by
  rw [← gl2ToReal_comp_toGL, ← Subgroup.map_map, sl2Part_map_toGL]

theorem sl2Part_le_gl2Image (Γ : Subgroup (GL (Fin 2) ℤ)) :
    (sl2Part Γ).map (mapGL (R := ℤ) ℝ) ≤ gl2Image Γ := by
  rw [sl2Part_map_real, gl2Image_def]
  exact Subgroup.map_mono (Subgroup.detOnePart_le Γ)

instance sl2Part_isFiniteRelIndex (Γ : Subgroup (GL (Fin 2) ℤ)) :
    ((sl2Part Γ).map (mapGL (R := ℤ) ℝ)).IsFiniteRelIndex (gl2Image Γ) :=
  ⟨by
    rw [sl2Part_map_real, gl2Image_def,
      Subgroup.relIndex_map_map_of_injective _ _ gl2ToReal_injective]
    exact detOnePart_relIndex_ne_zero Γ⟩

/-! ### The cusp bound for `GL(2, ℤ)` -/

/-- **A finite-index subgroup of `GL(2, ℤ)` has finitely many cusps.** -/
theorem finite_cuspOrbits_of_finiteIndex_GL2 (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    Finite (CuspOrbits (gl2Image Γ)) := by
  exact Finite.of_surjective _ (CuspOrbits.map_surjective (sl2Part_le_gl2Image Γ))

/-- **A finite-index subgroup of `GL(2, ℤ)` has at most its index of cusps.** -/
theorem natCard_cuspOrbits_le_index_GL2 (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    Nat.card (CuspOrbits (gl2Image Γ)) ≤ Γ.index := by
  calc Nat.card (CuspOrbits (gl2Image Γ))
      ≤ Nat.card (CuspOrbits ((sl2Part Γ).map (mapGL (R := ℤ) ℝ))) :=
        Nat.card_le_card_of_surjective _
          (CuspOrbits.map_surjective (sl2Part_le_gl2Image Γ))
    _ ≤ (sl2Part Γ).index := natCard_cuspOrbits_le_index (sl2Part Γ)
    _ ≤ Γ.index := sl2Part_index_le Γ

/-- **The full modular group over `ℤ` has at most one cusp.** -/
theorem natCard_cuspOrbits_top_le_one :
    Nat.card (CuspOrbits (gl2Image ⊤)) ≤ 1 := by
  have h := natCard_cuspOrbits_le_index_GL2 (⊤ : Subgroup (GL (Fin 2) ℤ))
  simpa using h

/-- **`SL(2, ℤ)` has at most two cusps**, through its index in `GL(2, ℤ)`. -/
theorem natCard_cuspOrbits_sl2Z_le_two :
    Nat.card (CuspOrbits (gl2Image sl2ZImage)) ≤ 2 :=
  (natCard_cuspOrbits_le_index_GL2 sl2ZImage).trans sl2ZImage_index_le_two

/-- **A certified transitive coset table bounds the cusps of a subgroup of `GL(2, ℤ)`.** If the
generators `g` generate `GL(2, ℤ)`, the relators `rels` hold for them, the words `stab` lie in `Γ`,
and the table on `k` points carries a deduction certificate, then `Γ` has at most `k` cusp orbits in
`GL(2, ℝ)` — through `Γ.index ≤ k` (`LeanCategories.ForMathlib.CosetTable`) and
`natCard_cuspOrbits_le_index_GL2`. -/
theorem natCard_cuspOrbits_le_of_cosetTable {m k : ℕ} {T : CosetTable m k}
    {g : Fin m → GL (Fin 2) ℤ} {rels stab : List (List (Fin m))}
    {cert : List (Fin k × List (Fin m))} {Γ : Subgroup (GL (Fin 2) ℤ)}
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ Γ) :
    Nat.card (CuspOrbits (gl2Image Γ)) ≤ k :=
  @natCard_cuspOrbits_le_index_GL2 Γ (T.finiteIndex hg hT hrels hstab) |>.trans
    (T.index_le hg hT hrels hstab)

/-- **A certified coset table in `SL(2, ℤ)` bounds the cusps of its image in `GL(2, ℤ)`.** The
generators `S` and `T` of `SpecialLinearGroup.SL2Z_generators` with a certificate on `k` points give
`H.index ≤ k` (`LeanCategories.ForMathlib.CosetTable`), and the image of `H` in `GL(2, ℤ)` has index
at most `2 * k` (`sl2ZImage_index_le_two`); the cusp bound follows from
`natCard_cuspOrbits_le_index_GL2`. -/
theorem natCard_cuspOrbits_le_of_cosetTable_sl2 {m k : ℕ} {T : CosetTable m k}
    {g : Fin m → SL(2, ℤ)} {rels stab : List (List (Fin m))}
    {cert : List (Fin k × List (Fin m))} {H : Subgroup SL(2, ℤ)}
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) :
    Nat.card (CuspOrbits (gl2Image (H.map toGL))) ≤ 2 * k := by
  have hfin : H.FiniteIndex := T.finiteIndex hg hT hrels hstab
  have hmap : (H.map toGL).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_map_of_injective H (f := toGL (n := Fin 2) (R := ℤ))
      SpecialLinearGroup.toGL_injective]
    exact mul_ne_zero hfin.index_ne_zero sl2ZImage_index_ne_zero
  refine (@natCard_cuspOrbits_le_index_GL2 (H.map toGL) hmap).trans ?_
  rw [Subgroup.index_map_of_injective H (f := toGL (n := Fin 2) (R := ℤ))
    SpecialLinearGroup.toGL_injective]
  calc H.index * sl2ZImage.index ≤ k * 2 :=
        Nat.mul_le_mul (T.index_le hg hT hrels hstab) sl2ZImage_index_le_two
    _ = 2 * k := by ring

end LeanCategories.ForMathlib
