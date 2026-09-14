/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DoubleComplexFirstPages
public import LeanCategories.Homological.FilteredComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Column and row filtrations of a double complex

Weibel, *An Introduction to Homological Algebra* (1994), Definitions 5.6.1
and 5.6.2, pp. 141--144 (FC05-C05-U045, FC05-C05-U046).

For a first-quadrant double complex, the direct-sum total complex carries the
increasing column filtration `F_p Tot_n = ⊕_{i≤p} C_{i,n-i}` and, dually, the
increasing row filtration.  U045 below constructs the column filtration itself.
The associated-graded identifications, spectral-sequence pages, and convergence
are result-level content and are not asserted as part of that definition.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The associated graded complex of an increasing filtration on a
nonnegatively graded chain complex. -/
noncomputable def associatedGradedNat {K : ChainComplex C ℕ}
    (F : ChainComplexFiltration C (ComplexShape.down ℕ) K) (p : ℤ) :
    ChainComplex C ℕ :=
  cokernel (Subobject.ofLE (F.obj (p - 1)) (F.obj p) (F.monotone (by omega)))

/-- The total-degree fibers in a first-quadrant double complex are finite, so
the direct-sum total complex exists in every abelian category. -/
private def totalFiber (n : ℕ) :=
  (fun x : ℕ × ℕ => x.1 + x.2) ⁻¹' ({n} : Set ℕ)

private def totalFiberToFin (n : ℕ) : totalFiber n → Fin (n + 1) × Fin (n + 1) :=
  fun x =>
    (⟨x.1.1, by
      have hx : x.1.1 + x.1.2 = n := by simpa [totalFiber] using x.2
      omega⟩,
     ⟨x.1.2, by
      have hx : x.1.1 + x.1.2 = n := by simpa [totalFiber] using x.2
      omega⟩)

private theorem totalFiberToFin_injective (n : ℕ) : Function.Injective (totalFiberToFin n) := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)

private instance (n : ℕ) : Finite (totalFiber n) :=
  Finite.of_injective (totalFiberToFin n) (totalFiberToFin_injective n)


noncomputable instance firstQuadrantHasTotal (K : FirstQuadrantDoubleComplex C) :
    HomologicalComplex₂.HasTotal K (ComplexShape.down ℕ) := by
  intro n
  let _ : Finite (((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' ({n} : Set ℕ))) := by
    change Finite (totalFiber n)
    infer_instance
  infer_instance

def columnPrefixShape (p : ℕ) : ComplexShape (Fin (p + 1)) where
  Rel i j := (ComplexShape.down ℕ).Rel i.1 j.1
  next_eq h h' := Fin.ext ((ComplexShape.down ℕ).next_eq h h')
  prev_eq h h' := Fin.ext ((ComplexShape.down ℕ).prev_eq h h')

def columnPrefixEmbedding (p : ℕ) :
    (columnPrefixShape p).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun i => i.1)
    (fun _ _ h => Fin.ext h) (fun _ _ => Iff.rfl)

instance (p : ℕ) : (columnPrefixEmbedding p).IsTruncGE where
  rel' i j h := h
  mem_next {j k'} h := by
    refine ⟨⟨k', ?_⟩, rfl⟩
    change k' + 1 = j.1 at h
    have hj := j.2
    omega

lemma exists_columnPrefixEmbedding_iff (p i : ℕ) :
    (∃ k, (columnPrefixEmbedding p).f k = i) ↔ i ≤ p := by
  constructor
  · rintro ⟨k, rfl⟩
    exact Nat.le_of_lt_succ k.2
  · intro hi
    exact ⟨⟨i, by omega⟩, rfl⟩

noncomputable abbrev columnPrefix (K : FirstQuadrantDoubleComplex C) (p : ℕ) :
    FirstQuadrantDoubleComplex C :=
  K.stupidTrunc (columnPrefixEmbedding p)

noncomputable def columnPrefixInclusionF
    (K : FirstQuadrantDoubleComplex C) (p i' : ℕ) :
    (columnPrefix K p).X i' ⟶ K.X i' :=
  if hi' : ∃ i, (columnPrefixEmbedding p).f i = i' then
    (K.stupidTruncXIso (columnPrefixEmbedding p) hi'.choose_spec).hom
  else 0

lemma columnPrefixInclusionF_eq (K : FirstQuadrantDoubleComplex C) (p : ℕ)
    {i : Fin (p + 1)} {i' : ℕ} (hi : (columnPrefixEmbedding p).f i = i') :
    columnPrefixInclusionF K p i' =
      (K.stupidTruncXIso (columnPrefixEmbedding p) hi).hom := by
  have hi' : ∃ k, (columnPrefixEmbedding p).f k = i' := ⟨i, hi⟩
  have hki : hi'.choose = i := (columnPrefixEmbedding p).injective_f
    (hi'.choose_spec.trans hi.symm)
  simp only [columnPrefixInclusionF, dif_pos hi']
  subst hki
  rfl

noncomputable def columnPrefixInclusion (K : FirstQuadrantDoubleComplex C) (p : ℕ) :
    columnPrefix K p ⟶ K where
  f := columnPrefixInclusionF K p
  comm' i' j' hij := by
    by_cases hi' : ∃ i, (columnPrefixEmbedding p).f i = i'
    · obtain ⟨i, hi⟩ := hi'
      have hij' : (ComplexShape.down ℕ).Rel ((columnPrefixEmbedding p).f i) j' := by
        simpa [hi] using hij
      obtain ⟨j, hj⟩ := (columnPrefixEmbedding p).mem_next hij'
      rw [columnPrefixInclusionF_eq K p hi, columnPrefixInclusionF_eq K p hj]
      dsimp [columnPrefix, HomologicalComplex.stupidTrunc,
        HomologicalComplex.stupidTruncXIso]
      rw [(K.restriction (columnPrefixEmbedding p)).extend_d_eq
        (columnPrefixEmbedding p) hi hj]
      rw [K.restriction_d_eq (columnPrefixEmbedding p) hi hj]
      simp [HomologicalComplex.restrictionXIso]
    · exact (K.isZero_stupidTrunc_X (columnPrefixEmbedding p) i'
        (by simpa using hi')).eq_of_src _ _

noncomputable def columnPrefixRetractionF
    (K : FirstQuadrantDoubleComplex C) (p i j : ℕ) :
    (K.X i).X j ⟶ ((columnPrefix K p).X i).X j :=
  if hi : ∃ k, (columnPrefixEmbedding p).f k = i then
    (K.stupidTruncXIso (columnPrefixEmbedding p) hi.choose_spec).inv.f j
  else 0

lemma columnPrefixRetractionF_eq (K : FirstQuadrantDoubleComplex C) (p j : ℕ)
    {k : Fin (p + 1)} {i : ℕ} (hk : (columnPrefixEmbedding p).f k = i) :
    columnPrefixRetractionF K p i j =
      (K.stupidTruncXIso (columnPrefixEmbedding p) hk).inv.f j := by
  have hi : ∃ l, (columnPrefixEmbedding p).f l = i := ⟨k, hk⟩
  have hlk : hi.choose = k := (columnPrefixEmbedding p).injective_f
    (hi.choose_spec.trans hk.symm)
  simp only [columnPrefixRetractionF, dif_pos hi]
  subst hlk
  rfl

noncomputable def columnPrefixRetractionDegree
    (K : FirstQuadrantDoubleComplex C) (p n : ℕ) :
    (HomologicalComplex₂.total K (ComplexShape.down ℕ)).X n ⟶
      (HomologicalComplex₂.total (columnPrefix K p) (ComplexShape.down ℕ)).X n :=
  HomologicalComplex₂.totalDesc K (fun i j h =>
    columnPrefixRetractionF K p i j ≫
      HomologicalComplex₂.ιTotal (columnPrefix K p) (ComplexShape.down ℕ) i j n h)

lemma columnPrefixTotalMap_retraction
    (K : FirstQuadrantDoubleComplex C) (p n : ℕ) :
    (HomologicalComplex₂.total.map (columnPrefixInclusion K p) (ComplexShape.down ℕ)).f n ≫
        columnPrefixRetractionDegree K p n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
  by_cases hi : i ≤ p
  · let k : Fin (p + 1) := ⟨i, by omega⟩
    have hk : (columnPrefixEmbedding p).f k = i := rfl
    have hinc : (columnPrefixInclusion K p).f i =
        (K.stupidTruncXIso (columnPrefixEmbedding p) hk).hom :=
      columnPrefixInclusionF_eq K p hk
    rw [hinc]
    simp only [columnPrefixRetractionDegree]
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    rw [columnPrefixRetractionF_eq K p j hk]
    have hcancel :
        (K.stupidTruncXIso (columnPrefixEmbedding p) hk).hom.f j ≫
            (K.stupidTruncXIso (columnPrefixEmbedding p) hk).inv.f j = 𝟙 _ := by
      have hc := HomologicalComplex.congr_hom
        (K.stupidTruncXIso (columnPrefixEmbedding p) hk).hom_inv_id j
      change (K.stupidTruncXIso (columnPrefixEmbedding p) hk).hom.f j ≫
        (K.stupidTruncXIso (columnPrefixEmbedding p) hk).inv.f j = 𝟙 _ at hc
      exact hc
    rw [← Category.assoc, hcancel, Category.id_comp, Category.comp_id]
  · have hnot : ∀ k, (columnPrefixEmbedding p).f k ≠ i := by
      intro k hk
      have hle : i ≤ p := (exists_columnPrefixEmbedding_iff p i).1 ⟨k, hk⟩
      exact hi hle
    have hz : IsZero ((columnPrefix K p).X i) :=
      K.isZero_stupidTrunc_X (columnPrefixEmbedding p) i hnot
    exact ((HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero hz).eq_of_src _ _

noncomputable instance columnPrefixTotalMapMono
    (K : FirstQuadrantDoubleComplex C) (p : ℕ) :
    Mono (HomologicalComplex₂.total.map (columnPrefixInclusion K p) (ComplexShape.down ℕ)) :=
  HomologicalComplex.mono_of_mono_f _ (fun n => by
    let _ : IsSplitMono
        ((HomologicalComplex₂.total.map (columnPrefixInclusion K p)
          (ComplexShape.down ℕ)).f n) :=
      IsSplitMono.mk' ⟨columnPrefixRetractionDegree K p n,
        columnPrefixTotalMap_retraction K p n⟩
    infer_instance)

noncomputable instance columnPrefixInclusionComponentMono
    (K : FirstQuadrantDoubleComplex C) (p i : ℕ) :
    Mono ((columnPrefixInclusion K p).f i) := by
  by_cases hi : i ≤ p
  · let k : Fin (p + 1) := ⟨i, by omega⟩
    have hk : (columnPrefixEmbedding p).f k = i := rfl
    rw [show (columnPrefixInclusion K p).f i =
      (K.stupidTruncXIso (columnPrefixEmbedding p) hk).hom from
        columnPrefixInclusionF_eq K p hk]
    infer_instance
  · have hnot : ∀ k, (columnPrefixEmbedding p).f k ≠ i := by
      intro k hk
      exact hi ((exists_columnPrefixEmbedding_iff p i).1 ⟨k, hk⟩)
    exact (K.isZero_stupidTrunc_X (columnPrefixEmbedding p) i hnot).mono _

noncomputable def columnPrefixMapF (K : FirstQuadrantDoubleComplex C)
    {p q : ℕ} (hpq : p ≤ q) (i : ℕ) :
    (columnPrefix K p).X i ⟶ (columnPrefix K q).X i :=
  if hi : i ≤ p then
    let kp : Fin (p + 1) := ⟨i, by omega⟩
    let kq : Fin (q + 1) := ⟨i, by omega⟩
    (K.stupidTruncXIso (columnPrefixEmbedding p)
      (show (columnPrefixEmbedding p).f kp = i from rfl)).hom ≫
      (K.stupidTruncXIso (columnPrefixEmbedding q)
        (show (columnPrefixEmbedding q).f kq = i from rfl)).inv
  else 0

lemma columnPrefixMapF_comp_inclusion (K : FirstQuadrantDoubleComplex C)
    {p q : ℕ} (hpq : p ≤ q) (i : ℕ) :
    columnPrefixMapF K hpq i ≫ (columnPrefixInclusion K q).f i =
      (columnPrefixInclusion K p).f i := by
  by_cases hi : i ≤ p
  · let kp : Fin (p + 1) := ⟨i, by omega⟩
    let kq : Fin (q + 1) := ⟨i, by omega⟩
    have hkp : (columnPrefixEmbedding p).f kp = i := rfl
    have hkq : (columnPrefixEmbedding q).f kq = i := rfl
    rw [show (columnPrefixInclusion K p).f i =
      (K.stupidTruncXIso (columnPrefixEmbedding p) hkp).hom from
        columnPrefixInclusionF_eq K p hkp]
    rw [show (columnPrefixInclusion K q).f i =
      (K.stupidTruncXIso (columnPrefixEmbedding q) hkq).hom from
        columnPrefixInclusionF_eq K q hkq]
    simp [columnPrefixMapF, hi, kp, kq]
  · have hnot : ∀ k, (columnPrefixEmbedding p).f k ≠ i := by
      intro k hk
      exact hi ((exists_columnPrefixEmbedding_iff p i).1 ⟨k, hk⟩)
    exact (K.isZero_stupidTrunc_X (columnPrefixEmbedding p) i hnot).eq_of_src _ _

noncomputable def columnPrefixMap (K : FirstQuadrantDoubleComplex C)
    {p q : ℕ} (hpq : p ≤ q) : columnPrefix K p ⟶ columnPrefix K q where
  f := columnPrefixMapF K hpq
  comm' i j _ := by
    rw [← cancel_mono ((columnPrefixInclusion K q).f j)]
    rw [Category.assoc, ← (columnPrefixInclusion K q).comm i j]
    rw [← Category.assoc, columnPrefixMapF_comp_inclusion K hpq i]
    rw [Category.assoc, columnPrefixMapF_comp_inclusion K hpq j]
    exact (columnPrefixInclusion K p).comm i j

lemma columnPrefixMap_comp_inclusion (K : FirstQuadrantDoubleComplex C)
    {p q : ℕ} (hpq : p ≤ q) :
    columnPrefixMap K hpq ≫ columnPrefixInclusion K q = columnPrefixInclusion K p := by
  apply HomologicalComplex.hom_ext
  intro i
  exact columnPrefixMapF_comp_inclusion K hpq i

noncomputable def columnFiltrationLevelNat
    (K : FirstQuadrantDoubleComplex C) (p : ℕ) :
    Subobject (HomologicalComplex₂.total K (ComplexShape.down ℕ)) :=
  Subobject.mk (HomologicalComplex₂.total.map (columnPrefixInclusion K p) (ComplexShape.down ℕ))

lemma columnFiltrationLevelNat_mono (K : FirstQuadrantDoubleComplex C)
    {p q : ℕ} (hpq : p ≤ q) :
    columnFiltrationLevelNat K p ≤ columnFiltrationLevelNat K q := by
  apply Subobject.mk_le_mk_of_comm
    (HomologicalComplex₂.total.map (columnPrefixMap K hpq) (ComplexShape.down ℕ))
  rw [← HomologicalComplex₂.total.map_comp]
  rw [columnPrefixMap_comp_inclusion K hpq]

/-- Weibel's canonical column filtration on the direct-sum total complex,
`F_p Tot_n = ⊕_{i≤p} C_{i,n-i}` for `p ≥ 0`, and zero for `p < 0`.

Source: Weibel, Definition 5.6.1 (FC05-C05-U045). -/
noncomputable def columnFiltration (K : FirstQuadrantDoubleComplex C) :
    ChainComplexFiltration C (ComplexShape.down ℕ)
      (HomologicalComplex₂.total K (ComplexShape.down ℕ)) where
  obj p := if p < 0 then ⊥ else columnFiltrationLevelNat K p.toNat
  monotone := by
    intro p q hpq
    by_cases hp : p < 0
    · simp [hp]
    · have hq : ¬ q < 0 := by omega
      simp only [hp, hq, ↓reduceIte]
      apply columnFiltrationLevelNat_mono K
      omega


/-- The horizontal row complex `C_{*,q}` in a first-quadrant double complex. -/
noncomputable def horizontalRowComplex
    (K : FirstQuadrantDoubleComplex C) (q : ℕ) : ChainComplex C ℕ :=
  ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K

/-- A realization of Weibel's row filtration on the direct-sum total complex. -/
structure RowFiltrationRealization
    (K : FirstQuadrantDoubleComplex C)
    [HomologicalComplex₂.HasTotal K (ComplexShape.down ℕ)] where
  /-- The increasing filtration on `Tot K`. -/
  filtration :
    ChainComplexFiltration C (ComplexShape.down ℕ)
      (HomologicalComplex₂.total K (ComplexShape.down ℕ))
  /-- Negative row filtration is zero. -/
  negative_isZero : ∀ (p : ℤ), p < 0 → ∀ n : ℕ,
    IsZero (filtration.degreeObject p n)
  /-- The associated graded object in filtration degree `p` is the `p`th
  row, with total degree `p+q`. -/
  graded_iso : ∀ (p q : ℕ),
    (associatedGradedNat filtration (p : ℤ)).X (p + q) ≅ (K.X q).X p


end LeanCategories.Homological
