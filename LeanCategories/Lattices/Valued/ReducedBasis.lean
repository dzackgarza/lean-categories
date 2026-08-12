/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ReductionStep
public import LeanCategories.Lattices.Valued.Standard

/-!
# Reduced bases and finiteness of the class set

`ClassFiniteness.lean` bounds the shortest vector, `Reduction.lean` builds the cleared projection
and the size reduction, and `ReductionStep.lean` packages the projected lattice with its Gram
determinant. This file runs the rank induction those three prepare, and reads finiteness of the
class set of a genus off the result.

## From the projected lattice back to the ambient one

`exists_ambientFamily` turns a basis of `projectedLattice x` into a family `z` of ambient vectors
together with lifts `w` under the cleared projection. It supplies at one stroke the four
hypotheses `liftBasis`, `isPositiveDefinite_projectedLattice` and `pairing_mul_det_gramFamily`
take: linear independence, the span, the lifting property and the Gram matrix. With it,
`rank_projectedLattice` says the projected lattice has rank one less.

## The induction

`exists_reduced_basis` is the rank induction. Its hypothesis is a determinant *bound* `|det| ≤ D`,
never a fixed determinant: over `ℝ` or `ℚ` the conclusion is false, since `diag (ε, d / ε)` is
reduced of fixed determinant with unbounded entries. Integrality is what excludes this, through
the lower bound `1` on the value of a nonzero vector, and the induction stays inside the integral
lattices to keep it.

One step splits off a shortest vector `x` of value `m`. Minkowski's bound and `1 ≤ det ≤ D` give
`m ≤ n * D`. The Gram determinant of the projected lattice is `m ^ (2 * (n - 1))` times the
determinant of `L` after cancelling one factor `m`; since `1 ≤ m` that determinant is at most
`projectedDetBound`, so the induction hypothesis applies to it. Its reduced basis transfers back
to lifts `v i`, size reduced so that `2 * |b(x, v i)| ≤ m`, and

  `b(z i, z j) = m * (m * b(v i, v j) - b(x, v i) * b(x, v j))`

turns a bound on the projected entries into `|b(v i, v j)| ≤ B' + m`. The entry bound
`reducedEntryBound` is the resulting recursion.

## Finiteness

`finite_isometryClasses_of_bounded` combines the reduced basis with `finite_boundedGramMatrices`.
A reduced basis presents its lattice as `finiteLatticeOfGramMatrix` of an integer matrix with
bounded entries, by `isoFiniteLatticeOfGramMatrix`, so the isometry classes of rank `n` and
determinant at most `D` are the image of a finite set of matrices.

`genus_finite` follows: `rank_eq_of_sameGenus`, `signature_eq_of_sameGenus` and
`determinant_eq_of_sameGenus` place a whole genus of a positive definite lattice inside one such
bounded family.
-/

@[expose] public section

noncomputable section

open CategoryTheory Matrix
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

variable (L : FiniteProjectiveLatticeCat ℤ ℤ)

section Determinant

/-- Reindexing a basis leaves the Gram determinant unchanged. -/
theorem determinant_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (b : Module.Basis ι ℤ L.obj.obj.carrier) (eqv : ι ≃ κ) :
    determinant L.obj (b.reindex eqv) = determinant L.obj b := by
  have hsub : gramMatrix L.obj (b.reindex eqv) =
      (gramMatrix L.obj b).submatrix eqv.symm eqv.symm := by
    ext i j
    simp [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
  rw [determinant, hsub, Matrix.det_submatrix_equiv_self, determinant]

/-- **The Gram determinant of a positive definite lattice is a lattice invariant.** Two bases
give determinants associated in `ℤ`, hence equal up to sign, and both are positive. The index
types need not agree. -/
theorem determinant_eq_determinant (hL : IsPositiveDefiniteLattice L) {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι ℤ L.obj.obj.carrier)
    (c : Module.Basis κ ℤ L.obj.obj.carrier) :
    determinant L.obj c = determinant L.obj b := by
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [← L.rank_eq_card_basis b, ← L.rank_eq_card_basis c]
  obtain ⟨eqv⟩ := Fintype.card_eq.mp hcard
  have hassoc := determinant_associated L.obj (b.reindex eqv) c
  rw [L.determinant_reindex b eqv] at hassoc
  have hb := L.determinant_pos hL b
  have hc := L.determinant_pos hL c
  rcases Int.associated_iff.mp hassoc with h | h
  · exact h.symm
  · omega

end Determinant

section Bridge

variable {L}

/-- The pairing of two cleared projections. Specialising `u = v` recovers
`pairing_scaledProjection_self`. -/
theorem pairing_scaledProjection_pairing (x u v : L.obj.obj.carrier) :
    L.obj.obj.pairing (L.scaledProjection x u) (L.scaledProjection x v) =
      L.obj.obj.pairing x x *
        (L.obj.obj.pairing x x * L.obj.obj.pairing u v -
          L.obj.obj.pairing x u * L.obj.obj.pairing x v) := by
  have hu : L.obj.obj.pairing u x = L.obj.obj.pairing x u := L.obj.property.2 u x
  simp only [scaledProjection_apply, L.pairing_sub_left, L.pairing_sub_right,
    BilinModuleCat.pairing_zsmul_left, BilinModuleCat.pairing_zsmul_right, zsmul_eq_mul,
    Int.cast_id, hu]
  ring

/-- **A basis of the projected lattice becomes an ambient family.** The four hypotheses that
`liftBasis`, `isPositiveDefinite_projectedLattice` and `pairing_mul_det_gramFamily` take are all
explicit arguments, so a single transfer supplies them at once. -/
theorem exists_ambientFamily {x : L.obj.obj.carrier} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bz : Module.Basis ι ℤ (L.projectedLattice x).obj.obj.carrier) :
    ∃ z w : ι → L.obj.obj.carrier,
      LinearIndependent ℤ z ∧
        Submodule.span ℤ (Set.range z) = L.projectedSubmodule x ∧
        (∀ i, L.scaledProjection x (w i) = z i) ∧
        gramMatrix (L.projectedLattice x).obj bz = L.gramFamily z := by
  classical
  let inc : (L.projectedLattice x).obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier :=
    (L.projectedSubmodule x).subtype
  have hker : LinearMap.ker inc = ⊥ := Submodule.ker_subtype _
  set z : ι → L.obj.obj.carrier := fun i ↦ inc (bz i) with hz
  have hzind : LinearIndependent ℤ z := bz.linearIndependent.map' inc hker
  have hzspan : Submodule.span ℤ (Set.range z) = L.projectedSubmodule x := by
    rw [hz, Set.range_comp' inc bz, ← Submodule.map_span, bz.span_eq, Submodule.map_top]
    exact Submodule.range_subtype _
  have hmem : ∀ i, ∃ v, L.scaledProjection x v = z i := by
    intro i
    have : z i ∈ L.projectedSubmodule x :=
      hzspan ▸ Submodule.subset_span (Set.mem_range_self i)
    exact this
  choose w hw using hmem
  refine ⟨z, w, hzind, hzspan, hw, ?_⟩
  ext i j
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply, gramFamily, Matrix.of_apply]
  exact projectedLattice_pairing x (bz i) (bz j)

/-- **The projected lattice has rank one less.** The lifted basis of `L` is indexed by one extra
point. -/
theorem rank_projectedLattice (hL : IsPositiveDefiniteLattice L) {x : L.obj.obj.carrier}
    (hx : L.IsMinimalVector x) : (L.projectedLattice x).rank + 1 = L.rank := by
  classical
  letI : Module.Finite ℤ (L.projectedLattice x).obj.obj.carrier := (L.projectedLattice x).property
  letI : Module.Free ℤ (L.projectedLattice x).obj.obj.carrier :=
    (L.projectedLattice x).carrier_free
  set bz := Module.Free.chooseBasis ℤ (L.projectedLattice x).obj.obj.carrier with hbz
  obtain ⟨z, w, hzind, hzspan, hw, -⟩ := exists_ambientFamily bz
  rw [L.rank_eq_card_basis (L.liftBasis z w hL hx hzind hzspan hw),
    (L.projectedLattice x).rank_eq_card_basis bz, Fintype.card_sum]
  simp [Nat.add_comm]

end Bridge

end FiniteProjectiveLatticeCat

section Bounds

/-- The determinant bound inherited by the projected lattice of a rank `n + 1` lattice whose own
Gram determinant is at most `D`. The shortest vector has value at most `(n + 1) * D`, and the
projected Gram determinant is that value to the power `2 * n` times the determinant of `L`. -/
def projectedDetBound (n : ℕ) (D : ℤ) : ℤ := (((n : ℤ) + 1) * D) ^ (2 * n) * D

/-- **The entry bound of a reduced basis.** Splitting off a shortest vector adds `(n + 1) * D` to
the entry bound of the projected lattice, whose determinant bound is `projectedDetBound`. -/
def reducedEntryBound : ℕ → ℤ → ℤ
  | 0, _ => 0
  | n + 1, D => reducedEntryBound n (projectedDetBound n D) + ((n : ℤ) + 1) * D

@[simp]
theorem reducedEntryBound_zero (D : ℤ) : reducedEntryBound 0 D = 0 := rfl

@[simp]
theorem reducedEntryBound_succ (n : ℕ) (D : ℤ) :
    reducedEntryBound (n + 1) D =
      reducedEntryBound n (projectedDetBound n D) + ((n : ℤ) + 1) * D := rfl

/-- The inherited determinant bound stays at least one. -/
theorem one_le_projectedDetBound (n : ℕ) {D : ℤ} (hD : 1 ≤ D) : 1 ≤ projectedDetBound n D := by
  have hbase : 1 ≤ ((n : ℤ) + 1) * D := by
    have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    nlinarith
  have hpow : 1 ≤ (((n : ℤ) + 1) * D) ^ (2 * n) := one_le_pow₀ hbase
  rw [projectedDetBound]
  nlinarith

/-- The entry bound is nonnegative. -/
theorem reducedEntryBound_nonneg (n : ℕ) {D : ℤ} (hD : 1 ≤ D) : 0 ≤ reducedEntryBound n D := by
  induction n generalizing D with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have := ih (one_le_projectedDetBound n hD)
    rw [reducedEntryBound_succ]
    nlinarith

end Bounds

namespace FiniteProjectiveLatticeCat

variable (L : FiniteProjectiveLatticeCat ℤ ℤ)

/-- **The shortest vector is bounded by the rank times the determinant bound.** Minkowski's bound
gives `n * d ^ (1 / n)`, and integrality forces `1 ≤ d ≤ D`, so `d ^ (1 / n) ≤ D`. -/
theorem isMinimalVector_pairing_le (hL : IsPositiveDefiniteLattice L) {n : ℕ} {D : ℤ}
    (b : Module.Basis (Fin (n + 1)) ℤ L.obj.obj.carrier) (hD : determinant L.obj b ≤ D)
    {x : L.obj.obj.carrier} (hx : L.IsMinimalVector x) :
    L.obj.obj.pairing x x ≤ ((n : ℤ) + 1) * D := by
  have hrank : L.rank = n + 1 := by rw [L.rank_eq_card_basis b, Fintype.card_fin]
  have hdet1 : 1 ≤ determinant L.obj b := L.determinant_pos hL b
  obtain ⟨y, hy0, hyle⟩ := L.exists_ne_zero_pairing_le hL b (by omega)
  have hdetR : (1 : ℝ) ≤ ((determinant L.obj b : ℤ) : ℝ) := by exact_mod_cast hdet1
  have hrpow : ((determinant L.obj b : ℤ) : ℝ) ^ ((L.rank : ℝ)⁻¹) ≤
      ((determinant L.obj b : ℤ) : ℝ) := by
    have hle : (L.rank : ℝ)⁻¹ ≤ 1 := by
      rw [hrank]
      push_cast
      rw [inv_le_one_iff₀]
      right
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((determinant L.obj b : ℤ) : ℝ) ^ ((L.rank : ℝ)⁻¹)
        ≤ ((determinant L.obj b : ℤ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hdetR hle
      _ = ((determinant L.obj b : ℤ) : ℝ) := Real.rpow_one _
  have hDR : ((determinant L.obj b : ℤ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hyR : ((L.obj.obj.pairing y y : ℤ) : ℝ) ≤ ((n : ℝ) + 1) * (D : ℝ) := by
    refine hyle.trans ?_
    rw [hrank] at hrpow ⊢
    push_cast at hrpow ⊢
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact mul_le_mul_of_nonneg_left (hrpow.trans hDR) hpos
  have hyZ : L.obj.obj.pairing y y ≤ ((n : ℤ) + 1) * D := by exact_mod_cast hyR
  exact (hx.2 y hy0).trans hyZ

end FiniteProjectiveLatticeCat

/-- **Reduced bases exist.** A positive definite integral lattice of rank `n` whose Gram
determinant is at most `D` has a basis all of whose Gram entries are at most
`reducedEntryBound n D` in absolute value.

The induction splits off a shortest vector `x` and passes to the projected lattice, which has
rank one less and Gram determinant at most `projectedDetBound n D`. A reduced basis there lifts
to lattice vectors `v i` with `b(x, v i)` size reduced, and `b(x,x) * (b(x,x) * b(v i, v j) -
b(x, v i) * b(x, v j))` is the projected Gram entry, which bounds `b(v i, v j)`.

The hypothesis is a determinant *bound*, not a fixed determinant: over `ℝ` or `ℚ` the statement
is false, since `diag (ε, d / ε)` is reduced with unbounded entries and fixed determinant. What
rules that out is integrality, which forces `1 ≤ b(x,x)`. -/
theorem exists_reduced_basis : ∀ (n : ℕ) (D : ℤ) (L : FiniteProjectiveLatticeCat ℤ ℤ),
    IsPositiveDefiniteLattice L → ∀ b : Module.Basis (Fin n) ℤ L.obj.obj.carrier,
    determinant L.obj b ≤ D →
    ∃ c : Module.Basis (Fin n) ℤ L.obj.obj.carrier,
      ∀ i j, |L.obj.obj.pairing (c i) (c j)| ≤ reducedEntryBound n D := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ b _
    exact ⟨b, fun i ↦ i.elim0⟩
  | succ n ih =>
    intro D L hL b hD
    classical
    have hdet1 : 1 ≤ determinant L.obj b := L.determinant_pos hL b
    have hD1 : 1 ≤ D := le_trans hdet1 hD
    have hrank : L.rank = n + 1 := by rw [L.rank_eq_card_basis b, Fintype.card_fin]
    obtain ⟨x, hx⟩ := L.exists_isMinimalVector hL (by omega)
    have hm1 : 1 ≤ L.obj.obj.pairing x x := L.pairing_self_pos hL hx.1
    have hmle : L.obj.obj.pairing x x ≤ ((n : ℤ) + 1) * D :=
      L.isMinimalVector_pairing_le hL b hD hx
    letI : Module.Finite ℤ (L.projectedLattice x).obj.obj.carrier :=
      (L.projectedLattice x).property
    letI : Module.Free ℤ (L.projectedLattice x).obj.obj.carrier :=
      (L.projectedLattice x).carrier_free
    have hNrank : Module.finrank ℤ (L.projectedLattice x).obj.obj.carrier = n := by
      have h := L.rank_projectedLattice hL hx
      rw [hrank] at h
      have hn : (L.projectedLattice x).rank = n := by omega
      exact hn
    set bz : Module.Basis (Fin n) ℤ (L.projectedLattice x).obj.obj.carrier :=
      Module.finBasisOfFinrankEq ℤ _ hNrank with hbz
    obtain ⟨z₀, w₀, hz₀ind, hz₀span, hw₀, hgram₀⟩ :=
      FiniteProjectiveLatticeCat.exists_ambientFamily bz
    set e₀ := L.liftBasis z₀ w₀ hL hx hz₀ind hz₀span hw₀ with he₀
    have hex₀ : e₀ (Sum.inl ()) = x := by simp [he₀]
    have hew₀ : ∀ i, e₀ (Sum.inr i) = w₀ i := fun i ↦ by simp [he₀]
    have hNpos : IsPositiveDefiniteLattice (L.projectedLattice x) :=
      L.isPositiveDefinite_projectedLattice hL hx.1 hw₀ e₀ hex₀ hew₀ bz hgram₀
    -- the determinant of the projected lattice
    have hkey := L.pairing_mul_det_gramFamily z₀ w₀ hw₀ e₀ hex₀ hew₀
    rw [Fintype.card_fin, L.determinant_eq_determinant hL b e₀] at hkey
    have hdetN : determinant (L.projectedLattice x).obj bz = (L.gramFamily z₀).det := by
      rw [determinant, hgram₀]
    have hdetN1 : 1 ≤ determinant (L.projectedLattice x).obj bz :=
      (L.projectedLattice x).determinant_pos hNpos bz
    have hDN : determinant (L.projectedLattice x).obj bz ≤ projectedDetBound n D := by
      rw [hdetN] at hdetN1 ⊢
      have hstep : (L.gramFamily z₀).det ≤
          L.obj.obj.pairing x x * (L.gramFamily z₀).det := by nlinarith
      refine hstep.trans ?_
      rw [hkey, projectedDetBound]
      refine mul_le_mul (pow_le_pow_left₀ (by omega) hmle _) hD (by omega)
        (pow_nonneg (by nlinarith [Int.natCast_nonneg n]) _)
    obtain ⟨c', hc'⟩ := ih (projectedDetBound n D) (L.projectedLattice x) hNpos bz hDN
    -- transfer the reduced basis of the projected lattice back, and size reduce the lifts
    obtain ⟨z, w, hzind, hzspan, hw, hgram⟩ :=
      FiniteProjectiveLatticeCat.exists_ambientFamily c'
    have hsize : ∀ i, ∃ u : L.obj.obj.carrier, L.scaledProjection x u = z i ∧
        2 * |L.obj.obj.pairing x u| ≤ L.obj.obj.pairing x x := by
      intro i
      obtain ⟨k, hk⟩ := L.exists_sub_smul_two_mul_abs_pairing_le hL hx.1 (w i)
      exact ⟨w i - k • x, by simp [map_sub, hw i], hk⟩
    choose v hv hvsize using hsize
    set e := L.liftBasis z v hL hx hzind hzspan hv with he
    have hexv : e (Sum.inl ()) = x := by simp [he]
    have hewv : ∀ i, e (Sum.inr i) = v i := fun i ↦ by simp [he]
    have hB'0 : 0 ≤ reducedEntryBound n (projectedDetBound n D) :=
      reducedEntryBound_nonneg n (one_le_projectedDetBound n hD1)
    have hzz : ∀ i j, |L.obj.obj.pairing (z i) (z j)| ≤
        reducedEntryBound n (projectedDetBound n D) := by
      intro i j
      have hentry := congrFun (congrFun hgram i) j
      rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply] at hentry
      rw [show L.obj.obj.pairing (z i) (z j) = L.gramFamily z i j from rfl, ← hentry]
      exact hc' i j
    have hentries : ∀ p q : Unit ⊕ Fin n,
        |L.obj.obj.pairing (e p) (e q)| ≤ reducedEntryBound (n + 1) D := by
      intro p q
      rw [reducedEntryBound_succ]
      have hsymm : ∀ u u' : L.obj.obj.carrier,
        L.obj.obj.pairing u u' = L.obj.obj.pairing u' u := fun u u' ↦ L.obj.property.2 u u'
      have hcross : ∀ i, |L.obj.obj.pairing x (v i)| ≤
          reducedEntryBound n (projectedDetBound n D) + ((n : ℤ) + 1) * D := by
        intro i
        have h := hvsize i
        have h0 := abs_nonneg (L.obj.obj.pairing x (v i))
        linarith
      match p, q with
      | Sum.inl (), Sum.inl () =>
        rw [hexv, abs_of_pos (by omega)]
        linarith
      | Sum.inl (), Sum.inr j =>
        rw [hexv, hewv j]
        exact hcross j
      | Sum.inr i, Sum.inl () =>
        rw [hexv, hewv i, hsymm (v i) x]
        exact hcross i
      | Sum.inr i, Sum.inr j =>
        rw [hewv i, hewv j]
        have hproj : L.obj.obj.pairing (z i) (z j) =
            L.obj.obj.pairing x x * (L.obj.obj.pairing x x * L.obj.obj.pairing (v i) (v j) -
              L.obj.obj.pairing x (v i) * L.obj.obj.pairing x (v j)) := by
          rw [← hv i, ← hv j, FiniteProjectiveLatticeCat.pairing_scaledProjection_pairing]
        have h1 := hzz i j
        rw [hproj, abs_mul, abs_of_pos (show (0 : ℤ) < L.obj.obj.pairing x x by omega)] at h1
        have h2 : |L.obj.obj.pairing x x * L.obj.obj.pairing (v i) (v j) -
            L.obj.obj.pairing x (v i) * L.obj.obj.pairing x (v j)| ≤
            reducedEntryBound n (projectedDetBound n D) := by
          nlinarith [abs_nonneg (L.obj.obj.pairing x x * L.obj.obj.pairing (v i) (v j) -
            L.obj.obj.pairing x (v i) * L.obj.obj.pairing x (v j))]
        have h3 : L.obj.obj.pairing x x * |L.obj.obj.pairing (v i) (v j)| ≤
            reducedEntryBound n (projectedDetBound n D) +
              |L.obj.obj.pairing x (v i)| * |L.obj.obj.pairing x (v j)| := by
          have hsplit : |L.obj.obj.pairing x x * L.obj.obj.pairing (v i) (v j)| ≤
              |L.obj.obj.pairing x x * L.obj.obj.pairing (v i) (v j) -
                L.obj.obj.pairing x (v i) * L.obj.obj.pairing x (v j)| +
              |L.obj.obj.pairing x (v i) * L.obj.obj.pairing x (v j)| := by
            simpa using abs_add_le (L.obj.obj.pairing x x * L.obj.obj.pairing (v i) (v j) -
              L.obj.obj.pairing x (v i) * L.obj.obj.pairing x (v j))
              (L.obj.obj.pairing x (v i) * L.obj.obj.pairing x (v j))
          rw [abs_mul, abs_of_pos (show (0 : ℤ) < L.obj.obj.pairing x x by omega),
            abs_mul] at hsplit
          linarith
        have h4 : 4 * (|L.obj.obj.pairing x (v i)| * |L.obj.obj.pairing x (v j)|) ≤
            L.obj.obj.pairing x x * L.obj.obj.pairing x x := by
          nlinarith [hvsize i, hvsize j, abs_nonneg (L.obj.obj.pairing x (v i)),
            abs_nonneg (L.obj.obj.pairing x (v j))]
        have h5 : 4 * L.obj.obj.pairing x x * |L.obj.obj.pairing (v i) (v j)| ≤
            4 * L.obj.obj.pairing x x *
              (reducedEntryBound n (projectedDetBound n D) + L.obj.obj.pairing x x) := by
          nlinarith [abs_nonneg (L.obj.obj.pairing (v i) (v j))]
        have h6 := le_of_mul_le_mul_left h5 (by omega : (0 : ℤ) < 4 * L.obj.obj.pairing x x)
        linarith
    have hcard : Fintype.card (Unit ⊕ Fin n) = n + 1 := by simp [Nat.add_comm]
    refine ⟨e.reindex (Fintype.equivFinOfCardEq hcard), fun i j ↦ ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact hentries _ _

namespace FiniteProjectiveLatticeCat

variable (L : FiniteProjectiveLatticeCat ℤ ℤ)

/-- A Gram matrix is symmetric. -/
theorem gramMatrix_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L.obj.obj.carrier) : (gramMatrix L.obj b).IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  simp only [gramMatrix, LinearMap.BilinForm.toMatrix_apply, BilinModuleCat.bilinMap_apply]
  exact L.obj.property.2 (b j) (b i)

/-- Coordinates in a basis turn the lattice pairing into the bilinear form of the Gram matrix. -/
theorem pairing_equivFun_symm {n : ℕ} (b : Module.Basis (Fin n) ℤ L.obj.obj.carrier)
    (u v : Fin n → ℤ) :
    L.obj.obj.pairing (b.equivFun.symm u) (b.equivFun.symm v) =
      Matrix.toBilin' (gramMatrix L.obj b) u v := by
  have hrepr : ∀ (w : Fin n → ℤ) (i : Fin n), b.repr (b.equivFun.symm w) i = w i := fun w i ↦ by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [L.pairing_eq_sum_gram b, Matrix.toBilin'_apply]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hrepr, hrepr]

/-- **A lattice is recovered, up to isometry, from the Gram matrix of any of its bases.** -/
def isoFiniteLatticeOfGramMatrix {n : ℕ} (b : Module.Basis (Fin n) ℤ L.obj.obj.carrier) :
    finiteLatticeOfGramMatrix (gramMatrix L.obj b) (L.gramMatrix_isSymm b) ≅ L :=
  (isFiniteProjectiveLattice ℤ ℤ).fullyFaithfulι.preimageIso
    ((isLattice ℤ ℤ).fullyFaithfulι.preimageIso
      (BilinModuleCat.isoMk b.equivFun.symm fun u v ↦ L.pairing_equivFun_symm b u v))

end FiniteProjectiveLatticeCat

/-- Global isometry classes of positive definite integral lattices of rank `n` whose Gram
determinant is at most `D`. -/
def boundedIsometryClasses (n : ℕ) (D : ℤ) : Set IntegralLatticeIsometryClass :=
  {q | ∃ (L : FiniteProjectiveLatticeCat ℤ ℤ) (b : Module.Basis (Fin n) ℤ L.obj.obj.carrier),
    Quotient.mk globalIsometrySetoid L = q ∧ IsPositiveDefiniteLattice L ∧
      determinant L.obj b ≤ D}

/-- **Finitely many isometry classes of bounded determinant.** Every class of rank `n` and Gram
determinant at most `D` carries a reduced basis, whose Gram matrix is one of the finitely many
integer matrices with entries bounded by `reducedEntryBound n D`, and that matrix determines the
class. -/
theorem finite_isometryClasses_of_bounded (n : ℕ) (D : ℤ) :
    (boundedIsometryClasses n D).Finite := by
  classical
  have hT : (Subtype.val ⁻¹'
      {G : Matrix (Fin n) (Fin n) ℤ | ∀ i j, |G i j| ≤ reducedEntryBound n D} :
        Set {A : Matrix (Fin n) (Fin n) ℤ // A.IsSymm}).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (finite_boundedGramMatrices (Fin n) _)
  refine Set.Finite.subset (hT.image fun A ↦
    Quotient.mk globalIsometrySetoid (finiteLatticeOfGramMatrix A.1 A.2)) ?_
  rintro q ⟨L, b, rfl, hL, hD⟩
  obtain ⟨c, hc⟩ := exists_reduced_basis n D L hL b hD
  refine ⟨⟨gramMatrix L.obj c, L.gramMatrix_isSymm c⟩, fun i j ↦ ?_, ?_⟩
  · simpa only [gramMatrix, LinearMap.BilinForm.toMatrix_apply, BilinModuleCat.bilinMap_apply]
      using hc i j
  · exact Quotient.sound ⟨L.isoFiniteLatticeOfGramMatrix c⟩

/-- **Finiteness of the class set of a genus.** A positive definite integral lattice has finitely
many global isometry classes in its genus: rank, signature and determinant are genus invariants,
so the whole genus lies inside one bounded family of isometry classes. -/
theorem genus_finite (L : FiniteProjectiveLatticeCat ℤ ℤ) (hL : IsPositiveDefiniteLattice L) :
    {q : IntegralLatticeIsometryClass | ∃ M : FiniteProjectiveLatticeCat ℤ ℤ,
      Quotient.mk globalIsometrySetoid M = q ∧ SameGenus L M}.Finite := by
  classical
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  set b : Module.Basis (Fin L.rank) ℤ L.obj.obj.carrier :=
    Module.finBasisOfFinrankEq ℤ _ rfl with hb
  refine Set.Finite.subset (finite_isometryClasses_of_bounded L.rank (determinant L.obj b)) ?_
  rintro q ⟨M, rfl, hgen⟩
  letI : Module.Finite ℤ M.obj.obj.carrier := M.property
  letI : Module.Free ℤ M.obj.obj.carrier := M.carrier_free
  have hrank : Module.finrank ℤ M.obj.obj.carrier = L.rank := (rank_eq_of_sameGenus hgen).symm
  refine ⟨M, Module.finBasisOfFinrankEq ℤ _ hrank, rfl, ?_, ?_⟩
  · rwa [IsPositiveDefiniteLattice, ← signature_eq_of_sameGenus hgen]
  · exact le_of_eq (determinant_eq_of_sameGenus hgen b _)

end LeanCategories.Lattices.Valued
