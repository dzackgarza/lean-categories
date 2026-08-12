/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.GenusInvariants
public import LeanCategories.Lattices.Valued.Reduction
public import LeanCategories.Lattices.Valued.Sublattice

/-!
# The reduction step for positive definite integral lattices

`Reduction.lean` splits off a shortest vector `x` and clears the denominators of the orthogonal
projection along it. This file builds the three objects that the rank induction consumes.

## A primitive vector starts a basis

`ker_scaledProjection` computes the kernel of the cleared projection: it is the line `ℤ ∙ x`.
The inclusion `⊇` is immediate; the converse says a vector on the rational line through `x` is
already on the integral line, which is exactly primitivity of a shortest vector.

With that kernel, no Smith normal form is needed. `liftBasis` takes any generating independent
family `z` of the projected submodule together with lifts `w` under the projection, and returns a
basis of the whole lattice indexed by `Unit ⊕ ι` whose first vector is `x`. `linearIndependent_lift`
and `span_lift` are the two halves.

## The projected lattice

`projectedSubmodule x` is the image of the cleared projection. Over `ℤ` a submodule of a finite
free module is finite free, so `projectedLattice x` packages it as an object of
`FiniteProjectiveLatticeCat ℤ ℤ` carrying the form restricted from the ambient lattice.

`isPositiveDefinite_projectedLattice` shows it is positive definite. The Gram matrix of any family
inside a positive definite lattice is positive semidefinite over `ℝ`
(`posSemidef_realGram_family`), and a positive semidefinite matrix with nonzero determinant is
positive definite. `isPositiveDefiniteSignature_of_posDef` converts that back into the signature
form of `IsPositiveDefiniteLattice`.

## The determinant

`gramFamily_eq` writes the Gram matrix of a family as the Gram matrix of a basis conjugated by the
coordinate matrix of the family. Applied to the family `x, z₂, …, z_n`, whose Gram matrix is block
diagonal because the projection is orthogonal to `x` (`gramFamily_sum_elim`), and whose coordinate
matrix in the basis `x, w₂, …, w_n` is block triangular with diagonal blocks `1` and `b(x,x)`
(`coordMatrix_sum_elim`), it gives `pairing_mul_det_gramFamily`:

  `b(x,x) * det(Gram z) = b(x,x) ^ (2 * (n - 1)) * det(Gram L)`.

Cancelling `b(x,x)` recovers the classical `det N = b(x,x) ^ (2n - 3) * det L`. Only block
determinant lemmas for a vanishing off-diagonal block are needed; no Schur complement and no
inverse of `b(x,x)` appear.

## What is not here

The rank induction itself. Its hypothesis must carry a determinant *bound* rather than a fixed
determinant: over `ℝ` or `ℚ` the conclusion is false, since a reduced basis of a real form of
fixed determinant has unbounded entries `diag(ε, d / ε)`. Integrality supplies the lower bound `1`
on the minimum, and the induction must stay inside the integral lattices to keep it. The pieces
that remain are the transfer of a basis of `projectedLattice x` back to an ambient family, the
bookkeeping that turns `pairing_mul_det_gramFamily` into a determinant bound for the smaller
lattice, and the entry bound assembled from the Hermite bound of `ClassFiniteness` and the size
reduction of `Reduction`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Matrix
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- A positive definite real Gram matrix has a positive definite signature. This is the converse
of `matrixQuadraticForm_posDef`. -/
theorem isPositiveDefiniteSignature_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) : IsPositiveDefiniteSignature (matrixSignature ℝ A) := by
  have hQ : ∀ x : ι → ℝ, x ≠ 0 → 0 < matrixQuadraticForm ℝ A x := by
    intro x hx
    have hpos := hA.dotProduct_mulVec_pos hx
    rw [star_trivial] at hpos
    simpa [matrixQuadraticForm, Matrix.toBilin'_apply'] using hpos
  have htop : ((matrixQuadraticForm ℝ A).restrict (⊤ : Submodule ℝ (ι → ℝ))).PosDef := by
    intro x hx
    exact hQ x.1 (by simpa using hx)
  have hle : Module.finrank ℝ (ι → ℝ) ≤ sigPos (matrixQuadraticForm ℝ A) := by
    simpa using le_sigPos_of_posDef (matrixQuadraticForm ℝ A) htop
  have hsum :=
    QuadraticForm.sigPos_add_sigNeg_add_radical (Q := matrixQuadraticForm ℝ A)
  have hup : sigPos (matrixQuadraticForm ℝ A) ≤ Module.finrank ℝ (ι → ℝ) :=
    sigPos_le_finrank (matrixQuadraticForm ℝ A)
  exact ⟨by omega, by omega⟩

section ModuleHelpers

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A combination with vanishing coefficients is zero. Stated for a general module so that it
applies to whichever integer module structure a lattice carrier presents. -/
theorem sum_smul_eq_zero_of_coeff_eq_zero {ι : Type*} [Fintype ι] {g : ι → R}
    (hg : ∀ i, g i = 0) (v : ι → M) : ∑ i, g i • v i = 0 :=
  Finset.sum_eq_zero fun i _ ↦ by rw [hg i, zero_smul]

/-- A scalar killing a nonzero vector of a torsion-free module is zero. -/
theorem eq_zero_of_smul_eq_zero [IsCancelMulZero R] [Module.IsTorsionFree R M] {a : R} {v : M}
    (h : a • v = 0) (hv : v ≠ 0) : a = 0 :=
  (smul_eq_zero.mp h).resolve_right hv

end ModuleHelpers

namespace FiniteProjectiveLatticeCat

variable (L : FiniteProjectiveLatticeCat ℤ ℤ)

/-- The pairing of two lattice vectors is the real Gram bilinear form of their coordinates. -/
theorem realCoord_dotProduct_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L.obj.obj.carrier) (x y : L.obj.obj.carrier) :
    L.realCoord b x ⬝ᵥ L.realGramMatrix b *ᵥ L.realCoord b y =
      ((L.obj.obj.pairing x y : ℤ) : ℝ) := by
  have hint : L.obj.obj.pairing x y =
      ∑ i, ∑ j, b.repr x i * gramMatrix L.obj b i j * b.repr y j := by
    rw [show L.obj.obj.pairing x y = L.obj.obj.bilinMap x y from rfl,
      ← Matrix.toBilin_toMatrix b L.obj.obj.bilinMap, Matrix.toBilin_apply]
    rfl
  rw [hint]
  push_cast
  simp only [realGramMatrix, realCoord, dotProduct, Matrix.mulVec, Matrix.map_apply,
    eq_intCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The Gram matrix of an arbitrary family of vectors in a positive definite lattice is positive
semidefinite over `ℝ`. -/
theorem posSemidef_realGram_family {J : Type*} [Finite J]
    (hL : IsPositiveDefiniteLattice L) (z : J → L.obj.obj.carrier) :
    (Matrix.of fun i j ↦ ((L.obj.obj.pairing (z i) (z j) : ℤ) : ℝ)).PosSemidef := by
  classical
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  set b := Module.Free.chooseBasis ℤ L.obj.obj.carrier with hb
  set M : Matrix (Module.Free.ChooseBasisIndex ℤ L.obj.obj.carrier) J ℝ :=
    Matrix.of fun p i ↦ L.realCoord b (z i) p with hM
  have hfac : (Matrix.of fun i j ↦ ((L.obj.obj.pairing (z i) (z j) : ℤ) : ℝ)) =
      Mᵀ * L.realGramMatrix b * M := by
    ext i j
    rw [Matrix.of_apply, ← L.realCoord_dotProduct_pair b (z i) (z j)]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hM, Matrix.of_apply, dotProduct,
      Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ by ring
  rw [hfac]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (L.realGramMatrix_posDef hL b).posSemidef.conjTranspose_mul_mul_same M

section Projected

variable {L}

/-- The image of the cleared projection along `x`: the rescaled orthogonal complement of `x`. -/
def projectedSubmodule (x : L.obj.obj.carrier) : Submodule ℤ L.obj.obj.carrier :=
  LinearMap.range (L.scaledProjection x)

/-- Membership in the projected submodule. -/
theorem mem_projectedSubmodule_iff {x y : L.obj.obj.carrier} :
    y ∈ L.projectedSubmodule x ↔ ∃ v, L.scaledProjection x v = y :=
  Iff.rfl

/-- The cleared projection kills its own centre. -/
-- already reachable by `simp` through `scaledProjection_apply`; not tagged
theorem scaledProjection_self (x : L.obj.obj.carrier) : L.scaledProjection x x = 0 := by
  rw [scaledProjection_apply, sub_self]

/-- **The kernel of the cleared projection is the line through a shortest vector.** A vector
killed by the projection lies on the rational line through `x`, and primitivity of `x` forces it
onto the integral line. -/
theorem ker_scaledProjection (hL : IsPositiveDefiniteLattice L) {x : L.obj.obj.carrier}
    (hx : L.IsMinimalVector x) :
    LinearMap.ker (L.scaledProjection x) = Submodule.span ℤ {x} := by
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  apply le_antisymm
  · intro y hy
    have hx0 : x ≠ 0 := hx.1
    set m := L.obj.obj.pairing x x with hm
    set c := L.obj.obj.pairing x y with hc
    have hmpos : 0 < m := L.pairing_self_pos hL hx0
    have hkey : m • y = c • x := by
      have := (L.scaledProjection_eq_zero_iff x y).mp hy
      simpa [hm, hc] using this
    set d : ℤ := (Int.gcd m c : ℤ) with hd
    have hdpos : 0 < d := by
      have hg : 0 < Int.gcd m c := Int.gcd_pos_of_ne_zero_left c hmpos.ne'
      omega
    set m' := m / d with hm'
    set c' := c / d with hc'
    have hmd : d * m' = m := Int.mul_ediv_cancel' (Int.gcd_dvd_left (a := m) (b := c))
    have hcd : d * c' = c := Int.mul_ediv_cancel' (Int.gcd_dvd_right (a := m) (b := c))
    have hcop : IsCoprime m' c' := by
      rw [Int.isCoprime_iff_gcd_eq_one, hm', hc', hd]
      exact Int.gcd_div_gcd_div_gcd (Int.gcd_pos_of_ne_zero_left c hmpos.ne')
    have hsmul : m' • y = c' • x := by
      have hdd : d • (m' • y) = d • (c' • x) := by
        rw [smul_smul, smul_smul, hmd, hcd]
        exact hkey
      exact smul_right_injective L.obj.obj.carrier hdpos.ne' (by simpa using hdd)
    obtain ⟨u, v, huv⟩ := hcop
    have hxeq : x = m' • (u • x + v • y) := by
      have h1 : m' • (u • x + v • y) = (m' * u) • x + v • (m' • y) := by
        simp only [ModuleCat.zsmul_eq_smul]
        module
      have h2 : (m' * u) • x + v • (c' • x) = (u * m' + v * c') • x := by
        simp only [ModuleCat.zsmul_eq_smul]
        module
      rw [h1, hsmul, h2, huv, one_smul]
    have hm'one : m' = 1 := by
      have hpos : 0 < m' := by nlinarith
      rcases L.eq_one_or_neg_one_of_isMinimalVector hL hx hxeq with h | h
      · exact h
      · omega
    rw [Submodule.mem_span_singleton]
    refine ⟨c', ?_⟩
    rw [hm'one, one_smul] at hsmul
    simpa using hsmul.symm
  · rw [Submodule.span_le]
    rintro _ rfl
    simp

section Adapted

variable {x : L.obj.obj.carrier} {ι : Type*} [Finite ι]
variable (z w : ι → L.obj.obj.carrier)

/-- The lifted family is linearly independent: the projection separates the lifts, and what is
left is a multiple of `x`. -/
theorem linearIndependent_lift (hzind : LinearIndependent ℤ z)
    (hw : ∀ i, L.scaledProjection x (w i) = z i) (hx0 : x ≠ 0) :
    LinearIndependent ℤ (Sum.elim (fun _ : Unit ↦ x) w) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton] at hg
  have hproj := congrArg (L.scaledProjection x) hg
  simp only [map_add, map_zero, map_sum, LinearMap.map_smul, scaledProjection_self, smul_zero,
    zero_add, hw] at hproj
  have hzero := Fintype.linearIndependent_iff.mp hzind (fun i ↦ g (Sum.inr i)) hproj
  rw [sum_smul_eq_zero_of_coeff_eq_zero hzero w, add_zero] at hg
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  rintro (⟨⟩ | i)
  · exact eq_zero_of_smul_eq_zero hg hx0
  · exact hzero i

/-- The lifted family spans: the projection of any vector is a combination of the projected
basis, and the residue lies on the line through `x`. -/
theorem span_lift (hL : IsPositiveDefiniteLattice L) (hx : L.IsMinimalVector x)
    (hzspan : Submodule.span ℤ (Set.range z) = L.projectedSubmodule x)
    (hw : ∀ i, L.scaledProjection x (w i) = z i) :
    ⊤ ≤ Submodule.span ℤ (Set.range (Sum.elim (fun _ : Unit ↦ x) w)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  intro y _
  have hp : L.scaledProjection x y ∈ Submodule.span ℤ (Set.range z) := by
    rw [hzspan]; exact ⟨y, rfl⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at hp
  obtain ⟨c, hc⟩ := hp
  have hker : y - ∑ i, c i • w i ∈ LinearMap.ker (L.scaledProjection x) := by
    simp only [ModuleCat.zsmul_eq_smul, LinearMap.mem_ker, map_sub, map_sum,
      LinearMap.map_smul, hw, hc, sub_self]
  rw [L.ker_scaledProjection hL hx, Submodule.mem_span_singleton] at hker
  obtain ⟨a, ha⟩ := hker
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨Sum.elim (fun _ ↦ a) c, ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
  rw [ha]
  simp only [ModuleCat.zsmul_eq_smul, sub_add_cancel]

/-- **A primitive vector starts a basis.** A basis of the rescaled orthogonal complement lifts to
a basis of the whole lattice whose first vector is the shortest vector `x`. -/
def liftBasis (hL : IsPositiveDefiniteLattice L) (hx : L.IsMinimalVector x)
    (hzind : LinearIndependent ℤ z)
    (hzspan : Submodule.span ℤ (Set.range z) = L.projectedSubmodule x)
    (hw : ∀ i, L.scaledProjection x (w i) = z i) :
    Module.Basis (Unit ⊕ ι) ℤ L.obj.obj.carrier :=
  Module.Basis.mk (L.linearIndependent_lift z w hzind hw hx.1)
    (L.span_lift z w hL hx hzspan hw)

@[simp]
theorem liftBasis_apply (hL : IsPositiveDefiniteLattice L) (hx : L.IsMinimalVector x)
    (hzind : LinearIndependent ℤ z)
    (hzspan : Submodule.span ℤ (Set.range z) = L.projectedSubmodule x)
    (hw : ∀ i, L.scaledProjection x (w i) = z i) (j : Unit ⊕ ι) :
    L.liftBasis z w hL hx hzind hzspan hw j = Sum.elim (fun _ : Unit ↦ x) w j := by
  rw [liftBasis, Module.Basis.mk_apply]

end Adapted

section ProjectedLattice

variable {x : L.obj.obj.carrier}

/-- **The projected lattice.** The image of the cleared projection, with the form restricted from
the ambient lattice, is again a finite projective integral lattice. -/
def projectedLattice (x : L.obj.obj.carrier) : FiniteProjectiveLatticeCat ℤ ℤ :=
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  let bP := (Submodule.basisOfPid (Module.Free.chooseBasis ℤ L.obj.obj.carrier)
    (L.projectedSubmodule x)).2
  ⟨formedSublattice L.obj (L.projectedSubmodule x), Module.Finite.of_basis bP⟩

/-- The projected lattice pairs its vectors by the ambient pairing. -/
@[simp]
theorem projectedLattice_pairing (x : L.obj.obj.carrier) (u v : L.projectedSubmodule x) :
    (L.projectedLattice x).obj.obj.pairing u v =
      L.obj.obj.pairing (u : L.obj.obj.carrier) (v : L.obj.obj.carrier) :=
  rfl

end ProjectedLattice

section GramFamily

/-- The pairing expressed through the Gram matrix of a basis. -/
theorem pairing_eq_sum_gram {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : Module.Basis κ ℤ L.obj.obj.carrier) (a b : L.obj.obj.carrier) :
    L.obj.obj.pairing a b = ∑ p, ∑ q, e.repr a p * gramMatrix L.obj e p q * e.repr b q := by
  rw [show L.obj.obj.pairing a b = L.obj.obj.bilinMap a b from rfl,
    ← Matrix.toBilin_toMatrix e L.obj.obj.bilinMap, Matrix.toBilin_apply]
  rfl

/-- The coordinate matrix of a family of lattice vectors in a chosen basis. -/
def coordMatrix {κ J : Type*} (e : Module.Basis κ ℤ L.obj.obj.carrier)
    (v : J → L.obj.obj.carrier) : Matrix κ J ℤ :=
  Matrix.of fun p i ↦ e.repr (v i) p

/-- The Gram matrix of a family of lattice vectors. -/
def gramFamily {J : Type*} (v : J → L.obj.obj.carrier) : Matrix J J ℤ :=
  Matrix.of fun i j ↦ L.obj.obj.pairing (v i) (v j)

/-- **The Gram matrix of a family is the basis Gram matrix conjugated by coordinates.** -/
theorem gramFamily_eq {κ J : Type*} [Fintype κ] [DecidableEq κ]
    (e : Module.Basis κ ℤ L.obj.obj.carrier) (v : J → L.obj.obj.carrier) :
    L.gramFamily v = (L.coordMatrix e v)ᵀ * gramMatrix L.obj e * L.coordMatrix e v := by
  ext i j
  rw [gramFamily, Matrix.of_apply, L.pairing_eq_sum_gram e]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coordMatrix, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end GramFamily

section ProjectedDeterminant

/-- **The Gram matrix of `x` together with the projected family is block diagonal.** The cleared
projection is orthogonal to `x`. -/
theorem gramFamily_sum_elim {x : L.obj.obj.carrier} {ι : Type*} (z w : ι → L.obj.obj.carrier)
    (hw : ∀ i, L.scaledProjection x (w i) = z i) :
    L.gramFamily (Sum.elim (fun _ : Unit ↦ x) z) =
      Matrix.fromBlocks (Matrix.of fun _ _ : Unit ↦ L.obj.obj.pairing x x) 0 0
        (L.gramFamily z) := by
  have hzero : ∀ i, L.obj.obj.pairing x (z i) = 0 := fun i ↦ by
    rw [← hw i]; exact L.pairing_scaledProjection_left x (w i)
  ext i j
  cases i with
  | inl u =>
    cases j with
    | inl u' => cases u; cases u'; rfl
    | inr j => simpa [gramFamily] using hzero j
  | inr i =>
    cases j with
    | inl u' =>
      have hsymm := L.obj.property.2 (z i) x
      simpa [gramFamily, hsymm] using hzero i
    | inr j => rfl

/-- **The coordinate matrix of `x` together with the projected family** in a basis that begins
with `x` and continues with the lifts. -/
theorem coordMatrix_sum_elim {x : L.obj.obj.carrier} {ι : Type*} [DecidableEq ι]
    (z w : ι → L.obj.obj.carrier) (hw : ∀ i, L.scaledProjection x (w i) = z i)
    (e : Module.Basis (Unit ⊕ ι) ℤ L.obj.obj.carrier) (hex : e (Sum.inl ()) = x)
    (hew : ∀ i, e (Sum.inr i) = w i) :
    L.coordMatrix e (Sum.elim (fun _ : Unit ↦ x) z) =
      Matrix.fromBlocks 1 (Matrix.of fun _ i ↦ -L.obj.obj.pairing x (w i)) 0
        (Matrix.diagonal fun _ ↦ L.obj.obj.pairing x x) := by
  classical
  have hzrepr : ∀ i, e.repr (z i) =
      L.obj.obj.pairing x x • Finsupp.single (Sum.inr i) (1 : ℤ) -
        L.obj.obj.pairing x (w i) • Finsupp.single (Sum.inl ()) (1 : ℤ) := by
    intro i
    rw [← hw i, scaledProjection_apply]
    simp only [ModuleCat.zsmul_eq_smul, map_sub, map_smul]
    rw [← hew i, ← hex, e.repr_self, e.repr_self]
  have hxrepr : e.repr x = Finsupp.single (Sum.inl ()) (1 : ℤ) := by rw [← hex, e.repr_self]
  ext p i
  cases i with
  | inl u =>
    cases u
    cases p with
    | inl u' => cases u'; simp [coordMatrix, hxrepr]
    | inr q => simp [coordMatrix, hxrepr]
  | inr i =>
    cases p with
    | inl u' =>
      cases u'
      simp [coordMatrix, hzrepr i]
    | inr q =>
      simp [coordMatrix, hzrepr i, Finsupp.single_apply, Matrix.diagonal_apply, eq_comm]

/-- **The determinant of the projected family.** Clearing the first row and column of the Gram
matrix multiplies the determinant by `b(x,x)` to the power `2 * (n - 1)`, and the cleared matrix
is the block sum of `b(x,x)` and the Gram matrix of the projected family. -/
theorem pairing_mul_det_gramFamily {x : L.obj.obj.carrier} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (z w : ι → L.obj.obj.carrier)
    (hw : ∀ i, L.scaledProjection x (w i) = z i)
    (e : Module.Basis (Unit ⊕ ι) ℤ L.obj.obj.carrier) (hex : e (Sum.inl ()) = x)
    (hew : ∀ i, e (Sum.inr i) = w i) :
    L.obj.obj.pairing x x * (L.gramFamily z).det =
      L.obj.obj.pairing x x ^ (2 * Fintype.card ι) * determinant L.obj e := by
  classical
  have hfam := L.gramFamily_eq e (Sum.elim (fun _ : Unit ↦ x) z)
  rw [L.gramFamily_sum_elim z w hw, L.coordMatrix_sum_elim z w hw e hex hew] at hfam
  have hdet := congrArg Matrix.det hfam
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_diagonal, Matrix.det_unique,
    Finset.prod_const, Finset.card_univ] at hdet
  simp only [Matrix.of_apply, one_mul] at hdet
  rw [determinant, hdet]
  ring

/-- The Gram determinant of a positive definite lattice is positive. -/
theorem determinant_pos (hL : IsPositiveDefiniteLattice L) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℤ L.obj.obj.carrier) : 0 < determinant L.obj b := by
  have hdet : (L.realGramMatrix b).det = ((determinant L.obj b : ℤ) : ℝ) := by
    rw [realGramMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp [determinant]
  have hpos := (L.realGramMatrix_posDef hL b).det_pos
  rw [hdet] at hpos
  exact_mod_cast hpos

/-- **The projected lattice is positive definite.** Its Gram matrix is positive semidefinite as
the Gram matrix of a family inside a positive definite lattice, and the determinant identity
shows the determinant is nonzero. -/
theorem isPositiveDefinite_projectedLattice (hL : IsPositiveDefiniteLattice L)
    {x : L.obj.obj.carrier} (hxne : x ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {z w : ι → L.obj.obj.carrier} (hw : ∀ i, L.scaledProjection x (w i) = z i)
    (e : Module.Basis (Unit ⊕ ι) ℤ L.obj.obj.carrier) (hex : e (Sum.inl ()) = x)
    (hew : ∀ i, e (Sum.inr i) = w i)
    (bz : Module.Basis ι ℤ (L.projectedLattice x).obj.obj.carrier)
    (hgram : gramMatrix (L.projectedLattice x).obj bz = L.gramFamily z) :
    IsPositiveDefiniteLattice (L.projectedLattice x) := by
  have hm : 0 < L.obj.obj.pairing x x := L.pairing_self_pos hL hxne
  have hkey := L.pairing_mul_det_gramFamily z w hw e hex hew
  have hne : (L.gramFamily z).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hkey
    exact absurd hkey.symm
      (mul_pos (pow_pos hm _) (L.determinant_pos hL e)).ne'
  have hmapdet : ((L.gramFamily z).map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hne
  have hsemi : ((L.gramFamily z).map (Int.castRingHom ℝ)).PosSemidef :=
    L.posSemidef_realGram_family hL z
  rw [IsPositiveDefiniteLattice, integralSignature_eq_matrixSignature _ bz, hgram]
  exact isPositiveDefiniteSignature_of_posDef (hsemi.posDef_iff_det_ne_zero.mpr hmapdet)

end ProjectedDeterminant

end Projected

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
