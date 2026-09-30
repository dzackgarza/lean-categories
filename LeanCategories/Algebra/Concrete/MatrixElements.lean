/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Concrete.PolynomialElements
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# Square matrices as elements, and their operations

`R ↦ Σ n, Mat_n(R)` (`Poly.squareMatrices`, entrywise transport) is a functor on commutative
rings; its points (`MatrixPoints`) are square matrices over a commutative ring, up to isomorphism
of the entry ring. Operations, each iso-natural:

* `det`, `trace` (values in the entry ring), `charpoly` (in the polynomial ring);
* `inverses`: the two-sided inverses of `M` (at most one; none when `M` is singular);
* `rank`: the rank of `M`, `finrank` of the column space;
* `kernel`: the vectors `v` with `M v = 0`.
-/

open CategoryTheory LeanCategories.Foundation Polynomial Matrix

namespace LeanCategories.Algebra

universe u

noncomputable section

/-- Square matrices over commutative rings, up to isomorphism of the entry ring. -/
abbrev MatrixPoints := IsoElements Poly.squareMatrices.{u}

namespace Mat

abbrev ringEquiv {R S : CommRingCat.{u}} (φ : R ≅ S) : R ≃+* S := φ.commRingCatIsoToRingEquiv

/-- `det`. -/
def detMethod : MatrixPoints.{u} ⥤ (Core.inclusion _ ⋙ ringCarrier.{u}).Elements :=
  IsoElements.isoNatural Poly.squareMatrices (Core.inclusion _ ⋙ ringCarrier)
    (fun _ M => M.2.det) fun φ M => by
      change (M.2.map φ.iso.hom.hom).det = φ.iso.hom.hom M.2.det
      exact (RingHom.map_det _ _).symm

/-- `trace`. -/
def traceMethod : MatrixPoints.{u} ⥤ (Core.inclusion _ ⋙ ringCarrier.{u}).Elements :=
  IsoElements.isoNatural Poly.squareMatrices (Core.inclusion _ ⋙ ringCarrier)
    (fun _ M => M.2.trace) fun φ M => by
      change (M.2.map φ.iso.hom.hom).trace = φ.iso.hom.hom M.2.trace
      exact (AddMonoidHom.map_trace φ.iso.hom.hom M.2).symm

/-- `charpoly`. -/
def charpolyMethod : MatrixPoints.{u} ⥤ (Core.inclusion _ ⋙ polyCarrier.{u}).Elements :=
  IsoElements.isoNatural Poly.squareMatrices (Core.inclusion _ ⋙ polyCarrier)
    (fun _ M => M.2.charpoly) fun φ M => by
      change (M.2.map φ.iso.hom.hom).charpoly = M.2.charpoly.map φ.iso.hom.hom
      exact Matrix.charpoly_map _ _

/-- The two-sided inverses of a square matrix. -/
def inverseSet (R : CommRingCat.{u}) (M : Σ n : ℕ, Matrix (Fin n) (Fin n) R) :
    Set (Σ n : ℕ, Matrix (Fin n) (Fin n) R) :=
  {N | ∃ h : N.1 = M.1, M.2 * (h ▸ N.2) = 1 ∧ (h ▸ N.2) * M.2 = 1}

/-- `inverse`: the inverses of `M` (at most one), natural under isomorphisms. -/
def inverseMethod :
    MatrixPoints.{u} ⥤ (Core.inclusion _ ⋙ Poly.squareMatrices.{u} ⋙ powersetFunctor).Elements :=
  IsoElements.isoNatural Poly.squareMatrices (Core.inclusion _ ⋙ Poly.squareMatrices ⋙
      powersetFunctor) (fun R M => inverseSet R M) fun {X Y} φ M => by
    obtain ⟨n, M⟩ := M
    set e := ringEquiv φ.iso
    change inverseSet Y.of ⟨n, M.map e⟩ = (fun N => ⟨N.1, N.2.map e⟩) '' inverseSet X.of ⟨n, M⟩
    ext ⟨m, N⟩
    constructor
    · rintro ⟨h, h₁, h₂⟩
      change m = n at h
      subst h
      refine ⟨⟨m, N.map e.symm⟩, ⟨rfl, ?_, ?_⟩, ?_⟩
      · have hM : (M.map e).map e.symm = M := by ext i j; simp
        change M * N.map e.symm = 1
        have := congrArg (fun A => A.map e.symm) h₁
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
        rwa [hM] at this
      · have hM : (M.map e).map e.symm = M := by ext i j; simp
        change N.map e.symm * M = 1
        have := congrArg (fun A => A.map e.symm) h₂
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
        rwa [hM] at this
      · change (⟨m, (N.map e.symm).map e⟩ : Σ n : ℕ, Matrix (Fin n) (Fin n) Y.of) = ⟨m, N⟩
        congr 1
        ext i j; simp
    · rintro ⟨⟨k, K⟩, ⟨h, h₁, h₂⟩, hK⟩
      change k = n at h
      subst h
      cases hK
      refine ⟨rfl, ?_, ?_⟩
      · change M.map e * K.map e = 1
        rw [← Matrix.map_mul, show M * K = 1 from h₁]
        simp
      · change K.map e * M.map e = 1
        rw [← Matrix.map_mul, show K * M = 1 from h₂]
        simp

theorem mulVec_map_equiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (w : Fin n → R) : (M.map e) *ᵥ (e ∘ w) = e ∘ (M *ᵥ w) :=
  funext fun i => by simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- An isomorphism of entry rings maps the column space of `M` onto that of `M.map e`. -/
def rangeEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    LinearMap.range M.mulVecLin ≃+ LinearMap.range (M.map e).mulVecLin where
  toFun v := ⟨e ∘ v.1, by
    obtain ⟨w, hw⟩ := v.2
    refine ⟨e ∘ w, ?_⟩
    change (M.map e) *ᵥ (e ∘ w) = e ∘ v.1
    rw [mulVec_map_equiv, ← hw]
    rfl⟩
  invFun v := ⟨e.symm ∘ v.1, by
    obtain ⟨w, hw⟩ := v.2
    refine ⟨e.symm ∘ w, ?_⟩
    have h := mulVec_map_equiv e.symm (M.map e) w
    rw [show (M.map e).map e.symm = M by ext i j; simp] at h
    change M *ᵥ (e.symm ∘ w) = e.symm ∘ v.1
    rw [h, ← hw]
    rfl⟩
  left_inv v := Subtype.ext (funext fun i => e.symm_apply_apply _)
  right_inv v := Subtype.ext (funext fun i => e.apply_symm_apply _)
  map_add' v w := Subtype.ext (funext fun i => map_add e _ _)

theorem rank_map {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : (M.map e).rank = M.rank := by
  unfold Matrix.rank Module.finrank
  congr 1
  exact (rank_eq_of_equiv_equiv e (rangeEquiv e M) e.bijective fun r v =>
    Subtype.ext (funext fun i => by simp [rangeEquiv])).symm

/-- `rank`, an isomorphism invariant. -/
def rankMethod : MatrixPoints.{u} ⥤ Discrete ℕ :=
  IsoElements.isoInvariant Poly.squareMatrices (fun _ M => M.2.rank) fun φ M =>
    rank_map (ringEquiv φ) M.2

/-- Vectors of any length over `R`, transported entrywise. -/
def vectors : CommRingCat.{u} ⥤ Type u :=
  typeFunctor (fun R => Σ n : ℕ, Fin n → R) (fun f v => ⟨v.1, f.hom ∘ v.2⟩)
    (fun _ v => by cases v; rfl) (fun f g v => by cases v; rfl)

/-- The kernel of `M`: the vectors `v` with `M v = 0`. -/
def kernelSet (R : CommRingCat.{u}) (M : Σ n : ℕ, Matrix (Fin n) (Fin n) R) :
    Set (Σ n : ℕ, Fin n → R) :=
  {v | ∃ h : v.1 = M.1, M.2 *ᵥ (h ▸ v.2) = 0}

/-- `ker`: the kernel of a square matrix, natural under isomorphisms. -/
def kernelMethod :
    MatrixPoints.{u} ⥤ (Core.inclusion _ ⋙ vectors.{u} ⋙ powersetFunctor).Elements :=
  IsoElements.isoNatural Poly.squareMatrices (Core.inclusion _ ⋙ vectors ⋙ powersetFunctor)
    (fun R M => kernelSet R M) fun {X Y} φ M => by
    obtain ⟨n, M⟩ := M
    set e := ringEquiv φ.iso
    change kernelSet Y.of ⟨n, M.map e⟩ = (fun v => ⟨v.1, e ∘ v.2⟩) '' kernelSet X.of ⟨n, M⟩
    have hmap : ∀ w : Fin n → X.of, (M.map e) *ᵥ (e ∘ w) = e ∘ (M *ᵥ w) :=
      mulVec_map_equiv e M
    ext ⟨m, v⟩
    constructor
    · rintro ⟨h, hv⟩
      change m = n at h
      subst h
      refine ⟨⟨m, e.symm ∘ v⟩, ⟨rfl, ?_⟩, ?_⟩
      · change M *ᵥ (e.symm ∘ v) = 0
        have h' : e ∘ (M *ᵥ (e.symm ∘ v)) = 0 := by
          rw [← hmap]
          simpa [Function.comp_def] using hv
        funext i
        simpa using congrFun h' i
      · change (⟨m, e ∘ (e.symm ∘ v)⟩ : Σ n : ℕ, Fin n → Y.of) = ⟨m, v⟩
        congr 1
        funext i; simp
    · rintro ⟨⟨k, w⟩, ⟨h, hw⟩, hv⟩
      change k = n at h
      subst h
      cases hv
      refine ⟨rfl, ?_⟩
      change (M.map e) *ᵥ (e ∘ w) = 0
      rw [hmap, show M *ᵥ w = 0 from hw]
      funext i; simp

end Mat

end

end LeanCategories.Algebra
