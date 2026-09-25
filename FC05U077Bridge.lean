import LeanCategories.Homological.BocksteinSpectralSequence

@[expose] noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

namespace BocksteinDerived

variable {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false

/-- Identity shifts for the `i` and `j` maps in the artificial Bockstein
bigrading. -/
def zeroShift : (ℤ × ℤ) ≃ (ℤ × ℤ) := Equiv.refl _

/-- Vertical translation by `-1`, the shift of the Bockstein connecting map. -/
def kShift : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1, p.2 - 1)
  invFun p := (p.1, p.2 + 1)
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp

/-- Artificial bigrading of the `r`th Bockstein exact couple. -/
noncomputable def bigraded (D : BocksteinExactCoupleData ℓ) :
    LeanCategories.Homological.BigradedExactCouple (C := ModuleCat ℤ) where
  D p := D.H p.2
  E p := D.E p.2
  iShift := zeroShift
  jShift := zeroShift
  kShift := kShift
  i p := bocksteinPrimeMap ℓ (D.H p.2)
  j p := D.j p.2
  k p := D.k p.2
  i_j p := by
    exact D.i_j p.2
  j_k p := by
    exact D.j_k p.2
  k_i p := by
    simpa [kShift] using D.k_i (p.2 - 1)
  exact_ij p := by
    exact D.exact_ij p.2
  exact_jk p := by
    exact D.exact_jk p.2
  exact_ki p := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨y, hy⟩ :=
      (ShortComplex.moduleCat_exact_iff _).mp (D.exact_ki (p.2 - 1)) x hx
    let hq : p.2 - 1 + 1 = p.2 := by omega
    have hktransport :
        eqToHom (congrArg D.E hq) ≫ D.k p.2 =
          D.k (p.2 - 1 + 1) ≫
            eqToHom (by simp [hq]) := by
      simpa only using (CategoryTheory.eqToHom_naturality D.k hq).symm
    use eqToHom (congrArg D.E hq) y
    calc
      D.k p.2 (eqToHom (congrArg D.E hq) y) =
          (D.k (p.2 - 1 + 1) ≫ eqToHom (by simp [hq])) y := by
              have h := congr($hktransport y)
              simpa only [ConcreteCategory.comp_apply] using h
      _ = x := hy

/-- The differential in the artificial bigraded page is the ordinary
Bockstein differential on the second coordinate. -/
lemma pageDifferential_eq_bockstein_d (D : BocksteinExactCoupleData ℓ)
    (p : ℤ × ℤ) :
    (bigraded D).page.d p (kShift p) =
      (bocksteinComplex D).d p.2 (p.2 - 1) := by
  simp [BigradedExactCouple.page, BigradedExactCouple.pageDifferential,
    BigradedExactCouple.pageShape, BigradedExactCouple.pageShift, bigraded,
    zeroShift, kShift, bocksteinComplex, bocksteinDifferential]

lemma pageDifferential_prev_eq_bockstein_d (D : BocksteinExactCoupleData ℓ)
    (p : ℤ × ℤ) :
    (bigraded D).page.d (kShift.symm p) p =
      (bocksteinComplex D).d (p.2 + 1) p.2 := by
  simp [BigradedExactCouple.page, BigradedExactCouple.pageDifferential,
    BigradedExactCouple.pageShape, BigradedExactCouple.pageShift, bigraded,
    zeroShift, kShift, bocksteinComplex, bocksteinDifferential]

/-- The short complex determining homology at `(p,q)` is the ordinary
Bockstein short complex in degree `q`. -/
noncomputable def pageShortComplexIso (D : BocksteinExactCoupleData ℓ)
    (p : ℤ × ℤ) :
    (bigraded D).page.sc' (kShift.symm p) p (kShift p) ≅
      (bocksteinComplex D).sc' (p.2 + 1) p.2 (p.2 - 1) := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simpa using (pageDifferential_prev_eq_bockstein_d D p).symm
  · simpa using (pageDifferential_eq_bockstein_d D p).symm

end BocksteinDerived

end LeanCategories.Homological

namespace LeanCategories.Homological.BocksteinDerived

open CategoryTheory CategoryTheory.Limits

variable {ℓ : ℕ}

lemma page_prev_rel (D : BocksteinExactCoupleData ℓ) (p : ℤ × ℤ) :
    (bigraded D).pageShape.Rel (kShift.symm p) p := by
  simp [BigradedExactCouple.pageShape, BigradedExactCouple.pageShift,
    bigraded, zeroShift, kShift]

lemma page_next_rel (D : BocksteinExactCoupleData ℓ) (p : ℤ × ℤ) :
    (bigraded D).pageShape.Rel p (kShift p) := by
  simp [BigradedExactCouple.pageShape, BigradedExactCouple.pageShift,
    bigraded, zeroShift, kShift]

noncomputable def pageHomologyIso (D : BocksteinExactCoupleData ℓ)
    (p : ℤ × ℤ) :
    (bocksteinComplex D).homology p.2 ≅ (bigraded D).page.homology p :=
  ((bocksteinComplex D).homologyIsoSc' (p.2 + 1) p.2 (p.2 - 1) (by simp) (by simp)) ≪≫
    (ShortComplex.homologyMapIso (pageShortComplexIso D p).symm) ≪≫
    ((bigraded D).page.homologyIsoSc' (kShift.symm p) p (kShift p)
      ((bigraded D).pageShape.prev_eq' (page_prev_rel D p))
      ((bigraded D).pageShape.next_eq' (page_next_rel D p))).symm

/-- One step of Bockstein derivation as the generic bigraded exact-couple
derivation data required by the U070 constructor. -/
noncomputable def bigradedDerivedData (D : BocksteinExactCoupleData ℓ) :
    (bigraded D).DerivedData where
  couple := bigraded (derived D)
  D_iso p := by
    change H D p.2 ≅ Abelian.image ((bigraded D).incomingI p)
    simpa [BigradedExactCouple.incomingI, bigradedIncoming, bigraded, zeroShift] using
      (Iso.refl (Abelian.image (bocksteinPrimeMap ℓ (D.H p.2))))
  E_iso p := pageHomologyIso D p

/-- The recursive tower of bigraded Bockstein exact couples. -/
noncomputable def bigradedTower (D : BocksteinExactCoupleData ℓ) :
    (bigraded D).DerivedTower where
  couple n := bigraded (iterate D n)
  zero_eq := rfl
  step n := bigradedDerivedData (iterate D n)
  succ_eq _ := rfl

/-- The generic page-shape family attached by U070 to the Bockstein tower. -/
def spectralShape (D : BocksteinExactCoupleData ℓ) : ℤ → ComplexShape (ℤ × ℤ) :=
  BigradedExactCouple.DerivedTower.spectralShape (bigraded D) (bigradedTower D) 0

/-- The Bockstein spectral sequence constructed from the long exact sequence
by repeated exact-couple derivation. -/
noncomputable def spectralSequence (D : BocksteinExactCoupleData ℓ) :
    SpectralSequence (ModuleCat ℤ) (spectralShape D) 0 :=
  BigradedExactCouple.DerivedTower.spectralSequence (bigraded D) (bigradedTower D) 0

lemma spectralSequence_page_zero_X (D : BocksteinExactCoupleData ℓ)
    (p : ℤ × ℤ) :
    ((spectralSequence D).page 0 (by omega)).X p = D.E p.2 := rfl

lemma spectralSequence_page_zero_d (D : BocksteinExactCoupleData ℓ)
    (p : ℤ × ℤ) :
    ((spectralSequence D).page 0 (by omega)).d p (kShift p) =
      (bocksteinComplex D).d p.2 (p.2 - 1) := by
  exact pageDifferential_eq_bockstein_d D p

end LeanCategories.Homological.BocksteinDerived
