/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.ExactCoupleSpectralSequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Data.Nat.Prime.Basic

/-!
# The Bockstein exact couple and spectral sequence

Weibel, *An Introduction to Homological Algebra* (1994), Construction 5.9.9,
pp. 157--158 (FC05-C05-U077).

Fix a prime `ℓ`. Given a graded abelian group `H_*` for which multiplication
by `ℓ` occurs in a long exact sequence

`⋯ ⟶ E_{n+1} ⟶ H_n ⟶[ℓ] H_n ⟶ E_n ⟶ H_{n-1} ⟶ ⋯`,

rolling the sequence into an exact couple yields the Bockstein spectral
sequence with initial page `E⁰ = E`. Weibel notes that its differential lowers
total degree by one; the auxiliary bigrading required by the spectral-sequence
formalism is artificial.

This file constructs the Bockstein differential, derives the exact couple
canonically by images and homology, iterates that derivation, and feeds the
resulting bigraded exact-couple tower into the generic FC05-C05-U070
constructor.  Thus the associated spectral sequence is constructed rather
than supplied as realization data. Proposition 5.9.10 and the later
convergence statements are not part of the definition layer.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

/-- Multiplication by the fixed prime `ℓ` on an abelian group. -/
def bocksteinPrimeMap (ℓ : ℕ) (A : ModuleCat ℤ) : A ⟶ A :=
  ℓ • 𝟙 A

/-- The graded long-exact-sequence data which Weibel rolls into the Bockstein
exact couple in Construction 5.9.9. -/
structure BocksteinExactCoupleData (ℓ : ℕ) where
  /-- The chosen integer is prime. -/
  prime : Nat.Prime ℓ
  /-- The graded integral object `H_*`. -/
  H : ℤ → ModuleCat ℤ
  /-- The graded coefficient object `E_*`. -/
  E : ℤ → ModuleCat ℤ
  /-- The reduction/quotient map `H_n ⟶ E_n`. -/
  j : ∀ n : ℤ, H n ⟶ E n
  /-- The connecting map `E_n ⟶ H_{n-1}`. -/
  k : ∀ n : ℤ, E n ⟶ H (n - 1)
  /-- `E_{n+1} ⟶ H_n ⟶[ℓ] H_n` is a complex. -/
  k_i : ∀ n : ℤ,
    (k (n + 1) ≫ eqToHom (congrArg H (by omega : n + 1 - 1 = n))) ≫
      bocksteinPrimeMap ℓ (H n) = 0
  /-- Exactness at the first copy of `H_n`. -/
  exact_ki : ∀ n : ℤ,
    (ShortComplex.mk
      (k (n + 1) ≫ eqToHom (congrArg H (by omega : n + 1 - 1 = n)))
      (bocksteinPrimeMap ℓ (H n)) (k_i n)).Exact
  /-- `H_n ⟶[ℓ] H_n ⟶ E_n` is a complex. -/
  i_j : ∀ n : ℤ, bocksteinPrimeMap ℓ (H n) ≫ j n = 0
  /-- Exactness at the second copy of `H_n`. -/
  exact_ij : ∀ n : ℤ,
    (ShortComplex.mk (bocksteinPrimeMap ℓ (H n)) (j n) (i_j n)).Exact
  /-- `H_n ⟶ E_n ⟶ H_{n-1}` is a complex. -/
  j_k : ∀ n : ℤ, j n ≫ k n = 0
  /-- Exactness at `E_n`. -/
  exact_jk : ∀ n : ℤ,
    (ShortComplex.mk (j n) (k n) (j_k n)).Exact

/-- The Bockstein differential `β_n : E_{n+1} ⟶ E_n`, obtained by following
the connecting map into `H_n` and then the quotient map back to `E_n`.

Source: Weibel, Construction 5.9.9 (FC05-C05-U077). -/
def bocksteinDifferential {ℓ : ℕ} (X : BocksteinExactCoupleData ℓ) (n : ℤ) :
    X.E (n + 1) ⟶ X.E n :=
  X.k (n + 1) ≫
    eqToHom (congrArg X.H (show n + 1 - 1 = n by omega)) ≫
    X.j n

/-- Consecutive Bockstein differentials compose to zero.  This is the
page-zero square-zero assertion coming directly from exactness of the long
exact sequence at `E_{n+1}`. -/
theorem bocksteinDifferential_sq {ℓ : ℕ} (X : BocksteinExactCoupleData ℓ) (n : ℤ) :
    bocksteinDifferential X (n + 1) ≫ bocksteinDifferential X n = 0 := by
  unfold bocksteinDifferential
  slice_lhs 3 4 => rw [X.j_k]
  simp

/-- The singly graded page-zero Bockstein complex.  Its object in degree `n`
is `E_n` and its differential is the Bockstein map
`E_{n+1} ⟶ H_n ⟶ E_n`.

Source: Weibel, Construction 5.9.9 (FC05-C05-U077). -/
def bocksteinComplex {ℓ : ℕ} (X : BocksteinExactCoupleData ℓ) :
    ChainComplex (ModuleCat ℤ) ℤ where
  X n := X.E n
  d i j :=
    if h : j + 1 = i then
      eqToHom (congrArg X.E h.symm) ≫ bocksteinDifferential X j
    else 0
  shape i j h := by
    simp only [ComplexShape.down_Rel] at h
    simp [h]
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    simp only [dif_pos hij, dif_pos hjk]
    subst i
    subst j
    simpa using bocksteinDifferential_sq X k

/-- The artificial vertical bigrading used for the Bockstein spectral
sequence: bidegree `(p,q)` carries `E_q`, with the first coordinate inert.
This choice keeps the underlying singly graded Bockstein complex literal; the
standard regrading and closed page-degree formulas belong to Proposition 5.9.2's
theorem layer. -/
def bocksteinPageZeroObject {ℓ : ℕ} (X : BocksteinExactCoupleData ℓ)
    (pq : ℤ × ℤ) : ModuleCat ℤ :=
  X.E pq.2

namespace BocksteinDerived

variable {ℓ : ℕ} (X : BocksteinExactCoupleData ℓ)

set_option backward.isDefEq.respectTransparency false

/-- The derived `D`-term in degree `n`: the image of multiplication by `ℓ`. -/
noncomputable abbrev H (n : ℤ) : ModuleCat ℤ :=
  Abelian.image (bocksteinPrimeMap ℓ (X.H n))

/-- The derived `E`-term in degree `n`: Bockstein homology of the current page. -/
noncomputable abbrev E (n : ℤ) : ModuleCat ℤ :=
  (bocksteinComplex X).homology n

/-- The restriction of multiplication by `ℓ` to its image. -/
noncomputable def i (n : ℤ) : H X n ⟶ H X n :=
  Abelian.image.ι (bocksteinPrimeMap ℓ (X.H n)) ≫
    Abelian.factorThruImage (bocksteinPrimeMap ℓ (X.H n))

lemma i_eq_primeMap (n : ℤ) :
    i X n = bocksteinPrimeMap ℓ (H X n) := by
  apply (cancel_mono (Abelian.image.ι (bocksteinPrimeMap ℓ (X.H n)))).1
  rw [i, Category.assoc, Abelian.image.fac]
  unfold bocksteinPrimeMap
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp]
  simp

/-- The original quotient map lands in Bockstein cycles and hence defines a
class in page homology. -/
noncomputable def jClass (n : ℤ) : X.H n ⟶ E X n :=
  (bocksteinComplex X).liftCycles (X.j n) (n - 1) (by simp) (by
      simp [bocksteinComplex, bocksteinDifferential]
      rw [← Category.assoc, X.j_k, zero_comp]) ≫
    (bocksteinComplex X).homologyπ n

lemma k_comp_jClass_eq_zero (n : ℤ) :
    (X.k (n + 1) ≫ eqToHom (congrArg X.H (show n + 1 - 1 = n by omega))) ≫
      jClass X n = 0 := by
  unfold jClass
  rw [← Category.assoc, HomologicalComplex.comp_liftCycles]
  apply HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
    (x := 𝟙 _) (i' := n + 1)
  simp [bocksteinComplex, bocksteinDifferential]

/-- The derived map `j'_n : im(ℓ_n) ⟶ H_n(E,β)`. -/
noncomputable def j (n : ℤ) : H X n ⟶ E X n :=
  (Abelian.coimageIsoImage (bocksteinPrimeMap ℓ (X.H n))).inv ≫
    (X.exact_ki n).isColimitCoimage.desc
      (CokernelCofork.ofπ (jClass X n) (k_comp_jClass_eq_zero X n))

lemma factorThruImage_comp_j (n : ℤ) :
    Abelian.factorThruImage (bocksteinPrimeMap ℓ (X.H n)) ≫ j X n =
      jClass X n := by
  let f := bocksteinPrimeMap ℓ (X.H n)
  have hfac : Abelian.coimage.π f ≫ (Abelian.coimageIsoImage f).hom =
      Abelian.factorThruImage f := by
    apply (cancel_mono (Abelian.image.ι f)).1
    rw [Abelian.image.fac]
    simpa only [Abelian.coimageIsoImage, asIso_hom, Category.assoc] using
      (Abelian.coimage_image_factorisation (f := f))
  have hfi : Abelian.factorThruImage f ≫ (Abelian.coimageIsoImage f).inv =
      Abelian.coimage.π f := by
    rw [← hfac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [j]
  slice_lhs 1 2 => rw [hfi]
  exact Cofork.IsColimit.π_desc (X.exact_ki n).isColimitCoimage

lemma image_ι_comp_jClass_eq_zero (n : ℤ) :
    Abelian.image.ι (bocksteinPrimeMap ℓ (X.H n)) ≫ jClass X n = 0 := by
  let K := bocksteinComplex X
  let a := Abelian.image.ι (bocksteinPrimeMap ℓ (X.H n))
  have hij : a ≫ X.j n = 0 :=
    (Abelian.image.ι_comp_eq_zero (f := bocksteinPrimeMap ℓ (X.H n)) (g := X.j n)).2
      (X.i_j n)
  have hcycle : (a ≫ X.j n) ≫ K.d n (n - 1) = 0 := by
    rw [hij, zero_comp]
  have hlift : K.liftCycles (a ≫ X.j n) (n - 1) (by simp) hcycle = 0 := by
    apply (cancel_mono (K.iCycles n)).1
    rw [K.liftCycles_i, zero_comp, hij]
  unfold jClass
  rw [← Category.assoc, HomologicalComplex.comp_liftCycles]
  rw [show K.liftCycles (a ≫ X.j n) (n - 1) (by simp) _ = 0 from hlift]
  simp

lemma i_comp_j (n : ℤ) : i X n ≫ j X n = 0 := by
  rw [i, Category.assoc, factorThruImage_comp_j]
  exact image_ι_comp_jClass_eq_zero X n

lemma exact_i_j (n : ℤ) :
    (ShortComplex.mk (i X n) (j X n) (i_comp_j X n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  let oldi := bocksteinPrimeMap ℓ (X.H n)
  let p := Abelian.factorThruImage oldi
  obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective p).1 inferInstance x
  have hmj : jClass X n m = 0 := by
    have h := congr($(factorThruImage_comp_j X n) m)
    simp only [ConcreteCategory.comp_apply] at h
    exact h.symm.trans hx
  let K := bocksteinComplex X
  have hjcycle : X.j n ≫ K.d n (n - 1) = 0 := by
    simp [K, bocksteinComplex, bocksteinDifferential]
    rw [← Category.assoc, X.j_k, zero_comp]
  let z := K.liftCycles (X.j n) (n - 1) (by simp) hjcycle
  have hzπ : K.homologyπ n (z m) = 0 := by
    simpa only [jClass, z, K, ConcreteCategory.comp_apply] using hmj
  let S := ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n + 1) n)
  have hS : S.Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    exact K.homologyIsCokernel (i := n + 1) (j := n) (by simp)
  obtain ⟨e, he⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS (z m) hzπ
  have he_i := congrArg (K.iCycles n) he
  have hto := congr($(K.toCycles_i (n + 1) n) e)
  simp only [ConcreteCategory.comp_apply] at hto
  have hlift := congr($(K.liftCycles_i (X.j n) (n - 1) (by simp) hjcycle) m)
  simp only [ConcreteCategory.comp_apply] at hlift
  have hd : K.d (n + 1) n e = X.j n m := by
    exact hto.symm.trans (he_i.trans hlift)
  let kn : X.E (n + 1) ⟶ X.H n :=
    X.k (n + 1) ≫ eqToHom (congrArg X.H (show n + 1 - 1 = n by omega))
  have hdn : K.d (n + 1) n = kn ≫ X.j n := by
    simp [K, kn, bocksteinComplex, bocksteinDifferential]
  have hje : X.j n (kn e) = X.j n m := by
    rw [hdn] at hd
    change X.j n (kn e) = X.j n m at hd
    exact hd
  have hjzero : X.j n (m - kn e) = 0 := by
    simp only [map_sub, sub_eq_zero]
    exact hje.symm
  obtain ⟨a, ha⟩ :=
    (ShortComplex.moduleCat_exact_iff _).mp (X.exact_ij n) (m - kn e) hjzero
  have hkfactor : kn ≫ p = 0 := by
    apply (cancel_mono (Abelian.image.ι oldi)).1
    rw [zero_comp, Category.assoc, Abelian.image.fac]
    exact X.k_i n
  use p a
  have hpa : Abelian.image.ι oldi (p a) = oldi a := by
    have h := congr($(Abelian.image.fac oldi) a)
    simpa only [ConcreteCategory.comp_apply] using h
  have hke : p (kn e) = 0 := by
    have h := congr($hkfactor e)
    simp only [ConcreteCategory.comp_apply] at h
    change p (kn e) = 0 at h
    exact h
  change i X n (p a) = p m
  rw [i]
  change p (Abelian.image.ι oldi (p a)) = p m
  rw [hpa, ha, map_sub, hke, sub_zero]

/-- Cycles in degree `n` map under `k_n` into `im(ℓ_{n-1})`. -/
noncomputable def kCycles (n : ℤ) :
    (bocksteinComplex X).cycles n ⟶ H X (n - 1) := by
  let F : KernelFork (X.j (n - 1)) :=
    KernelFork.ofι ((bocksteinComplex X).iCycles n ≫ X.k n) (by
      have hd := (bocksteinComplex X).iCycles_d n (n - 1)
      have hdn : (bocksteinComplex X).d n (n - 1) =
          X.k n ≫ X.j (n - 1) := by
        simp [bocksteinComplex, bocksteinDifferential]
      rw [hdn] at hd
      simpa only [Category.assoc] using hd)
  exact (X.exact_ij (n - 1)).isLimitImage.lift F

lemma kCycles_comp_image_ι (n : ℤ) :
    kCycles X n ≫ Abelian.image.ι (bocksteinPrimeMap ℓ (X.H (n - 1))) =
      (bocksteinComplex X).iCycles n ≫ X.k n := by
  unfold kCycles
  exact Fork.IsLimit.lift_ι (X.exact_ij (n - 1)).isLimitImage

lemma toCycles_comp_kCycles_eq_zero (n : ℤ) :
    (bocksteinComplex X).toCycles (n + 1) n ≫ kCycles X n = 0 := by
  apply (cancel_mono
    (Abelian.image.ι (bocksteinPrimeMap ℓ (X.H (n - 1))))).1
  rw [zero_comp, Category.assoc, kCycles_comp_image_ι]
  rw [← Category.assoc, HomologicalComplex.toCycles_i]
  simp [bocksteinComplex, bocksteinDifferential, Category.assoc, X.j_k]

/-- The derived connecting map `k'_n : H_n(E,β) ⟶ im(ℓ_{n-1})`. -/
noncomputable def k (n : ℤ) : E X n ⟶ H X (n - 1) :=
  (CokernelCofork.IsColimit.desc'
    ((bocksteinComplex X).homologyIsCokernel (i := n + 1) (j := n) (by simp))
    (kCycles X n) (toCycles_comp_kCycles_eq_zero X n)).1

lemma homologyπ_comp_k_comp_image_ι (n : ℤ) :
    (bocksteinComplex X).homologyπ n ≫ k X n ≫
        Abelian.image.ι (bocksteinPrimeMap ℓ (X.H (n - 1))) =
      (bocksteinComplex X).iCycles n ≫ X.k n := by
  rw [← Category.assoc]
  have hk := (CokernelCofork.IsColimit.desc'
    ((bocksteinComplex X).homologyIsCokernel (i := n + 1) (j := n) (by simp))
    (kCycles X n) (toCycles_comp_kCycles_eq_zero X n)).2
  change (bocksteinComplex X).homologyπ n ≫ k X n = kCycles X n at hk
  rw [hk]
  exact kCycles_comp_image_ι X n

lemma j_comp_k (n : ℤ) : j X n ≫ k X n = 0 := by
  let p := Abelian.factorThruImage (bocksteinPrimeMap ℓ (X.H n))
  apply (cancel_epi p).1
  rw [comp_zero]
  slice_lhs 1 2 => rw [factorThruImage_comp_j]
  let q := Abelian.image.ι (bocksteinPrimeMap ℓ (X.H (n - 1)))
  apply (cancel_mono q).1
  rw [zero_comp]
  unfold jClass
  slice_lhs 2 4 => rw [homologyπ_comp_k_comp_image_ι X n]
  slice_lhs 1 2 => rw [HomologicalComplex.liftCycles_i]
  exact X.j_k n

lemma exact_j_k (n : ℤ) :
    (ShortComplex.mk (j X n) (k X n) (j_comp_k X n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  let K := bocksteinComplex X
  let π := K.homologyπ n
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective π).1 inferInstance x
  have hfac := congr($(homologyπ_comp_k_comp_image_ι X n) z)
  simp only [ConcreteCategory.comp_apply] at hfac
  have hkz : X.k n (K.iCycles n z) = 0 := by
    rw [hx] at hfac
    calc
      X.k n (K.iCycles n z) =
          Abelian.image.ι (bocksteinPrimeMap ℓ (X.H (n - 1))) 0 := hfac.symm
      _ = 0 := map_zero _
  obtain ⟨h, hh⟩ :=
    (ShortComplex.moduleCat_exact_iff _).mp (X.exact_jk n)
      ((bocksteinComplex X).iCycles n z) hkz
  change X.j n h = (bocksteinComplex X).iCycles n z at hh
  let p := Abelian.factorThruImage (bocksteinPrimeMap ℓ (X.H n))
  use p h
  have hfactor := congr($(factorThruImage_comp_j X n) h)
  simp only [ConcreteCategory.comp_apply] at hfactor
  rw [hfactor]
  have hjcycle : X.j n ≫ K.d n (n - 1) = 0 := by
    simp [K, bocksteinComplex, bocksteinDifferential]
    rw [← Category.assoc, X.j_k, zero_comp]
  let z' := K.liftCycles (X.j n) (n - 1) (by simp) hjcycle
  have hz' : z' h = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
    have hlift := congr($(K.liftCycles_i (X.j n) (n - 1) (by simp) hjcycle) h)
    simp only [ConcreteCategory.comp_apply] at hlift
    exact hlift.trans hh
  change K.homologyπ n (z' h) = K.homologyπ n z
  rw [hz']

/-- The derived connecting map with its target index normalized to degree `n`. -/
noncomputable def kNext (n : ℤ) : E X (n + 1) ⟶ H X n :=
  k X (n + 1) ≫ eqToHom (congrArg (H X) (show n + 1 - 1 = n by omega))

/-- The original connecting map with its target index normalized to degree `n`. -/
noncomputable def sourceKNext (n : ℤ) : X.E (n + 1) ⟶ X.H n :=
  X.k (n + 1) ≫ eqToHom (congrArg X.H (show n + 1 - 1 = n by omega))

lemma H_transport_comp_image_ι {a b : ℤ} (h : a = b) :
    eqToHom (congrArg (H X) h) ≫
        Abelian.image.ι (bocksteinPrimeMap ℓ (X.H b)) =
      Abelian.image.ι (bocksteinPrimeMap ℓ (X.H a)) ≫
        eqToHom (congrArg X.H h) := by
  subst b
  simp

lemma homologyπ_comp_kNext_comp_image_ι (n : ℤ) :
    (bocksteinComplex X).homologyπ (n + 1) ≫ kNext X n ≫
        Abelian.image.ι (bocksteinPrimeMap ℓ (X.H n)) =
      (bocksteinComplex X).iCycles (n + 1) ≫ sourceKNext X n := by
  unfold kNext sourceKNext
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    rw [H_transport_comp_image_ι X (show n + 1 - 1 = n by omega)]
  slice_lhs 1 3 => rw [homologyπ_comp_k_comp_image_ι X (n + 1)]
  rfl

lemma kNext_comp_i (n : ℤ) : kNext X n ≫ i X n = 0 := by
  let K := bocksteinComplex X
  let oldi := bocksteinPrimeMap ℓ (X.H n)
  let p := Abelian.factorThruImage oldi
  let kn := sourceKNext X n
  have hkfactor : kn ≫ p = 0 := by
    apply (cancel_mono (Abelian.image.ι oldi)).1
    rw [zero_comp, Category.assoc, Abelian.image.fac]
    exact X.k_i n
  apply (cancel_epi (K.homologyπ (n + 1))).1
  unfold i
  rw [comp_zero]
  slice_lhs 1 3 => rw [homologyπ_comp_kNext_comp_image_ι X n]
  change K.iCycles (n + 1) ≫ kn ≫ p = 0
  calc
    (K.iCycles (n + 1) ≫ kn) ≫ p =
        K.iCycles (n + 1) ≫ (kn ≫ p) := Category.assoc _ _ _
    _ = K.iCycles (n + 1) ≫ 0 := by rw [hkfactor]
    _ = 0 := comp_zero

lemma exact_kNext_i (n : ℤ) :
    (ShortComplex.mk (kNext X n) (i X n) (kNext_comp_i X n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  let oldi := bocksteinPrimeMap ℓ (X.H n)
  let p := Abelian.factorThruImage oldi
  obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective p).1 inferInstance x
  have hpa : Abelian.image.ι oldi (p m) = oldi m := by
    have h := congr($(Abelian.image.fac oldi) m)
    simpa only [ConcreteCategory.comp_apply] using h
  have hpoldi : p (oldi m) = 0 := by
    change i X n (p m) = 0 at hx
    rw [i] at hx
    simp only [ConcreteCategory.comp_apply] at hx
    rw [hpa] at hx
    exact hx
  have hioldi : oldi (oldi m) = 0 := by
    have h := congr($(Abelian.image.fac oldi) (oldi m))
    simp only [ConcreteCategory.comp_apply] at h
    rw [hpoldi] at h
    exact h.symm.trans (map_zero _)
  obtain ⟨e, he⟩ :=
    (ShortComplex.moduleCat_exact_iff _).mp (X.exact_ki n) (oldi m) hioldi
  have he' : sourceKNext X n e = oldi m := by
    change (X.k (n + 1) ≫
      eqToHom (congrArg X.H (show n + 1 - 1 = n by omega))) e = oldi m
    exact he
  have hjezero : X.j n (sourceKNext X n e) = 0 := by
    rw [he']
    have hij := congr($(X.i_j n) m)
    simpa using hij
  let K := bocksteinComplex X
  have hde : K.d (n + 1) n e = 0 := by
    simpa [K, sourceKNext, bocksteinComplex, bocksteinDifferential,
      ConcreteCategory.comp_apply] using hjezero
  let T := ShortComplex.mk (K.iCycles (n + 1)) (K.d (n + 1) n)
    (K.iCycles_d (n + 1) n)
  have hT : T.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    exact K.cyclesIsKernel (i := n + 1) (j := n) (by simp)
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT e hde
  use K.homologyπ (n + 1) z
  apply (ModuleCat.mono_iff_injective (Abelian.image.ι oldi)).1 inferInstance
  have hk := congr($(homologyπ_comp_kNext_comp_image_ι X n) z)
  simp only [ConcreteCategory.comp_apply] at hk
  calc
    Abelian.image.ι oldi (kNext X n (K.homologyπ (n + 1) z)) =
        sourceKNext X n (K.iCycles (n + 1) z) := hk
    _ = sourceKNext X n e := by rw [hz]
    _ = oldi m := he'
    _ = Abelian.image.ι oldi (p m) := hpa.symm

/-- The exact couple derived once from the Bockstein long exact sequence. -/
noncomputable def derived : BocksteinExactCoupleData ℓ where
  prime := X.prime
  H := H X
  E := E X
  j := j X
  k := k X
  k_i n := by
    change kNext X n ≫ bocksteinPrimeMap ℓ (H X n) = 0
    rw [← i_eq_primeMap X n]
    exact kNext_comp_i X n
  exact_ki n := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : i X n x = 0 := by
      have hi := congr($(i_eq_primeMap X n) x)
      exact hi.trans hx
    obtain ⟨y, hy⟩ :=
      (ShortComplex.moduleCat_exact_iff _).mp (exact_kNext_i X n) x hx'
    use y
    exact hy
  i_j n := by
    rw [← i_eq_primeMap X n]
    exact i_comp_j X n
  exact_ij n := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨y, hy⟩ :=
      (ShortComplex.moduleCat_exact_iff _).mp (exact_i_j X n) x hx
    use y
    have hi := congr($(i_eq_primeMap X n) y)
    exact hi.symm.trans hy
  j_k n := j_comp_k X n
  exact_jk n := exact_j_k X n

/-- Iterated derived Bockstein exact couples. -/
noncomputable def iterate : ℕ → BocksteinExactCoupleData ℓ
  | 0 => X
  | r + 1 => derived (iterate r)


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
end BocksteinDerived

end LeanCategories.Homological
