module

public import LeanCategories.Modules.Bilinear.Valued
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- The objects that are finite projective and have a symmetric form. -/
def isLattice : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ Module.Finite R L.carrier ∧ Module.Projective R L.carrier ∧ L.IsSymmetric

/-- The category of `W`-valued `R`-lattices. -/
abbrev LatticeCat := (isLattice R W).FullSubcategory

/-- Finite symmetric form modules. Projectivity is not required. -/
def isFiniteForm : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ Module.Finite R L.carrier ∧ L.IsSymmetric

/-- The category of finite `W`-valued symmetric form modules. -/
abbrev FiniteFormCat := (isFiniteForm R W).FullSubcategory

/-- Change the value module by postcomposition. -/
def changeValue {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : LatticeCat R W ⥤ LatticeCat R W' where
  obj L :=
    ⟨(LeanCategories.Modules.Bilinear.Valued.changeValue R W f).obj L.obj,
      ⟨L.property.1, L.property.2.1,
        fun x y ↦ congr_arg f (L.property.2.2 x y)⟩⟩
  map g := ObjectProperty.homMk
    ((LeanCategories.Modules.Bilinear.Valued.changeValue R W f).map g.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Scalar extension of the form. -/
def baseChangeForm (L : BilinModuleCat R W) :
    TensorProduct S (TensorProduct R S L.carrier) (TensorProduct R S L.carrier) →ₗ[S]
      TensorProduct R S W :=
  (TensorProduct.lift.equiv (.id S) (TensorProduct R S L.carrier)
    (TensorProduct R S L.carrier) (TensorProduct R S W))
      (LinearMap.BilinMap.baseChange S L.bilinMap)

/-- Scalar extension of a bilinear module. -/
def baseChangeObject (L : BilinModuleCat R W) : BilinModuleCat S (TensorProduct R S W) :=
  op ⟨op (ModuleCat.of S (TensorProduct R S L.carrier)), baseChangeForm R W S L⟩

/-- Scalar extension on the category of bilinear modules. -/
def baseChangeBilin : BilinModuleCat R W ⥤ BilinModuleCat S (TensorProduct R S W) where
  obj := baseChangeObject R W S
  map {L M} f := by
    refine Quiver.Hom.op (CategoryOfElements.homMk _ _
      (op (ModuleCat.ofHom (LinearMap.baseChange S (BilinModuleCat.underlyingMap f)))) ?_)
    dsimp [bilinearForms]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b y =>
          change (a * b) ⊗ₜ[R] M.pairing (BilinModuleCat.underlyingMap f x)
            (BilinModuleCat.underlyingMap f y) = (a * b) ⊗ₜ[R] L.pairing x y
          rw [BilinModuleCat.map_pairing f]
        | add y₁ y₂ hy₁ hy₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, hy₁, hy₂]
      | add x₁ x₂ hx₁ hx₂ =>
        rw [TensorProduct.add_tmul, map_add, map_add, hx₁, hx₂]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  map_id L := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (LinearMap.baseChange S (LinearMap.id)) z = z
    rw [LinearMap.baseChange_id]
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (LinearMap.baseChange S
      (BilinModuleCat.underlyingMap g ∘ₗ BilinModuleCat.underlyingMap f)) z =
        (LinearMap.baseChange S (BilinModuleCat.underlyingMap g) ∘ₗ
          LinearMap.baseChange S (BilinModuleCat.underlyingMap f)) z
    rw [LinearMap.baseChange_comp]

/-- Scalar extension on the total category of variable-valued forms. -/
def baseChangeBilWForm : BilWFormCat R ⥤ BilWFormCat S where
  obj X := by
    refine ⟨ModuleCat.of S (TensorProduct R S X.value), ?_⟩
    exact baseChangeObject R X.value S X.formed
  map {X Y} f := by
    refine BilWFormCat.homMk
      (LinearMap.baseChange S (BilWFormCat.carrierMap f).hom)
      (LinearMap.baseChange S (BilWFormCat.valueMap f).hom) ?_
    intro x y
    change (LinearMap.baseChange S (BilWFormCat.valueMap f).hom)
        ((LinearMap.BilinMap.baseChange S X.formed.bilinMap) x y) =
      (LinearMap.BilinMap.baseChange S Y.formed.bilinMap)
        ((LinearMap.baseChange S (BilWFormCat.carrierMap f).hom) x)
        ((LinearMap.baseChange S (BilWFormCat.carrierMap f).hom) y)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
        change (a * b) ⊗ₜ[R]
            (BilWFormCat.valueMap f).hom (X.pairing x y) =
          (a * b) ⊗ₜ[R] Y.pairing
            ((BilWFormCat.carrierMap f).hom x)
            ((BilWFormCat.carrierMap f).hom y)
        rw [BilWFormCat.map_pairing]
      | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  map_id X := by
    apply BilWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_id
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_id
  map_comp f g := by
    apply BilWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_comp (A := S)
        (f := (BilWFormCat.valueMap f).hom) (BilWFormCat.valueMap g).hom
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_comp (A := S)
        (f := (BilWFormCat.carrierMap f).hom) (BilWFormCat.carrierMap g).hom

/-- Scalar extension on the total category of symmetric variable-valued forms. -/
def baseChangeSymBilWForm : SymBilWFormCat R ⥤ SymBilWFormCat S where
  obj X := by
    refine ⟨(baseChangeBilWForm R S).obj X.obj, ?_⟩
    exact LinearMap.BilinMap.baseChange_isSymm X.property
  map f := ObjectProperty.homMk ((baseChangeBilWForm R S).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilWForm R S).map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilWForm R S).map_comp f.hom g.hom

/-- Scalar extension preserves finite projective symmetric lattices. -/
def baseChange : LatticeCat R W ⥤ LatticeCat S (TensorProduct R S W) where
  obj L := by
    letI : Module.Finite R L.obj.carrier := L.property.1
    letI : Module.Projective R L.obj.carrier := L.property.2.1
    refine ⟨baseChangeObject R W S L.obj, ?_⟩
    change Module.Finite S (TensorProduct R S L.obj.carrier) ∧
      Module.Projective S (TensorProduct R S L.obj.carrier) ∧
        ∀ x y, (LinearMap.BilinMap.baseChange S L.obj.bilinMap) x y =
          (LinearMap.BilinMap.baseChange S L.obj.bilinMap) y x
    exact ⟨inferInstance, inferInstance,
      LinearMap.BilinMap.baseChange_isSymm L.property.2.2⟩
  map f := ObjectProperty.homMk ((baseChangeBilin R W S).map f.hom)
  map_id L := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilin R W S).map_id L.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilin R W S).map_comp f.hom g.hom

end BaseChange

/-- Integral lattices are `R`-valued `R`-lattices. -/
abbrev IntegralLatticeCat := LatticeCat R R

/-- Scalar extension of an integral lattice along `R → S`. -/
noncomputable def baseChangeIntegral (S : Type u) [CommRing S] [Algebra R S] :
    IntegralLatticeCat R ⥤ IntegralLatticeCat S where
  obj L :=
    (changeValue S (TensorProduct R S R)
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap).obj
        ((baseChange R R S).obj L)
  map f :=
    (changeValue S (TensorProduct R S R)
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap).map
        ((baseChange R R S).map f)
  map_id L := by simp
  map_comp f g := by simp

section Evenness

variable {R}

/-- The quadratic map `x ↦ b(x,x)` associated to an integral lattice. -/
def quadraticMap (L : IntegralLatticeCat R) :
    QuadraticForm R L.obj.carrier :=
  LinearMap.BilinMap.toQuadraticMap L.obj.bilinMap

/-- The scale ideal generated by all pairings. -/
def scaleModule (L : IntegralLatticeCat R) : Ideal R :=
  LinearMap.range L.obj.form

/-- The value ideal generated by the diagonal values `b(x,x)`. -/
def valueModule (L : IntegralLatticeCat R) : Ideal R :=
  Ideal.span (Set.range (quadraticMap L))

/-- The quotient in the defining exact sequence for the scale ideal. -/
abbrev ScaleCokernel (L : IntegralLatticeCat R) := R ⧸ scaleModule L

/-- The quotient in the defining exact sequence for the value ideal. -/
abbrev ValueCokernel (L : IntegralLatticeCat R) := R ⧸ valueModule L

def scaleInclusion (L : IntegralLatticeCat R) : scaleModule L →ₗ[R] R :=
  (scaleModule L).subtype

def scaleProjection (L : IntegralLatticeCat R) : R →ₗ[R] ScaleCokernel L :=
  Submodule.mkQ (scaleModule L)

def valueInclusion (L : IntegralLatticeCat R) : valueModule L →ₗ[R] R :=
  (valueModule L).subtype

def valueProjection (L : IntegralLatticeCat R) : R →ₗ[R] ValueCokernel L :=
  Submodule.mkQ (valueModule L)

/-- Restrict the codomain of a quadratic map to a submodule containing all values. -/
def quadraticMapCodRestrict {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Q : QuadraticMap R M N)
    (P : Submodule R N) (hQ : ∀ x, Q x ∈ P) : QuadraticMap R M P where
  toFun x := ⟨Q x, hQ x⟩
  toFun_smul r x := by
    apply Subtype.ext
    exact Q.map_smul r x
  exists_companion' := by
    let B : LinearMap.BilinMap R M P := LinearMap.mk₂ R
      (fun x y ↦ ⟨QuadraticMap.polar Q x y,
        P.sub_mem (P.sub_mem (hQ (x + y)) (hQ x)) (hQ y)⟩)
      (fun x y z ↦ by
        apply Subtype.ext
        exact QuadraticMap.polar_add_left Q x y z)
      (fun r x y ↦ by
        apply Subtype.ext
        exact QuadraticMap.polar_smul_left Q r x y)
      (fun x y z ↦ by
        apply Subtype.ext
        exact QuadraticMap.polar_add_right Q x y z)
      (fun r x y ↦ by
        apply Subtype.ext
        exact QuadraticMap.polar_smul_right Q r x y)
    refine ⟨B, ?_⟩
    intro x y
    apply Subtype.ext
    exact QuadraticMap.map_add Q x y

theorem exact_scaleModule (L : IntegralLatticeCat R) :
    Function.Exact (scaleInclusion L) (scaleProjection L) :=
  LinearMap.exact_subtype_mkQ (scaleModule L)

theorem exact_valueModule (L : IntegralLatticeCat R) :
    Function.Exact (valueInclusion L) (valueProjection L) :=
  LinearMap.exact_subtype_mkQ (valueModule L)

theorem scaleInclusion_injective (L : IntegralLatticeCat R) :
    Function.Injective (scaleInclusion L) :=
  Subtype.val_injective

theorem scaleProjection_surjective (L : IntegralLatticeCat R) :
    Function.Surjective (scaleProjection L) :=
  Submodule.mkQ_surjective _

theorem valueInclusion_injective (L : IntegralLatticeCat R) :
    Function.Injective (valueInclusion L) :=
  Subtype.val_injective

theorem valueProjection_surjective (L : IntegralLatticeCat R) :
    Function.Surjective (valueProjection L) :=
  Submodule.mkQ_surjective _

/-- Quadratic `I`-evenness is a lift of `x ↦ b(x,x)` through `I ↪ R`. -/
def IsQuadraticallyEven (L : IntegralLatticeCat R) (I : Ideal R) : Prop :=
  ∃ qI : QuadraticMap R L.obj.carrier I,
    I.subtype.compQuadraticMap qI = quadraticMap L

/-- Bilinear `I`-evenness is a lift of the tensor form through `I ↪ R`. -/
def IsBilinearlyEven (L : IntegralLatticeCat R) (I : Ideal R) : Prop :=
  ∃ bI : TensorProduct R L.obj.carrier L.obj.carrier →ₗ[R] I,
    I.subtype ∘ₗ bI = L.obj.form

theorem isBilinearlyEven_iff_pairing_mem (L : IntegralLatticeCat R)
    (I : Ideal R) :
    IsBilinearlyEven L I ↔ ∀ x y, L.obj.pairing x y ∈ I := by
  constructor
  · rintro ⟨bI, hbI⟩ x y
    have hxy := LinearMap.congr_fun hbI (x ⊗ₜ[R] y)
    change I.subtype (bI (x ⊗ₜ[R] y)) = L.obj.pairing x y at hxy
    rw [← hxy]
    exact (bI (x ⊗ₜ[R] y)).property
  · intro h
    let bI : TensorProduct R L.obj.carrier L.obj.carrier →ₗ[R] I :=
      LinearMap.codRestrict I L.obj.form (by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => exact h x y
        | add x y hx hy => simpa using I.add_mem hx hy)
    refine ⟨bI, ?_⟩
    ext z
    rfl

theorem isQuadraticallyEven_iff_value_mem
    (L : IntegralLatticeCat R) (I : Ideal R) :
    IsQuadraticallyEven L I ↔ ∀ x, quadraticMap L x ∈ I := by
  constructor
  · rintro ⟨qI, hqI⟩ x
    have hx := QuadraticMap.congr_fun hqI x
    change I.subtype (qI x) = quadraticMap L x at hx
    rw [← hx]
    exact (qI x).property
  · intro h
    refine ⟨quadraticMapCodRestrict (quadraticMap L) I h, ?_⟩
    ext x
    rfl

theorem isQuadraticallyEven_of_isBilinearlyEven
    (L : IntegralLatticeCat R) (I : Ideal R)
    (hL : IsBilinearlyEven L I) : IsQuadraticallyEven L I := by
  rcases hL with ⟨bI, hbI⟩
  let bI' : LinearMap.BilinMap R L.obj.carrier I :=
    (TensorProduct.lift.equiv (.id R) L.obj.carrier L.obj.carrier I).symm bI
  refine ⟨LinearMap.BilinMap.toQuadraticMap bI', ?_⟩
  ext x
  simp only [LinearMap.compQuadraticMap_apply,
    LinearMap.BilinMap.toQuadraticMap_apply]
  change I.subtype (bI (x ⊗ₜ[R] x)) = L.obj.form (x ⊗ₜ[R] x)
  exact LinearMap.congr_fun hbI (x ⊗ₜ[R] x)

theorem isBilinearlyEven_of_isQuadraticallyEven_of_invertible_two
    [Invertible (2 : R)] (L : IntegralLatticeCat R) (I : Ideal R)
    (hL : IsQuadraticallyEven L I) : IsBilinearlyEven L I := by
  rw [isBilinearlyEven_iff_pairing_mem]
  rw [isQuadraticallyEven_iff_value_mem] at hL
  intro x y
  have hPolar : QuadraticMap.polar (quadraticMap L) x y ∈ I :=
    I.sub_mem (I.sub_mem (hL (x + y)) (hL x)) (hL y)
  have hPolarEq :
      QuadraticMap.polar (quadraticMap L) x y =
        (2 : R) • L.obj.pairing x y := by
    rw [quadraticMap, LinearMap.BilinMap.polar_toQuadraticMap]
    change L.obj.pairing x y + L.obj.pairing y x =
      (2 : R) • L.obj.pairing x y
    rw [← L.property.2.2 x y]
    rw [two_smul R]
  rw [hPolarEq] at hPolar
  have hScaled := I.smul_mem (⅟(2 : R)) hPolar
  simpa [smul_smul, invOf_mul_self] using hScaled

theorem isQuadraticallyEven_top (L : IntegralLatticeCat R) :
    IsQuadraticallyEven L (⊤ : Ideal R) := by
  refine ⟨Submodule.topEquiv.symm.toLinearMap.compQuadraticMap
    (quadraticMap L), ?_⟩
  ext x
  rfl

theorem isBilinearlyEven_top (L : IntegralLatticeCat R) :
    IsBilinearlyEven L (⊤ : Ideal R) := by
  refine ⟨Submodule.topEquiv.symm.toLinearMap ∘ₗ L.obj.form, ?_⟩
  ext x
  rfl

theorem isQuadraticallyEven_of_eq_top (L : IntegralLatticeCat R)
    (I : Ideal R) (hI : I = ⊤) : IsQuadraticallyEven L I := by
  subst I
  exact isQuadraticallyEven_top L

theorem isBilinearlyEven_of_eq_top (L : IntegralLatticeCat R)
    (I : Ideal R) (hI : I = ⊤) : IsBilinearlyEven L I := by
  subst I
  exact isBilinearlyEven_top L

theorem isQuadraticallyEven_span_singleton_of_isUnit
    (L : IntegralLatticeCat R) (a : R) (ha : IsUnit a) :
    IsQuadraticallyEven L (Ideal.span {a}) :=
  isQuadraticallyEven_of_eq_top L _
    (Ideal.span_singleton_eq_top.mpr ha)

theorem isBilinearlyEven_span_singleton_of_isUnit
    (L : IntegralLatticeCat R) (a : R) (ha : IsUnit a) :
    IsBilinearlyEven L (Ideal.span {a}) :=
  isBilinearlyEven_of_eq_top L _
    (Ideal.span_singleton_eq_top.mpr ha)

/-- Classical evenness is quadratic `2R`-evenness. -/
abbrev IsEven (L : IntegralLatticeCat R) : Prop :=
  IsQuadraticallyEven L (Ideal.span {(2 : R)})

section BaseChangeEvenness

variable (S : Type u) [CommRing S] [Algebra R S]

@[simp]
theorem baseChangeIntegral_pairing_tmul (L : IntegralLatticeCat R)
    (a b : S) (x y : L.obj.carrier) :
    ((baseChangeIntegral R S).obj L).obj.pairing
        (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R S (L.obj.pairing x y) := by
  change (TensorProduct.AlgebraTensorModule.rid R S S)
      ((a * b) ⊗ₜ[R] L.obj.pairing x y) = _
  simp [Algebra.smul_def, mul_comm]

theorem baseChangeIntegral_pairing_zero_left (L : IntegralLatticeCat R)
    (y : TensorProduct R S L.obj.carrier) :
    ((baseChangeIntegral R S).obj L).obj.pairing 0 y = 0 :=
  BilinModuleCat.pairing_zero_left ((baseChangeIntegral R S).obj L).obj y

theorem baseChangeIntegral_pairing_zero_right (L : IntegralLatticeCat R)
    (x : TensorProduct R S L.obj.carrier) :
    ((baseChangeIntegral R S).obj L).obj.pairing x 0 = 0 :=
  BilinModuleCat.pairing_zero_right ((baseChangeIntegral R S).obj L).obj x

@[simp]
theorem baseChangeIntegral_pairing_add_left (L : IntegralLatticeCat R)
    (x y z : TensorProduct R S L.obj.carrier) :
    ((baseChangeIntegral R S).obj L).obj.pairing (x + y) z =
      ((baseChangeIntegral R S).obj L).obj.pairing x z +
        ((baseChangeIntegral R S).obj L).obj.pairing y z :=
  BilinModuleCat.pairing_add_left ((baseChangeIntegral R S).obj L).obj x y z

@[simp]
theorem baseChangeIntegral_pairing_add_right (L : IntegralLatticeCat R)
    (x y z : TensorProduct R S L.obj.carrier) :
    ((baseChangeIntegral R S).obj L).obj.pairing x (y + z) =
      ((baseChangeIntegral R S).obj L).obj.pairing x y +
        ((baseChangeIntegral R S).obj L).obj.pairing x z :=
  BilinModuleCat.pairing_add_right ((baseChangeIntegral R S).obj L).obj x y z

theorem baseChangeIntegral_quadraticMap_add (L : IntegralLatticeCat R)
    (x y : TensorProduct R S L.obj.carrier) :
    quadraticMap ((baseChangeIntegral R S).obj L) (x + y) =
      quadraticMap ((baseChangeIntegral R S).obj L) x +
        quadraticMap ((baseChangeIntegral R S).obj L) y +
          (((baseChangeIntegral R S).obj L).obj.pairing x y +
            ((baseChangeIntegral R S).obj L).obj.pairing y x) := by
  change ((baseChangeIntegral R S).obj L).obj.pairing (x + y) (x + y) = _
  rw [baseChangeIntegral_pairing_add_left (R := R) S L,
    baseChangeIntegral_pairing_add_right (R := R) S L,
    baseChangeIntegral_pairing_add_right (R := R) S L]
  simp only [quadraticMap, LinearMap.BilinMap.toQuadraticMap_apply,
    BilinModuleCat.bilinMap_apply]
  abel

theorem symmetrized_pairing_mem_of_isQuadraticallyEven
    (L : IntegralLatticeCat R) (I : Ideal R)
    (hL : IsQuadraticallyEven L I) (x y : L.obj.carrier) :
    L.obj.pairing x y + L.obj.pairing y x ∈ I := by
  rw [isQuadraticallyEven_iff_value_mem] at hL
  have h := I.sub_mem (I.sub_mem (hL (x + y)) (hL x)) (hL y)
  change QuadraticMap.polar (quadraticMap L) x y ∈ I at h
  rw [quadraticMap, LinearMap.BilinMap.polar_toQuadraticMap] at h
  exact h

theorem baseChangeIntegral_symmetrized_pairing_mem
    (L : IntegralLatticeCat R) (I : Ideal R)
    (hL : IsQuadraticallyEven L I)
    (x y : TensorProduct R S L.obj.carrier) :
    ((baseChangeIntegral R S).obj L).obj.pairing x y +
      ((baseChangeIntegral R S).obj L).obj.pairing y x ∈
        Ideal.map (algebraMap R S) I := by
  induction x using TensorProduct.induction_on with
  | zero =>
    have hEq :
        ((baseChangeIntegral R S).obj L).obj.pairing 0 y +
          ((baseChangeIntegral R S).obj L).obj.pairing y 0 = 0 := by
      rw [baseChangeIntegral_pairing_zero_left (R := R) S L y,
        baseChangeIntegral_pairing_zero_right (R := R) S L y, zero_add]
    exact hEq.symm ▸ (Ideal.map (algebraMap R S) I).zero_mem
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero =>
      have hEq :
          ((baseChangeIntegral R S).obj L).obj.pairing (a ⊗ₜ[R] x) 0 +
            ((baseChangeIntegral R S).obj L).obj.pairing 0 (a ⊗ₜ[R] x) = 0 := by
        rw [baseChangeIntegral_pairing_zero_right (R := R) S L (a ⊗ₜ[R] x),
          baseChangeIntegral_pairing_zero_left (R := R) S L (a ⊗ₜ[R] x),
          zero_add]
      exact hEq.symm ▸ (Ideal.map (algebraMap R S) I).zero_mem
    | tmul b y =>
      have hxy := symmetrized_pairing_mem_of_isQuadraticallyEven L I hL x y
      have hMap : algebraMap R S
          (L.obj.pairing x y + L.obj.pairing y x) ∈
          Ideal.map (algebraMap R S) I :=
        Ideal.mem_map_of_mem (algebraMap R S) hxy
      have hMul := (Ideal.map (algebraMap R S) I).smul_mem (a * b) hMap
      simpa [baseChangeIntegral_pairing_tmul, map_add, Algebra.smul_def,
        mul_add, mul_comm, mul_left_comm, mul_assoc] using hMul
    | add y₁ y₂ hy₁ hy₂ =>
      rw [baseChangeIntegral_pairing_add_right,
        baseChangeIntegral_pairing_add_left]
      convert (Ideal.map (algebraMap R S) I).add_mem hy₁ hy₂ using 1
      all_goals abel
  | add x₁ x₂ hx₁ hx₂ =>
    rw [baseChangeIntegral_pairing_add_left,
      baseChangeIntegral_pairing_add_right]
    convert (Ideal.map (algebraMap R S) I).add_mem hx₁ hx₂ using 1
    all_goals abel

theorem baseChangeIntegral_isQuadraticallyEven
    (L : IntegralLatticeCat R) (I : Ideal R)
    (hL : IsQuadraticallyEven L I) :
    IsQuadraticallyEven ((baseChangeIntegral R S).obj L)
      (Ideal.map (algebraMap R S) I) := by
  rw [isQuadraticallyEven_iff_value_mem]
  intro x
  change TensorProduct R S L.obj.carrier at x
  induction x using TensorProduct.induction_on with
  | zero =>
    change 0 ∈ Ideal.map (algebraMap R S) I
    exact (Ideal.map (algebraMap R S) I).zero_mem
  | tmul a x =>
    change ((baseChangeIntegral R S).obj L).obj.pairing
      (a ⊗ₜ[R] x) (a ⊗ₜ[R] x) ∈ Ideal.map (algebraMap R S) I
    rw [baseChangeIntegral_pairing_tmul]
    rw [isQuadraticallyEven_iff_value_mem] at hL
    have hx := hL x
    change L.obj.pairing x x ∈ I at hx
    have hMap : algebraMap R S (L.obj.pairing x x) ∈
        Ideal.map (algebraMap R S) I :=
      Ideal.mem_map_of_mem (algebraMap R S) hx
    simpa [Algebra.smul_def] using
      (Ideal.map (algebraMap R S) I).smul_mem (a * a) hMap
  | add x y hx hy =>
    have hSym := baseChangeIntegral_symmetrized_pairing_mem S L I hL x y
    rw [baseChangeIntegral_quadraticMap_add (R := R) S L x y]
    exact (Ideal.map (algebraMap R S) I).add_mem
      ((Ideal.map (algebraMap R S) I).add_mem hx hy) hSym

theorem baseChangeIntegral_isBilinearlyEven
    (L : IntegralLatticeCat R) (I : Ideal R)
    (hL : IsBilinearlyEven L I) :
    IsBilinearlyEven ((baseChangeIntegral R S).obj L)
      (Ideal.map (algebraMap R S) I) := by
  rw [isBilinearlyEven_iff_pairing_mem] at hL ⊢
  intro x y
  change TensorProduct R S L.obj.carrier at x y
  induction x using TensorProduct.induction_on with
  | zero =>
    exact (baseChangeIntegral_pairing_zero_left (R := R) S L y).symm ▸
      (Ideal.map (algebraMap R S) I).zero_mem
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero =>
      exact (baseChangeIntegral_pairing_zero_right (R := R) S L
        (a ⊗ₜ[R] x)).symm ▸ (Ideal.map (algebraMap R S) I).zero_mem
    | tmul b y =>
      have hxy : algebraMap R S (L.obj.pairing x y) ∈
          Ideal.map (algebraMap R S) I :=
        Ideal.mem_map_of_mem (algebraMap R S) (hL x y)
      simpa [baseChangeIntegral_pairing_tmul, Algebra.smul_def] using
        (Ideal.map (algebraMap R S) I).smul_mem (a * b) hxy
    | add y₁ y₂ hy₁ hy₂ =>
      rw [baseChangeIntegral_pairing_add_right]
      exact (Ideal.map (algebraMap R S) I).add_mem hy₁ hy₂
  | add x₁ x₂ hx₁ hx₂ =>
    rw [baseChangeIntegral_pairing_add_left]
    exact (Ideal.map (algebraMap R S) I).add_mem hx₁ hx₂

end BaseChangeEvenness

end Evenness

/-- Rational lattices obtained from `R`-lattices. -/
abbrev RationalLatticeCat [IsDomain R] :=
  LatticeCat (FractionRing R) (FractionRing R)

/-- Rationalization is scalar extension followed by the canonical value isomorphism. -/
noncomputable def rationalization [IsDomain R] :
    IntegralLatticeCat R ⥤ RationalLatticeCat R :=
  baseChange R R (FractionRing R) ⋙
    changeValue (FractionRing R) (TensorProduct R (FractionRing R) R)
      (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
        (FractionRing R)).toLinearMap

section MetricDual

variable [IsDomain R]

abbrev RationalSpan (L : IntegralLatticeCat R) :=
  TensorProduct R (FractionRing R) L.obj.carrier

/-- The canonical map into the rational span. -/
def toRationalSpan (L : IntegralLatticeCat R) :
    L.obj.carrier →ₗ[R] RationalSpan R L :=
  TensorProduct.mk R (FractionRing R) L.obj.carrier 1

/-- The image of the lattice inside its rational span. -/
def integralImage (L : IntegralLatticeCat R) :
    Submodule R (RationalSpan R L) :=
  LinearMap.range (toRationalSpan R L)

/-- The rationalized bilinear form. -/
noncomputable abbrev rationalizedForm (L : IntegralLatticeCat R) :
    LinearMap.BilinForm (FractionRing R) (RationalSpan R L) :=
  LinearMap.compr₂ (LinearMap.BilinMap.baseChange (FractionRing R) L.obj.bilinMap)
    (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
      (FractionRing R)).toLinearMap

omit [IsDomain R] in
theorem rationalizedForm_tmul (L : IntegralLatticeCat R)
    (a b : FractionRing R) (x y : L.obj.carrier) :
    rationalizedForm R L (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R (FractionRing R) (L.obj.pairing x y) := by
  simp [rationalizedForm, BilinModuleCat.bilinMap, BilinModuleCat.adjoint,
    BilinModuleCat.pairing, Algebra.smul_def, mul_comm]

/-- The image of an ideal of `R` inside its fraction field. -/
def idealInFractionRing (I : Ideal R) : Submodule R (FractionRing R) :=
  Submodule.map (Algebra.linearMap R (FractionRing R)) I

/-- The value module `Frac(R) / I`. -/
abbrev IdealValueQuotient (I : Ideal R) :=
  FractionRing R ⧸ idealInFractionRing R I

/-- The quotient map `Frac(R) → Frac(R) / I`. -/
def idealValueProjection (I : Ideal R) :
    FractionRing R →ₗ[R] IdealValueQuotient R I :=
  Submodule.mkQ (idealInFractionRing R I)

/-- Pair a rational vector with the original lattice. -/
noncomputable def rationalPairingMap (L : IntegralLatticeCat R) :
    RationalSpan R L →ₗ[R] (L.obj.carrier →ₗ[R] FractionRing R) where
  toFun x := ((rationalizedForm R L x).restrictScalars R).comp
    (toRationalSpan R L)
  map_add' x y := by
    ext z
    simp
  map_smul' r x := by
    ext z
    simp [Algebra.smul_def]

/-- The map whose kernel is the metric `I`-dual. -/
noncomputable def idealDualMap (L : IntegralLatticeCat R) (I : Ideal R) :
    RationalSpan R L →ₗ[R]
      (L.obj.carrier →ₗ[R] IdealValueQuotient R I) where
  toFun x := (idealValueProjection R I).comp (rationalPairingMap R L x)
  map_add' x y := by
    ext z
    simp
  map_smul' r x := by
    ext z
    simp

/-- The metric `I`-dual, defined as a kernel without generators. -/
noncomputable def idealDual (L : IntegralLatticeCat R) (I : Ideal R) :
    Submodule R (RationalSpan R L) :=
  LinearMap.ker (idealDualMap R L I)

noncomputable def idealDualInclusion (L : IntegralLatticeCat R) (I : Ideal R) :
    idealDual R L I →ₗ[R] RationalSpan R L :=
  (idealDual R L I).subtype

omit [IsDomain R] in
theorem exact_idealDual (L : IntegralLatticeCat R) (I : Ideal R) :
    Function.Exact (idealDualInclusion R L I) (idealDualMap R L I) :=
  LinearMap.exact_subtype_ker_map (idealDualMap R L I)

theorem toRationalSpan_mem_idealDual_iff (L : IntegralLatticeCat R)
    (I : Ideal R) (x : L.obj.carrier) :
    toRationalSpan R L x ∈ idealDual R L I ↔
      ∀ y, L.obj.pairing x y ∈ I := by
  constructor
  · intro hx y
    rw [idealDual, LinearMap.mem_ker] at hx
    have hy := LinearMap.congr_fun hx y
    change idealValueProjection R I
      (rationalizedForm R L (toRationalSpan R L x)
        (toRationalSpan R L y)) = 0 at hy
    change idealValueProjection R I
      (rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) = 0 at hy
    rw [rationalizedForm_tmul] at hy
    simp only [one_mul] at hy
    rw [idealValueProjection, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, idealInFractionRing] at hy
    rcases hy with ⟨a, ha, hEq⟩
    have : a = L.obj.pairing x y :=
      (FaithfulSMul.algebraMap_injective R (FractionRing R)) hEq
    simpa [this] using ha
  · intro h
    rw [idealDual, LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    change idealValueProjection R I
      (rationalizedForm R L (toRationalSpan R L x)
        (toRationalSpan R L y)) = 0
    change idealValueProjection R I
      (rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) = 0
    rw [rationalizedForm_tmul]
    simp only [one_mul]
    rw [idealValueProjection, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, idealInFractionRing]
    exact ⟨L.obj.pairing x y, h y, rfl⟩

/-- The canonical map to the rational span factors through the metric `I`-dual. -/
def CanonicalMapLiftsToIdealDual (L : IntegralLatticeCat R) (I : Ideal R) : Prop :=
  ∃ ι : L.obj.carrier →ₗ[R] idealDual R L I,
    idealDualInclusion R L I ∘ₗ ι = toRationalSpan R L

theorem isBilinearlyEven_iff_canonicalMapLiftsToIdealDual
    (L : IntegralLatticeCat R) (I : Ideal R) :
    IsBilinearlyEven L I ↔ CanonicalMapLiftsToIdealDual R L I := by
  rw [isBilinearlyEven_iff_pairing_mem]
  constructor
  · intro h
    refine ⟨LinearMap.codRestrict (idealDual R L I) (toRationalSpan R L) ?_, ?_⟩
    · intro x
      exact (toRationalSpan_mem_idealDual_iff R L I x).mpr (h x)
    · ext x
      rfl
  · rintro ⟨ι, hι⟩ x y
    apply (toRationalSpan_mem_idealDual_iff R L I x).mp
    have hx : idealDualInclusion R L I (ι x) = toRationalSpan R L x :=
      LinearMap.congr_fun hι x
    rw [← hx]
    exact (ι x).property

/-- The metric dual as a submodule of the rational span. -/
noncomputable abbrev metricDual (L : IntegralLatticeCat R) :
    Submodule R (RationalSpan R L) :=
  (rationalizedForm R L).dualSubmodule (integralImage R L)

/-- The specified inclusion `L♯ → L ⊗_R Frac(R)`. -/
noncomputable def metricDualInclusion (L : IntegralLatticeCat R) :
    metricDual R L →ₗ[R] RationalSpan R L :=
  (metricDual R L).subtype

/-- The canonical map `L → L♯`. -/
noncomputable def toMetricDual (L : IntegralLatticeCat R) :
    L.obj.carrier →ₗ[R] metricDual R L :=
  LinearMap.codRestrict (metricDual R L) (toRationalSpan R L) (by
    intro x
    change (toRationalSpan R L) x ∈
      (rationalizedForm R L).dualSubmodule (integralImage R L)
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rcases hy with ⟨y, rfl⟩
    refine Submodule.mem_one.mpr ⟨L.obj.pairing x y, ?_⟩
    change algebraMap R (FractionRing R) (L.obj.pairing x y) =
      rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
    rw [rationalizedForm_tmul]
    simp)

/-- Rational nondegeneracy means that the adjoint of the extended form is bijective. -/
def IsGenericallyNondegenerate (L : IntegralLatticeCat R) : Prop :=
  Function.Bijective (rationalizedForm R L)

/-- The Riesz equivalence supplied by the extended form and rational nondegeneracy. -/
noncomputable def rationalAdjointEquiv (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    RationalSpan R L ≃ₗ[FractionRing R]
      Module.Dual (FractionRing R) (RationalSpan R L) :=
  LinearEquiv.ofBijective (rationalizedForm R L) hL

/-- The Riesz realization of `Hom_R(L,R)` inside the rational span. -/
noncomputable def rieszEmbedding (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    L.obj.valueDual →ₗ[R] RationalSpan R L :=
  (rationalAdjointEquiv R L hL).symm.toLinearMap.restrictScalars R ∘ₗ
    Module.Dual.baseChange (FractionRing R)

/-- The extended form, restricted to `R`-scalars. -/
noncomputable def restrictedRationalizedForm (L : IntegralLatticeCat R) :
    LinearMap.BilinMap R (RationalSpan R L) (FractionRing R) :=
  LinearMap.mk₂ R (fun x y ↦ rationalizedForm R L x y)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)

/-- The form on `Hom_R(L,R)` transported through its Riesz realization. -/
noncomputable def rieszDualBilinMap (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.BilinMap R L.obj.valueDual (FractionRing R) :=
  (restrictedRationalizedForm R L).compl₁₂
    (rieszEmbedding R L hL) (rieszEmbedding R L hL)

/-- Tensor-hom form transported to `Hom_R(L,R)` by the Riesz realization. -/
noncomputable def rieszDualForm (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    TensorProduct R L.obj.valueDual L.obj.valueDual →ₗ[R] FractionRing R :=
  (TensorProduct.lift.equiv (.id R) L.obj.valueDual L.obj.valueDual
    (FractionRing R)) (rieszDualBilinMap R L hL)

/-- `Hom_R(L,R)` with the form supplied by `b_K` and its Riesz equivalence. -/
noncomputable def rieszDualBilinObject (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    BilinModuleCat R (FractionRing R) :=
  op ⟨op (ModuleCat.of R L.obj.valueDual), rieszDualForm R L hL⟩

omit [IsDomain R] in
theorem rationalizedForm_isSymmetric (L : IntegralLatticeCat R) :
    ∀ x y, rationalizedForm R L x y = rationalizedForm R L y x := by
  intro x y
  have hsymm : ∀ a b, L.obj.bilinMap a b = L.obj.bilinMap b a := by
    intro a b
    exact L.property.2.2 a b
  change (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
      (FractionRing R))
      (LinearMap.BilinMap.baseChange (FractionRing R) L.obj.bilinMap x y) =
    (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
      (FractionRing R))
      (LinearMap.BilinMap.baseChange (FractionRing R) L.obj.bilinMap y x)
  rw [LinearMap.BilinMap.baseChange_isSymm hsymm]

omit [IsDomain R] in
theorem rieszDualBilinObject_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    (rieszDualBilinObject R L hL).IsSymmetric := by
  intro f g
  exact rationalizedForm_isSymmetric R L _ _

omit [IsDomain R] in
theorem rieszEmbedding_adjoint (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (x : L.obj.carrier) :
    rieszEmbedding R L hL (L.obj.adjoint x) = toRationalSpan R L x := by
  apply (rationalAdjointEquiv R L hL).injective
  simp only [rieszEmbedding, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    toRationalSpan]
  change (rationalAdjointEquiv R L hL)
      ((rationalAdjointEquiv R L hL).symm
        (Module.Dual.baseChange (FractionRing R) (L.obj.adjoint x))) =
    (rationalAdjointEquiv R L hL) (1 ⊗ₜ[R] x)
  rw [LinearEquiv.apply_symm_apply]
  change Module.Dual.baseChange (FractionRing R) (L.obj.adjoint x) =
    rationalizedForm R L (1 ⊗ₜ[R] x)
  ext z
  simp [BilinModuleCat.adjoint]

omit [IsDomain R] in
theorem rieszDualBilinMap_adjoint (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (x y : L.obj.carrier) :
    rieszDualBilinMap R L hL (L.obj.adjoint x) (L.obj.adjoint y) =
      algebraMap R (FractionRing R) (L.obj.pairing x y) := by
  change rationalizedForm R L
    (rieszEmbedding R L hL (L.obj.adjoint x))
    (rieszEmbedding R L hL (L.obj.adjoint y)) = _
  rw [rieszEmbedding_adjoint, rieszEmbedding_adjoint]
  change rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) = _
  rw [rationalizedForm_tmul]
  simp

/-- Change an integral form from `R`-values to `Frac(R)`-values. -/
noncomputable def fractionValuedLattice (L : IntegralLatticeCat R) :
    LatticeCat R (FractionRing R) :=
  (changeValue R R (Algebra.linearMap R (FractionRing R))).obj L

/-- The Riesz model of `L♯`: `Hom_R(L,R)` with the form induced by `b_K`. -/
noncomputable def rieszDualLattice (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LatticeCat R (FractionRing R) := by
  letI : Module.Finite R L.obj.carrier := L.property.1
  letI : Module.Projective R L.obj.carrier := L.property.2.1
  refine ⟨rieszDualBilinObject R L hL, ?_⟩
  change Module.Finite R L.obj.valueDual ∧ Module.Projective R L.obj.valueDual ∧
    (rieszDualBilinObject R L hL).IsSymmetric
  exact ⟨inferInstance, inferInstance, rieszDualBilinObject_isSymmetric R L hL⟩

/-- The adjoint is an isometry after changing values to `Frac(R)`. -/
noncomputable def toRieszDualBilin (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    (fractionValuedLattice R L).obj ⟶ rieszDualBilinObject R L hL := by
  refine Quiver.Hom.op (CategoryOfElements.homMk _ _
    (op (ModuleCat.ofHom L.obj.adjoint)) ?_)
  dsimp [bilinearForms]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    exact rieszDualBilinMap_adjoint R L hL x y
  | add x y hx hy => simp [hx, hy]

/-- The adjoint `L → L♯` in the category of `Frac(R)`-valued `R`-lattices. -/
noncomputable def toRieszDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    fractionValuedLattice R L ⟶ rieszDualLattice R L hL :=
  ObjectProperty.homMk (toRieszDualBilin R L hL)

omit [IsDomain R] in
theorem rationalizedForm_rieszEmbedding (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (f : L.obj.valueDual)
    (x : L.obj.carrier) :
    rationalizedForm R L (rieszEmbedding R L hL f) (toRationalSpan R L x) =
      algebraMap R (FractionRing R) (f x) := by
  change (rationalAdjointEquiv R L hL) (rieszEmbedding R L hL f)
      (1 ⊗ₜ[R] x) = _
  simp [rieszEmbedding, Algebra.smul_def]

/-- The Riesz model maps into the metric-dual submodule of the rational span. -/
noncomputable def rieszToMetricDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    L.obj.valueDual →ₗ[R] metricDual R L :=
  LinearMap.codRestrict (metricDual R L) (rieszEmbedding R L hL) (by
    intro f
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rcases hy with ⟨y, rfl⟩
    refine Submodule.mem_one.mpr ⟨f y, ?_⟩
    exact (rationalizedForm_rieszEmbedding R L hL f y).symm)

@[simp]
theorem rieszToMetricDual_coe (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (f : L.obj.valueDual) :
    (rieszToMetricDual R L hL f : RationalSpan R L) = rieszEmbedding R L hL f :=
  rfl

/-- The integral lattice mapped onto its image in the rational span. -/
def toIntegralImage (L : IntegralLatticeCat R) :
    L.obj.carrier →ₗ[R] integralImage R L :=
  (toRationalSpan R L).rangeRestrict

/-- A metric-dual vector defines an `R`-linear functional by integral pairing. -/
noncomputable def metricDualToValueDual (L : IntegralLatticeCat R) :
    metricDual R L →ₗ[R] L.obj.valueDual where
  toFun v := ((rationalizedForm R L).dualSubmoduleToDual
    (integralImage R L) v).comp (toIntegralImage R L)
  map_add' v w := by
    ext x
    simp [toIntegralImage]
  map_smul' r v := by
    ext x
    simp [toIntegralImage]

theorem metricDualToValueDual_rieszToMetricDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (f : L.obj.valueDual) :
    metricDualToValueDual R L (rieszToMetricDual R L hL f) = f := by
  ext x
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  change algebraMap R (FractionRing R)
      ((rationalizedForm R L).dualSubmoduleParing
        (rieszToMetricDual R L hL f) (toIntegralImage R L x)) =
    algebraMap R (FractionRing R) (f x)
  rw [LinearMap.BilinForm.dualSubmoduleParing_spec]
  exact rationalizedForm_rieszEmbedding R L hL f x

theorem rieszToMetricDual_metricDualToValueDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (v : metricDual R L) :
    rieszToMetricDual R L hL (metricDualToValueDual R L v) = v := by
  apply Subtype.ext
  apply (rationalAdjointEquiv R L hL).injective
  change (rationalAdjointEquiv R L hL)
      ((rationalAdjointEquiv R L hL).symm
        (Module.Dual.baseChange (FractionRing R) (metricDualToValueDual R L v))) =
    rationalizedForm R L v
  rw [LinearEquiv.apply_symm_apply]
  ext x
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply]
  simp only [LinearMap.coe_restrictScalars]
  rw [Module.Dual.baseChange_apply_tmul]
  simp only [Algebra.smul_def, mul_one]
  change algebraMap R (FractionRing R)
      ((rationalizedForm R L).dualSubmoduleParing v (toIntegralImage R L x)) =
    rationalizedForm R L v (1 ⊗ₜ[R] x)
  exact (rationalizedForm R L).dualSubmoduleParing_spec v (toIntegralImage R L x)

/-- The Riesz model and the metric-dual submodule are isomorphic as `R`-modules. -/
noncomputable def rieszMetricDualEquiv (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    L.obj.valueDual ≃ₗ[R] metricDual R L :=
  { toLinearMap := rieszToMetricDual R L hL
    invFun := metricDualToValueDual R L
    left_inv := metricDualToValueDual_rieszToMetricDual R L hL
    right_inv := rieszToMetricDual_metricDualToValueDual R L hL }

@[simp]
theorem rieszMetricDualEquiv_adjoint (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (x : L.obj.carrier) :
    rieszMetricDualEquiv R L hL (L.obj.adjoint x) = toMetricDual R L x := by
  apply Subtype.ext
  change rieszEmbedding R L hL (L.obj.adjoint x) = toRationalSpan R L x
  exact rieszEmbedding_adjoint R L hL x

/-- The restriction of `b_K` to the metric-dual submodule. -/
noncomputable def metricDualBilinMap (L : IntegralLatticeCat R) :
    LinearMap.BilinMap R (metricDual R L) (FractionRing R) :=
  (restrictedRationalizedForm R L).compl₁₂
    (metricDualInclusion R L) (metricDualInclusion R L)

/-- Tensor-hom form on the metric-dual submodule. -/
noncomputable def metricDualForm (L : IntegralLatticeCat R) :
    TensorProduct R (metricDual R L) (metricDual R L) →ₗ[R] FractionRing R :=
  (TensorProduct.lift.equiv (.id R) (metricDual R L) (metricDual R L)
    (FractionRing R)) (metricDualBilinMap R L)

/-- The metric dual as a bilinear object, using the restriction of `b_K`. -/
noncomputable def metricDualBilinObject (L : IntegralLatticeCat R) :
    BilinModuleCat R (FractionRing R) :=
  op ⟨op (ModuleCat.of R (metricDual R L)), metricDualForm R L⟩

theorem metricDualBilinObject_isSymmetric (L : IntegralLatticeCat R) :
    (metricDualBilinObject R L).IsSymmetric := by
  intro x y
  change metricDualBilinMap R L x y = metricDualBilinMap R L y x
  change rationalizedForm R L (metricDualInclusion R L x) (metricDualInclusion R L y) =
    rationalizedForm R L (metricDualInclusion R L y) (metricDualInclusion R L x)
  exact rationalizedForm_isSymmetric R L _ _

/-- The actual metric-dual submodule as a `Frac(R)`-valued `R`-lattice. -/
noncomputable def metricDualLattice (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LatticeCat R (FractionRing R) := by
  letI : Module.Finite R L.obj.carrier := L.property.1
  letI : Module.Projective R L.obj.carrier := L.property.2.1
  letI : Module.Finite R L.obj.valueDual := inferInstance
  letI : Module.Projective R L.obj.valueDual := inferInstance
  refine ⟨metricDualBilinObject R L, ?_⟩
  change Module.Finite R (metricDual R L) ∧ Module.Projective R (metricDual R L) ∧
    (metricDualBilinObject R L).IsSymmetric
  exact ⟨Module.Finite.equiv (rieszMetricDualEquiv R L hL),
    Module.Projective.of_equiv' (rieszMetricDualEquiv R L hL),
      metricDualBilinObject_isSymmetric R L⟩

/-- The inclusion `L → L♯` preserves the `Frac(R)`-valued forms. -/
noncomputable def toMetricDualBilin (L : IntegralLatticeCat R) :
    (fractionValuedLattice R L).obj ⟶ metricDualBilinObject R L := by
  refine Quiver.Hom.op (CategoryOfElements.homMk _ _
    (op (ModuleCat.ofHom (toMetricDual R L))) ?_)
  dsimp [bilinearForms]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) =
      algebraMap R (FractionRing R) (L.obj.pairing x y)
    rw [rationalizedForm_tmul]
    simp
  | add x y hx hy => simp [hx, hy]

/-- An integral lattice in the total category of symmetric variable-valued forms. -/
noncomputable def integralSymBilWFormObject (L : IntegralLatticeCat R) : SymBilWFormCat R :=
  ⟨BilWFormCat.of (ModuleCat.of R L.obj.carrier) (ModuleCat.of R R) L.obj.form,
    L.property.2.2⟩

/-- The metric dual in the total category of symmetric variable-valued forms. -/
noncomputable def metricDualSymBilWFormObject (L : IntegralLatticeCat R) : SymBilWFormCat R :=
  ⟨⟨ModuleCat.of R (FractionRing R), metricDualBilinObject R L⟩,
    metricDualBilinObject_isSymmetric R L⟩

/-- The inclusion into the metric dual, with values changed from `R` to `Frac(R)`. -/
noncomputable def toMetricDualSymBilWForm (L : IntegralLatticeCat R) :
    integralSymBilWFormObject R L ⟶ metricDualSymBilWFormObject R L :=
  ObjectProperty.homMk
    (BilWFormCat.homMk (toMetricDual R L) (Algebra.linearMap R (FractionRing R)) (by
      intro x y
      change algebraMap R (FractionRing R) (L.obj.pairing x y) =
        rationalizedForm R L (toRationalSpan R L x) (toRationalSpan R L y)
      change algebraMap R (FractionRing R) (L.obj.pairing x y) =
        rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
      rw [rationalizedForm_tmul]
      simp))

/-- The discriminant formed module as the categorical cokernel of `L → L♯`. -/
noncomputable def discriminantSymBilWFormObject (L : IntegralLatticeCat R) : SymBilWFormCat R :=
  SymBilWFormCat.cokernelObject (toMetricDualSymBilWForm R L)

/-- The formed quotient map from the metric dual to the discriminant module. -/
noncomputable def discriminantSymBilWFormProjection (L : IntegralLatticeCat R) :
    metricDualSymBilWFormObject R L ⟶ discriminantSymBilWFormObject R L :=
  SymBilWFormCat.cokernelProjection (toMetricDualSymBilWForm R L)

/-- The quadratic map `x ↦ b_A(x,x)` on the categorical discriminant module. -/
noncomputable def discriminantSymBilWQuadraticMap (L : IntegralLatticeCat R) :
    QuadraticMap R (discriminantSymBilWFormObject R L).obj.carrier
      (discriminantSymBilWFormObject R L).obj.value :=
  LinearMap.BilinMap.toQuadraticMap
    (discriminantSymBilWFormObject R L).obj.formed.bilinMap

/-- The discriminant is the categorical cokernel among symmetric formed modules. -/
noncomputable def discriminantSymBilWFormIsCokernel (L : IntegralLatticeCat R) :
    IsColimit (SymBilWFormCat.cokernelCofork (toMetricDualSymBilWForm R L)) :=
  SymBilWFormCat.cokernelIsColimit (toMetricDualSymBilWForm R L)

/-- The value relations in the discriminant cokernel are exactly the image of `R`. -/
theorem discriminantValueRelations_eq (L : IntegralLatticeCat R) :
    BilWFormCat.cokernelValueRelations (toMetricDualSymBilWForm R L).hom =
      LinearMap.range (Algebra.linearMap R (FractionRing R)) := by
  apply le_antisymm
  · rw [BilWFormCat.cokernelValueRelations, sup_le_iff, sup_le_iff]
    constructor
    · constructor
      · exact le_rfl
      · rw [BilWFormCat.leftMixedRelations, Submodule.span_le]
        rintro _ ⟨⟨x, y⟩, rfl⟩
        change metricDual R L at y
        refine ⟨metricDualToValueDual R L y x, ?_⟩
        change algebraMap R (FractionRing R) (metricDualToValueDual R L y x) =
          rationalizedForm R L (toRationalSpan R L x) y
        rw [rationalizedForm_isSymmetric]
        exact (rationalizedForm R L).dualSubmoduleParing_spec
          y (toIntegralImage R L x)
    · rw [BilWFormCat.rightMixedRelations, Submodule.span_le]
      rintro _ ⟨⟨y, x⟩, rfl⟩
      change metricDual R L at y
      refine ⟨metricDualToValueDual R L y x, ?_⟩
      change algebraMap R (FractionRing R) (metricDualToValueDual R L y x) =
        rationalizedForm R L y (toRationalSpan R L x)
      exact (rationalizedForm R L).dualSubmoduleParing_spec
        y (toIntegralImage R L x)
  · exact le_trans le_sup_left le_sup_left

/-- The inclusion `L → L♯` in the category of `Frac(R)`-valued `R`-lattices. -/
noncomputable def toMetricDualLattice (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    fractionValuedLattice R L ⟶ metricDualLattice R L hL :=
  ObjectProperty.homMk (toMetricDualBilin R L)

omit [IsDomain R] in
theorem rieszDualBilinMap_adjoint_left (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (x : L.obj.carrier)
    (f : L.obj.valueDual) :
    rieszDualBilinMap R L hL (L.obj.adjoint x) f =
      algebraMap R (FractionRing R) (f x) := by
  change rationalizedForm R L (rieszEmbedding R L hL (L.obj.adjoint x))
    (rieszEmbedding R L hL f) = _
  rw [rieszEmbedding_adjoint, rationalizedForm_isSymmetric]
  exact rationalizedForm_rieszEmbedding R L hL f x

omit [IsDomain R] in
theorem rieszDualBilinMap_adjoint_right (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (f : L.obj.valueDual)
    (x : L.obj.carrier) :
    rieszDualBilinMap R L hL f (L.obj.adjoint x) =
      algebraMap R (FractionRing R) (f x) := by
  change rationalizedForm R L (rieszEmbedding R L hL f)
    (rieszEmbedding R L hL (L.obj.adjoint x)) = _
  rw [rieszEmbedding_adjoint]
  exact rationalizedForm_rieszEmbedding R L hL f x

/-- The value module `Frac(R) / R`. -/
abbrev FractionValueQuotient :=
  FractionRing R ⧸ LinearMap.range (Algebra.linearMap R (FractionRing R))

/-- The quotient map `Frac(R) → Frac(R) / R`. -/
def fractionValueProjection :
    FractionRing R →ₗ[R] FractionValueQuotient R :=
  Submodule.mkQ (LinearMap.range (Algebra.linearMap R (FractionRing R)))

omit [IsDomain R] in
@[simp]
theorem fractionValueProjection_algebraMap (r : R) :
    fractionValueProjection R (algebraMap R (FractionRing R) r) = 0 := by
  rw [fractionValueProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨r, rfl⟩

/-- The Riesz form after projection to `Frac(R) / R`. -/
noncomputable def quotientRieszDualBilinMap (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.BilinMap R L.obj.valueDual (FractionValueQuotient R) :=
  (rieszDualBilinMap R L hL).compr₂ (fractionValueProjection R)

omit [IsDomain R] in
theorem adjointRange_le_ker_quotientRieszDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.range L.obj.adjoint ≤ LinearMap.ker (quotientRieszDualBilinMap R L hL) := by
  rintro f ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro g
  change fractionValueProjection R
    (rieszDualBilinMap R L hL (L.obj.adjoint x) g) = 0
  rw [rieszDualBilinMap_adjoint_left, fractionValueProjection_algebraMap]

omit [IsDomain R] in
theorem adjointRange_le_flipKer_quotientRieszDual (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.range L.obj.adjoint ≤
      LinearMap.ker (quotientRieszDualBilinMap R L hL).flip := by
  rintro f ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro g
  change fractionValueProjection R
    (rieszDualBilinMap R L hL g (L.obj.adjoint x)) = 0
  rw [rieszDualBilinMap_adjoint_right, fractionValueProjection_algebraMap]

/-- The discriminant bilinear map on `A_L = L*/iota_L(L)`. -/
noncomputable def discriminantBilinMap (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LinearMap.BilinMap R L.obj.defect (FractionValueQuotient R) :=
  (quotientRieszDualBilinMap R L hL).liftQ₂
    (LinearMap.range L.obj.adjoint) (LinearMap.range L.obj.adjoint)
    (adjointRange_le_ker_quotientRieszDual R L hL)
    (adjointRange_le_flipKer_quotientRieszDual R L hL)

/-- Tensor-hom form of the discriminant bilinear map. -/
noncomputable def discriminantForm (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    TensorProduct R L.obj.defect L.obj.defect →ₗ[R] FractionValueQuotient R :=
  (TensorProduct.lift.equiv (.id R) L.obj.defect L.obj.defect
    (FractionValueQuotient R)) (discriminantBilinMap R L hL)

/-- The discriminant module with its `Frac(R) / R`-valued bilinear form. -/
noncomputable def discriminantBilinObject (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    BilinModuleCat R (FractionValueQuotient R) :=
  op ⟨op (ModuleCat.of R L.obj.defect), discriminantForm R L hL⟩

omit [IsDomain R] in
@[simp]
theorem discriminantBilinMap_mk (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (f g : L.obj.valueDual) :
    discriminantBilinMap R L hL
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      fractionValueProjection R (rieszDualBilinMap R L hL f g) :=
  rfl

omit [IsDomain R] in
theorem rieszDualBilinMap_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    ∀ f g, rieszDualBilinMap R L hL f g = rieszDualBilinMap R L hL g f := by
  intro f g
  exact rationalizedForm_isSymmetric R L _ _

omit [IsDomain R] in
theorem discriminantBilinMap_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    ∀ x y, discriminantBilinMap R L hL x y = discriminantBilinMap R L hL y x := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    induction y using Submodule.Quotient.induction_on with
    | _ g =>
      change fractionValueProjection R (rieszDualBilinMap R L hL f g) =
        fractionValueProjection R (rieszDualBilinMap R L hL g f)
      rw [rieszDualBilinMap_isSymmetric]

omit [IsDomain R] in
theorem discriminantBilinObject_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    (discriminantBilinObject R L hL).IsSymmetric :=
  discriminantBilinMap_isSymmetric R L hL

/-- `A_L` in the category of finite symmetric `Frac(R) / R`-valued form modules. -/
noncomputable def discriminantFormModule (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    FiniteFormCat R (FractionValueQuotient R) := by
  letI : Module.Finite R L.obj.carrier := L.property.1
  letI : Module.Projective R L.obj.carrier := L.property.2.1
  refine ⟨discriminantBilinObject R L hL, ?_⟩
  change Module.Finite R L.obj.defect ∧
    (discriminantBilinObject R L hL).IsSymmetric
  exact ⟨inferInstance, discriminantBilinObject_isSymmetric R L hL⟩

/-- The Riesz model after projection of its values to `Frac(R) / R`. -/
noncomputable def projectedRieszDualLattice (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    LatticeCat R (FractionValueQuotient R) :=
  (changeValue R (FractionRing R) (fractionValueProjection R)).obj
    (rieszDualLattice R L hL)

/-- The projected Riesz model, regarded as a finite symmetric form module. -/
noncomputable def projectedRieszDualFiniteForm (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    FiniteFormCat R (FractionValueQuotient R) :=
  ⟨(projectedRieszDualLattice R L hL).obj,
    ⟨(projectedRieszDualLattice R L hL).property.1,
      (projectedRieszDualLattice R L hL).property.2.2⟩⟩

/-- The quotient projection `L♯ → A_L` preserves the projected forms. -/
noncomputable def discriminantProjectionBilin (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    (projectedRieszDualLattice R L hL).obj ⟶ discriminantBilinObject R L hL := by
  refine Quiver.Hom.op (CategoryOfElements.homMk _ _
    (op (ModuleCat.ofHom L.obj.defectProjection)) ?_)
  dsimp [bilinearForms]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => rfl
  | add x y hx hy => simp [hx, hy]

/-- The quotient projection `L♯ → A_L` in the finite-form category. -/
noncomputable def discriminantProjection (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    projectedRieszDualFiniteForm R L hL ⟶ discriminantFormModule R L hL :=
  ObjectProperty.homMk (discriminantProjectionBilin R L hL)

/-- The associated quadratic map `q(x) = b_A(x,x)` on the discriminant module. -/
noncomputable def discriminantQuadraticMap (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) :
    QuadraticMap R L.obj.defect (FractionValueQuotient R) :=
  (discriminantBilinMap R L hL).toQuadraticMap

omit [IsDomain R] in
@[simp]
theorem discriminantQuadraticMap_apply (L : IntegralLatticeCat R)
    (hL : IsGenericallyNondegenerate R L) (x : L.obj.defect) :
    discriminantQuadraticMap R L hL x = discriminantBilinMap R L hL x x :=
  rfl

omit [IsDomain R] in
/-- The module sequence from the radical through the adjoint and its cokernel is exact. -/
theorem adjointModuleSequenceExact (L : IntegralLatticeCat R) :
    Function.Injective L.obj.radicalInclusion ∧
      Function.Exact L.obj.radicalInclusion L.obj.adjoint ∧
      Function.Exact L.obj.adjoint L.obj.defectProjection ∧
      Function.Surjective L.obj.defectProjection :=
  ⟨L.obj.radicalInclusion_injective, L.obj.exact_radical_adjoint,
    L.obj.exact_adjoint_defect, L.obj.defectProjection_surjective⟩

theorem toRationalSpan_injective (L : IntegralLatticeCat R) :
    Function.Injective (toRationalSpan R L) := by
  letI : Module.Projective R L.obj.carrier := L.property.2.1
  exact Module.Flat.tensorProduct_mk_injective R L.obj.carrier (FractionRing R)

theorem toMetricDual_injective (L : IntegralLatticeCat R) :
    Function.Injective (toMetricDual R L) := by
  intro x y h
  apply toRationalSpan_injective R L
  exact congr_arg Subtype.val h

theorem exact_radical_toMetricDual_iff (L : IntegralLatticeCat R) :
    Function.Exact L.obj.radicalInclusion (toMetricDual R L) ↔
      L.obj.IsNondegenerate := by
  rw [LinearMap.exact_iff]
  have hker : LinearMap.ker (toMetricDual R L) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx0 : x = 0 := (toMetricDual_injective R L) (by simpa using hx)
      simp [hx0]
    · exact bot_le
  have hrange : LinearMap.range L.obj.radicalInclusion = L.obj.radical :=
    Submodule.range_subtype L.obj.radical
  rw [hker, hrange]
  exact eq_comm

/-- The radical-to-metric-dual sequence is exact for a nondegenerate lattice. -/
theorem exact_radical_toMetricDual (L : IntegralLatticeCat R)
    (hL : L.obj.IsNondegenerate) :
    Function.Exact L.obj.radicalInclusion (toMetricDual R L) := by
  exact (exact_radical_toMetricDual_iff R L).mpr hL

end MetricDual

end LeanCategories.Lattices.Valued
