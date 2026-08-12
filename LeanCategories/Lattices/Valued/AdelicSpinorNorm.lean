/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IdeleGroup
public import LeanCategories.Lattices.Valued.CanonicalSpinorNorm
public import LeanCategories.Lattices.Valued.LocalDensity

/-!
# The adelic spinor norm

At every finite place the completed quadratic space is a finite symmetric form over a local
field in which `2` is invertible, so it carries the canonical spinor norm of
`CanonicalSpinorNorm.lean`. This file assembles those local norms into one homomorphism from
the finite adelic orthogonal group to the idele square classes.

The domain is the restricted product of the local orthogonal groups with respect to the
integral subgroups of `LocalDensity.lean`, so it is adelic and not a plain product. The target
is `IdeleSquareClass K`, reached through the square classes of the finite ideles. An element of
the finite adelic orthogonal group is the identity at every infinite place, so its adelic
spinor norm is trivial there.

The assembly is not automatic. A family of local square classes is the family of component
square classes of an idele exactly when almost all of the classes contain a local unit. That
restriction condition is a statement about the integral orthogonal groups at almost all places,
and it is NOT proved here: it enters as the explicit hypothesis `IsIdeleAssembled`. Everything
else, including well-definedness of the assembled map, is proved. Well-definedness rests on
`finiteIdeleComponents_injective`: a finite idele all of whose components are squares is the
square of a finite idele, because a square root of a local unit is a local unit.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open LeanCategories.Modules.Bilinear.Valued
open scoped NumberField RestrictedProduct

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]

/-! ## Two is invertible in a completion at a finite place -/

/-- A completion at a finite place has characteristic zero. -/
instance adicCompletionCharZero (w : HeightOneSpectrum (𝓞 K)) :
    CharZero (w.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (w.adicCompletion K)).injective

/-- Two is invertible in a completion at a finite place. -/
instance adicCompletionInvertibleTwo (w : HeightOneSpectrum (𝓞 K)) :
    Invertible (2 : w.adicCompletion K) :=
  invertibleOfNonzero two_ne_zero

/-! ## The local spinor norm at a finite place -/

variable (v : HeightOneSpectrum (𝓞 K)) (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))

/-- The completed quadratic space at a finite place, as a finite symmetric form. -/
abbrev localForm : FiniteFormCat (v.adicCompletion K) (v.adicCompletion K) :=
  (finiteProjectiveToFiniteForm (v.adicCompletion K) (v.adicCompletion K)).obj
    ((extendFiniteIntegralToHeightOneField (𝓞 K) K v).obj L)

/-- The canonical spinor norm of the completed quadratic space at a finite place. -/
def localSpinorNorm (hL : (localForm K v L).obj.IsLeftNondegenerate) :
    SpinorNorm (localForm K v L) :=
  canonicalSpinorNorm (localForm K v L) hL

/-- The local spinor norm as a homomorphism on the local orthogonal group. -/
def localSpinorNormHom (hL : (localForm K v L).obj.IsLeftNondegenerate) :
    LocalOrthogonalGroup K v L →* FieldSquareClass (v.adicCompletion K) :=
  (localSpinorNorm K v L hL).1

/-- The local spinor kernel at a finite place: the local isometries of trivial spinor norm. -/
def localSpinorKernel (hL : (localForm K v L).obj.IsLeftNondegenerate) :
    Subgroup (LocalOrthogonalGroup K v L) :=
  MonoidHom.ker (localSpinorNormHom K v L hL)

/-- The local spinor kernel is the kernel of the canonical spinor norm of the local form. -/
theorem localSpinorKernel_eq_spinorKernel (hL : (localForm K v L).obj.IsLeftNondegenerate) :
    localSpinorKernel K v L hL = spinorKernel (localForm K v L) (localSpinorNorm K v L hL) :=
  rfl

/-- The local spinor norm takes the expected value on a reflection. -/
theorem localSpinorNormHom_reflection (hL : (localForm K v L).obj.IsLeftNondegenerate)
    (x : (localForm K v L).obj.carrier)
    (hx : (localForm K v L).obj.pairing x x ≠ 0) :
    localSpinorNormHom K v L hL (finiteFormReflectionElement (localForm K v L) x hx) =
      fieldSquareClass (Units.mk0 ((localForm K v L).obj.pairing x x) hx) :=
  (localSpinorNorm K v L hL).2 x hx

/-! ## Square classes of finite ideles -/

/-- The square-class quotient map of a field, as a homomorphism. -/
def fieldSquareClassHom (F : Type u) [Field F] : Fˣ →* FieldSquareClass F :=
  QuotientGroup.mk' (Subgroup.square Fˣ)

@[simp]
theorem fieldSquareClassHom_apply (F : Type u) [Field F] (x : Fˣ) :
    fieldSquareClassHom F x = fieldSquareClass x :=
  rfl

/-- Evaluation of a finite idele at a finite place. -/
def finiteIdeleEval : FiniteIdeleGroup K →* (v.adicCompletion K)ˣ where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The square classes of all components of a finite idele. -/
def finiteIdeleComponentsHom :
    FiniteIdeleGroup K →*
      ∀ w : HeightOneSpectrum (𝓞 K), FieldSquareClass (w.adicCompletion K) where
  toFun x w := fieldSquareClass (x w)
  map_one' := funext fun w => map_one ((fieldSquareClassHom _).comp (finiteIdeleEval K w))
  map_mul' x y :=
    funext fun w => map_mul ((fieldSquareClassHom _).comp (finiteIdeleEval K w)) x y

/-- The square classes of the finite ideles. -/
abbrev FiniteIdeleSquareClass := FiniteIdeleGroup K ⧸ Subgroup.square (FiniteIdeleGroup K)

/-- A field element whose square lies in a valuation subring lies in that subring. -/
theorem mem_of_mul_self_mem {F : Type u} [Field F] (O : ValuationSubring F) {x : F}
    (hx : x * x ∈ O) : x ∈ O := by
  rcases O.mem_or_inv_mem x with h | h
  · exact h
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem O
    · simpa [mul_inv_cancel_right₀ hx0] using mul_mem hx h

/-- A unit whose square is an integral unit is an integral unit. -/
theorem mem_units_of_mul_self_mem_units {F : Type u} [Field F] (O : ValuationSubring F)
    {x : Fˣ} (h : x * x ∈ (Submonoid.ofClass O).units) :
    x ∈ (Submonoid.ofClass O).units := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨mem_of_mul_self_mem O ?_, mem_of_mul_self_mem O ?_⟩
  · simpa using h1
  · simpa using h2

/-- A finite idele whose components are all squares is a square. -/
theorem isSquare_of_forall_isSquare {x : FiniteIdeleGroup K}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), IsSquare (x w)) : IsSquare x := by
  choose y hy using h
  refine ⟨⟨y, ?_⟩, ?_⟩
  · refine x.2.mono fun w hw => mem_units_of_mul_self_mem_units _ ?_
    rw [← hy w]
    exact hw
  · exact DFunLike.ext _ _ hy

/-- The square classes of the components of a finite idele square class. -/
def finiteIdeleComponents :
    FiniteIdeleSquareClass K →*
      ∀ w : HeightOneSpectrum (𝓞 K), FieldSquareClass (w.adicCompletion K) :=
  QuotientGroup.lift _ (finiteIdeleComponentsHom K) <| by
    rintro x ⟨y, rfl⟩
    funext w
    change fieldSquareClass (y w * y w) = 1
    rw [fieldSquareClass_mul, ← sq, modSquares_sq]

/-- The component square classes determine the square class of a finite idele. -/
theorem finiteIdeleComponents_injective :
    Function.Injective (finiteIdeleComponents K) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  induction c using QuotientGroup.induction_on with
  | _ x =>
    refine (QuotientGroup.eq_one_iff _).mpr (isSquare_of_forall_isSquare K fun w => ?_)
    exact (QuotientGroup.eq_one_iff _).mp (congrFun hc w)

/-! ## Finite ideles inside the ideles -/

/-- A finite idele is an idele which is trivial at every infinite place. -/
def finiteToIdele : FiniteIdeleGroup K →* IdeleGroup K :=
  MonoidHom.inr (InfiniteIdeleGroup K) (FiniteIdeleGroup K)

/-- Square classes of finite ideles are square classes of ideles. -/
def finiteToIdeleSquareClass : FiniteIdeleSquareClass K →* IdeleSquareClass K :=
  QuotientGroup.map _ _ (finiteToIdele K) <| by
    intro x hx
    exact Subgroup.mem_square.mpr (Subgroup.mem_square.mp hx |>.map (finiteToIdele K))

/-- The square class of an idele at a finite place. -/
def ideleComponentHom : IdeleGroup K →* FieldSquareClass (v.adicCompletion K) :=
  (fieldSquareClassHom _).comp ((finiteIdeleEval K v).comp (MonoidHom.snd _ _))

/-- The square class of an idele square class at a finite place. -/
def ideleLocalSquareClass : IdeleSquareClass K →* FieldSquareClass (v.adicCompletion K) :=
  QuotientGroup.lift _ (ideleComponentHom K v) <| by
    rintro x ⟨y, rfl⟩
    change fieldSquareClass (y.2 v * y.2 v) = 1
    rw [fieldSquareClass_mul, ← sq, modSquares_sq]

/-- The local square class of an included finite idele class is its local square class. -/
theorem ideleLocalSquareClass_finiteToIdeleSquareClass (c : FiniteIdeleSquareClass K) :
    ideleLocalSquareClass K v (finiteToIdeleSquareClass K c) =
      finiteIdeleComponents K c v := by
  induction c using QuotientGroup.induction_on with
  | _ x => rfl

/-! ## The finite adelic orthogonal group -/

/-- The finite adelic orthogonal group: the restricted product of the local orthogonal groups
with respect to the integral subgroups. -/
abbrev AdelicOrthogonalGroup :=
  Πʳ w : HeightOneSpectrum (𝓞 K),
    [LocalOrthogonalGroup K w L, LocalIntegralOrthogonalSubgroup K w L]

/-- The family of local spinor norms of an adelic isometry. -/
def localSpinorNormFamily
    (hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate) :
    AdelicOrthogonalGroup K L →*
      ∀ w : HeightOneSpectrum (𝓞 K), FieldSquareClass (w.adicCompletion K) where
  toFun g w := localSpinorNormHom K w L (hnd w) (g w)
  map_one' := funext fun w => map_one (localSpinorNormHom K w L (hnd w))
  map_mul' g h := funext fun w => map_mul (localSpinorNormHom K w L (hnd w)) (g w) (h w)

/-! ## The adelic spinor norm -/

/-- The restriction condition: the local spinor norms of an adelic isometry are the component
square classes of a single idele.

This is the one arithmetic input that is assumed. Classically it holds because at almost all
places the completed lattice is unimodular and the spinor norms of its integral orthogonal
group are square classes of local units, so almost all components of the assembled family
contain a unit. That statement is not proved here. -/
def IsIdeleAssembled
    (hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate) : Prop :=
  ∀ g : AdelicOrthogonalGroup K L,
    localSpinorNormFamily K L hnd g ∈ (finiteIdeleComponents K).range

variable {K L}

/-- The finite adelic spinor norm, valued in the square classes of the finite ideles. -/
def finiteAdelicSpinorNorm
    {hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate}
    (hass : IsIdeleAssembled K L hnd) :
    AdelicOrthogonalGroup K L →* FiniteIdeleSquareClass K :=
  (MonoidHom.ofInjective (finiteIdeleComponents_injective K)).symm.toMonoidHom.comp
    ((localSpinorNormFamily K L hnd).codRestrict _ hass)

/-- The adelic spinor norm of a finite adelic isometry. -/
def adelicSpinorNorm
    {hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate}
    (hass : IsIdeleAssembled K L hnd) :
    AdelicOrthogonalGroup K L →* IdeleSquareClass K :=
  (finiteToIdeleSquareClass K).comp (finiteAdelicSpinorNorm hass)

/-- The component square classes of the finite adelic spinor norm are the local spinor norms. -/
theorem finiteIdeleComponents_finiteAdelicSpinorNorm
    {hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate}
    (hass : IsIdeleAssembled K L hnd) (g : AdelicOrthogonalGroup K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteIdeleComponents K (finiteAdelicSpinorNorm hass g) v =
      localSpinorNormHom K v L (hnd v) (g v) :=
  congrFun (MonoidHom.apply_ofInjective_symm (finiteIdeleComponents_injective K)
    ((localSpinorNormFamily K L hnd).codRestrict _ hass g)) v

/-- The component of the adelic spinor norm at a finite place is the local spinor norm. -/
theorem adelicSpinorNorm_localComponent
    {hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate}
    (hass : IsIdeleAssembled K L hnd) (g : AdelicOrthogonalGroup K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleLocalSquareClass K v (adelicSpinorNorm hass g) =
      localSpinorNormHom K v L (hnd v) (g v) := by
  rw [adelicSpinorNorm, MonoidHom.comp_apply,
    ideleLocalSquareClass_finiteToIdeleSquareClass,
    finiteIdeleComponents_finiteAdelicSpinorNorm]

/-! ## The adelic spinor kernel -/

/-- The adelic spinor kernel: the adelic isometries of trivial adelic spinor norm. -/
def adelicSpinorKernel
    {hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate}
    (hass : IsIdeleAssembled K L hnd) : Subgroup (AdelicOrthogonalGroup K L) :=
  MonoidHom.ker (adelicSpinorNorm hass)

/-- An adelic isometry lies in the adelic spinor kernel exactly when every one of its local
components lies in the local spinor kernel. -/
theorem mem_adelicSpinorKernel_iff
    {hnd : ∀ w : HeightOneSpectrum (𝓞 K), (localForm K w L).obj.IsLeftNondegenerate}
    (hass : IsIdeleAssembled K L hnd) (g : AdelicOrthogonalGroup K L) :
    g ∈ adelicSpinorKernel hass ↔
      ∀ w : HeightOneSpectrum (𝓞 K), g w ∈ localSpinorKernel K w L (hnd w) := by
  constructor
  · intro hg w
    have h := adelicSpinorNorm_localComponent hass g w
    rw [MonoidHom.mem_ker.mp hg, map_one] at h
    exact MonoidHom.mem_ker.mpr h.symm
  · intro hg
    refine MonoidHom.mem_ker.mpr ?_
    have hone : finiteAdelicSpinorNorm hass g = 1 := by
      refine finiteIdeleComponents_injective K ?_
      funext w
      rw [finiteIdeleComponents_finiteAdelicSpinorNorm, map_one]
      exact MonoidHom.mem_ker.mp (hg w)
    rw [adelicSpinorNorm, MonoidHom.comp_apply, hone, map_one]

end LeanCategories.Lattices.Valued
