/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Sheaves.PresheafOfFunctions
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Sheaves versus presheaves: the exponential example

Weibel, *An Introduction to Homological Algebra* (1994), §1.6,
FC05-C01-U057.

Sheaves of abelian groups form an abelian category, but the inclusion into
presheaves is not an abelian subcategory: epimorphisms of sheaves need only be
locally surjective. The source example is the exponential map on
`X = ℂˣ`. It is locally surjective, hence an epimorphism of sheaves, while its
map on global sections is not surjective because `ℂˣ` admits no continuous
global logarithm.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace LeanCategories.Homological

/-- The presheaf of continuous `A`-valued functions, retaining the additive-group structure
on every section object. -/
noncomputable def continuousAddPresheaf (X : TopCat.{u}) (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of C((Opens.toTopCat X).obj (unop U), TopCat.of A)
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := fun g => g.comp ((Opens.toTopCat X).map f.unop).hom
      map_zero' := rfl
      map_add' := by intros; rfl }
  map_id U := by ext f; rfl
  map_comp f g := by ext h; rfl

/-- After forgetting additive structure, `continuousAddPresheaf` is the usual presheaf of
continuous functions. -/
noncomputable def continuousAddPresheafForgetIso (X : TopCat.{u}) (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    continuousAddPresheaf X A ⋙ CategoryTheory.forget AddCommGrpCat ≅
      TopCat.presheafToTop X (TopCat.of A) :=
  NatIso.ofComponents
    (fun U => (Equiv.mk
      (fun g => TopCat.ofHom g)
      (fun g => g.hom)
      (by intro g; rfl)
      (by intro g; apply TopCat.hom_ext; rfl)).toIso)
    (by
      intro U V f
      apply ConcreteCategory.hom_ext
      intro g
      rfl)

/-- The sheaf of continuous functions into a topological abelian group. -/
noncomputable def continuousAddSheaf (X : TopCat.{u}) (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨continuousAddPresheaf X A, by
    apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (CategoryTheory.forget AddCommGrpCat) (continuousAddPresheaf X A)).2
    exact TopCat.Presheaf.isSheaf_of_iso
      (continuousAddPresheafForgetIso X A).symm
      (TopCat.sheafToTop (X := X) (TopCat.of A)).property⟩

end LeanCategories.Homological

namespace LeanCategories.Homological

/-- Postcomposition by a continuous additive homomorphism induces a morphism of continuous
function sheaves. -/
noncomputable def continuousAddSheafMap (X : TopCat.{u})
    {A B : Type u} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    (φ : A →ₜ+ B) : continuousAddSheaf X A ⟶ continuousAddSheaf X B :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
      { toFun := fun g => φ.toContinuousMap.comp g
        map_zero' := by ext; simp
        map_add' := by intro f g; ext x; exact φ.map_add (f x) (g x) }
     naturality := by
      intro U V f
      ext g
      rfl }⟩

/-- The nonzero complex number `exp z`, packaged as a unit. -/
noncomputable def complexExpUnit (z : ℂ) : ℂˣ :=
  { val := Complex.exp z
    inv := Complex.exp (-z)
    val_inv := by rw [← Complex.exp_add]; simp
    inv_val := by rw [← Complex.exp_add]; simp }

/-- Complex exponential as a continuous additive homomorphism from `ℂ` to the additive
version of `ℂˣ`. -/
noncomputable def complexExpAddHom : ℂ →ₜ+ Additive ℂˣ where
  toFun z := Additive.ofMul (complexExpUnit z)
  map_zero' := by apply Additive.toMul.injective; apply Units.ext; simp [complexExpUnit]
  map_add' x y := by
    apply Additive.toMul.injective
    apply Units.ext
    exact Complex.exp_add x y
  continuous_toFun := by
    apply continuous_ofMul.comp
    rw [Units.continuous_iff]
    constructor
    · exact Complex.continuous_exp
    · change Continuous (Complex.exp ∘ fun z : ℂ => -z)
      exact Complex.continuous_exp.comp continuous_neg

/-- The exponential morphism between the sheaves of continuous `ℂ`-valued and
`Additive ℂˣ`-valued functions. -/
noncomputable def expSheafHom (X : TopCat.{0}) :
    continuousAddSheaf X ℂ ⟶ continuousAddSheaf X (Additive ℂˣ) :=
  continuousAddSheafMap X complexExpAddHom

end LeanCategories.Homological

namespace LeanCategories.Homological

/-- The multiplicative/additive type tag does not change the topology. -/
noncomputable def additiveHomeomorph (G : Type*) [TopologicalSpace G] :
    G ≃ₜ Additive G where
  toEquiv := Additive.ofMul
  continuous_toFun := continuous_ofMul
  continuous_invFun := continuous_toMul

/-- Complex exponential, regarded as a map `ℂ → Additive ℂˣ`, is a covering map. -/
theorem isCoveringMap_complexExpAdd :
    IsCoveringMap (complexExpAddHom : ℂ → Additive ℂˣ) := by
  have h₁ := Complex.isCoveringMap_exp.homeomorph_comp
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm
  have h₂ := h₁.homeomorph_comp (additiveHomeomorph ℂˣ)
  convert h₂ using 1
  funext z
  apply Additive.toMul.injective
  apply Units.ext
  let y : {w : ℂ // w ≠ 0} := ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have h := (unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply y
  have hv : (((unitsHomeomorphNeZero (G₀ := ℂ)).symm y : ℂˣ) : ℂ) = y.1 :=
    congrArg Subtype.val h
  change Complex.exp z = (((unitsHomeomorphNeZero (G₀ := ℂ)).symm y : ℂˣ) : ℂ)
  exact hv.symm

/-- Complex exponential is surjective onto nonzero complex numbers. -/
theorem complexExpAddHom_surjective :
    Function.Surjective (complexExpAddHom : ℂ → Additive ℂˣ) := by
  intro y
  let u : ℂˣ := Additive.toMul y
  refine ⟨Complex.log (u : ℂ), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change Complex.exp (Complex.log (u : ℂ)) = (u : ℂ)
  exact Complex.exp_log (Units.ne_zero u)

/-- The exponential morphism of continuous-function sheaves is locally surjective. -/
theorem expSheafHom_isLocallySurjective (X : TopCat.{0}) :
    TopCat.Presheaf.IsLocallySurjective (expSheafHom X).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  change C((Opens.toTopCat X).obj U, TopCat.of (Additive ℂˣ)) at t
  let xu : U := ⟨x, hx⟩
  obtain ⟨a, ha⟩ := complexExpAddHom_surjective (t xu)
  obtain ⟨e, hae, he⟩ := isCoveringMap_complexExpAdd.isLocalHomeomorph a
  have ht : t xu ∈ e.target := by
    rw [← ha, he]
    exact e.map_source hae
  let W : Set U := t ⁻¹' e.target
  have hW : IsOpen W := e.open_target.preimage t.continuous
  let V : Opens X :=
    ⟨U.inclusion' '' W, U.isOpenEmbedding.isOpenMap _ hW⟩
  have hVU : V ≤ U := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact z.2
  let iVU : C(V, U) := ((Opens.toTopCat X).map (homOfLE hVU)).hom
  have htarget (z : V) : t (iVU z) ∈ e.target := by
    rcases z.2 with ⟨w, hw, hwz⟩
    have hzi : iVU z = w := by
      apply Subtype.ext
      exact hwz.symm
    rw [hzi]
    exact hw
  let s : C(V, ℂ) :=
    ⟨fun z => e.symm (t (iVU z)),
      e.continuousOn_symm.comp_continuous
        (t.continuous.comp iVU.continuous) htarget⟩
  refine ⟨V, hVU, ?_, ?_⟩
  · refine ⟨s, ?_⟩
    change complexExpAddHom.toContinuousMap.comp s = t.comp iVU
    apply ContinuousMap.ext
    intro z
    change complexExpAddHom (e.symm (t (iVU z))) = t (iVU z)
    rw [he]
    exact e.right_inv (htarget z)
  · exact ⟨xu, ht, rfl⟩

/-- There is no continuous logarithm defined on all of `ℂˣ`. -/
theorem noContinuousGlobalLog :
    ¬ ∃ l : C(ℂˣ, ℂ),
      ∀ z : ℂˣ, complexExpAddHom (l z) = Additive.ofMul z := by
  rintro ⟨l, hl⟩
  let turn : ℝ → ℂ := fun t => (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  let g₁ : ℝ → ℂ := fun t => l (Additive.toMul (complexExpAddHom (turn t)))
  let g₂ : ℝ → ℂ := fun t => l 1 + turn t
  have hturn : Continuous turn := by
    dsimp [turn]
    fun_prop
  have hg₁ : Continuous g₁ := by
    dsimp [g₁]
    exact l.continuous.comp
      (continuous_toMul.comp (complexExpAddHom.continuous.comp hturn))
  have hg₂ : Continuous g₂ := by
    dsimp [g₂]
    exact continuous_const.add hturn
  have he : complexExpAddHom ∘ g₁ = complexExpAddHom ∘ g₂ := by
    funext t
    change complexExpAddHom (l (Additive.toMul (complexExpAddHom (turn t)))) =
      complexExpAddHom (l 1 + turn t)
    rw [hl, map_add, hl]
    simp
  have hzero : g₁ 0 = g₂ 0 := by
    dsimp [g₁, g₂, turn]
    simp
  have hEq : g₁ = g₂ :=
    isCoveringMap_complexExpAdd.eq_of_comp_eq hg₁ hg₂ he 0 hzero
  have hOne := congrFun hEq 1
  dsimp [g₁, g₂, turn] at hOne
  have hOne' :
      l (Additive.toMul (complexExpAddHom (2 * (Real.pi : ℂ) * Complex.I))) =
        l 1 + 2 * (Real.pi : ℂ) * Complex.I := by
    simpa only [one_mul] using hOne
  have hloop : Additive.toMul (complexExpAddHom (2 * (Real.pi : ℂ) * Complex.I)) = (1 : ℂˣ) := by
    apply Units.ext
    change Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1
    exact Complex.exp_two_pi_mul_I
  rw [hloop] at hOne'
  have : (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    have h : l 1 + 2 * (Real.pi : ℂ) * Complex.I = l 1 + 0 := by
      simpa only [add_zero] using hOne'.symm
    exact add_left_cancel h
  exact Complex.two_pi_I_ne_zero this

/-- On `ℂˣ`, the exponential morphism is an epimorphism in the category of sheaves. -/
instance expSheafHom_epi : Epi (expSheafHom (TopCat.of ℂˣ)) :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    (expSheafHom_isLocallySurjective (TopCat.of ℂˣ))

/-- The same exponential morphism is not an epimorphism after forgetting to presheaves:
surjectivity on the top open would produce a continuous global logarithm. -/
theorem expSheafHom_presheaf_not_epi :
    ¬ Epi (expSheafHom (TopCat.of ℂˣ)).hom := by
  intro hEpi
  let X : TopCat := TopCat.of ℂˣ
  let U : Opens X := ⊤
  have hEpiTop : Epi ((expSheafHom X).hom.app (op U)) :=
    ((CategoryTheory.NatTrans.epi_iff_epi_app (expSheafHom X).hom).mp hEpi) (op U)
  have hsurj : Function.Surjective ((expSheafHom X).hom.app (op U)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp hEpiTop
  let idSection : C((Opens.toTopCat X).obj U, TopCat.of (Additive ℂˣ)) :=
    ⟨fun z => Additive.ofMul z.1, continuous_ofMul.comp continuous_subtype_val⟩
  obtain ⟨s, hs⟩ := hsurj idSection
  change C((Opens.toTopCat X).obj U, TopCat.of ℂ) at s
  change complexExpAddHom.toContinuousMap.comp s = idSection at hs
  let l : C(ℂˣ, ℂ) := s.comp (Opens.inclusionTopIso X).inv.hom
  apply noContinuousGlobalLog
  refine ⟨l, ?_⟩
  intro z
  have hz := congrArg
    (fun q : C((Opens.toTopCat X).obj U, TopCat.of (Additive ℂˣ)) => q ⟨z, trivial⟩) hs
  exact hz

end LeanCategories.Homological
