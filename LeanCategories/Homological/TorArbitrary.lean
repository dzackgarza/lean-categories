/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# TorArbitrary: Tor one for an arbitrary abelian group, the dimension-shift platform

Card `E-HAT-3.A-6 / E-HAT-3.A-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/TorArbitrary.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/TorArbitrary.lean` with the `def` names carrying underscores renamed per the
  `defsWithUnderscore` lint (`addEquiv_intLinearEquiv` -> `addEquivIntLinearEquiv`); theorem names
    keep the certificate's spelling.
-/


/-!
# `E-HAT-3.A-6` / `E-HAT-3.A-2`: `Tor₁` for an arbitrary abelian group

Mathlib master still has no comparison between `Tor` and filtered colimits and no balancing of
`Tor`, so the two cards' passage from the finitely generated case to an arbitrary `A` is proved
here along the Weibel route (`An Introduction to Homological Algebra`, §2.6: filtered colimits are
exact in `R`-mod, Cor. 2.6.16–2.6.17, p. 58), realised elementwise through the finitely generated
stages of `cards/TorStages.lean`: every element of `Tor₁(A,B)` descends to the stage of a finitely
generated free presentation, and there the two card statements are already available.

The bridge is dimension shifting (Weibel, Exercise 2.4.3): for **any** epimorphism `f : P ⟶ A`
with `P` projective, `Tor₁(A,B)` is the kernel of `ker f ⊗ B → P ⊗ B`. The resolution that
computes it is the splice `P`, then the canonical projective resolutions of the kernel, its
kernel, and so on — built with `ChainComplex.mk'` from Mathlib's `Projective.d`/`syzygies`, whose
exactness and quasi-isomorphism proofs are copied from `ProjectiveResolution.of`
(`Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean`).
-/

open CategoryTheory Limits MonoidalCategory

namespace LeanCategories.Homological.TorArbitrary

/-- `Tor₁`, the first left derived functor of `tensorLeft B`, as in the sibling certificates. -/
noncomputable abbrev torOne (A B : ModuleCat ℤ) : ModuleCat ℤ :=
  ((tensorLeft B).leftDerived 1).obj A

section Splice

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P]

/-- **The splice resolution of `A` over the presentation `f`.** `P` in degree zero, then
`Projective.syzygies f` with the differential `Projective.d f`, then the canonical projective
resolutions of the kernels of the successive differentials. For `f = Projective.π A` this is
Mathlib's `ProjectiveResolution.of`; the general form is what an arbitrary presentation needs. -/
noncomputable def presComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.mk' P (Projective.syzygies f) (Projective.d f)
    (fun g => ⟨Projective.syzygies g, Projective.d g, by
      show (Projective.π (Limits.kernel g) ≫ Limits.kernel.ι g) ≫ g = 0
      rw [Category.assoc, Limits.kernel.condition, comp_zero]⟩)

theorem presComplex_d_1_0 : (presComplex f).d 1 0 = Projective.d f := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The splice resolution is exact in every positive degree, as for `ProjectiveResolution.of`. -/
theorem presComplex_exactAt_succ (n : ℕ) : (presComplex f).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', presComplex,
    ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  match n with
  | 0 => apply exact_d_f
  | n + 1 => apply exact_d_f

instance (n : ℕ) : Projective ((presComplex f).X n) := by
  obtain (_ | _ | _ | n) := n
  · show Projective P
    infer_instance
  all_goals apply Projective.projective_over

/-- **The augmentation of the splice resolution onto `A`.** -/
noncomputable def presPi : presComplex f ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj A :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨f, by
    show (Projective.π (Limits.kernel f) ≫ Limits.kernel.ι f) ≫ f = 0
    rw [Category.assoc, Limits.kernel.condition, comp_zero]⟩

/-- The augmentation's degree-zero component is the presentation map itself. -/
theorem presPi_cond : (Projective.π (Limits.kernel f) ≫ Limits.kernel.ι f) ≫ f = 0 := by
  rw [Category.assoc, Limits.kernel.condition, comp_zero]

theorem presPi_f_zero : (presPi f).f 0 = f :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := presComplex f) (X := A) f
    (by show HomologicalComplex.d (presComplex f) 1 0 ≫ f = 0
        exact presPi_cond f)

/-- **The splice resolution is a projective resolution of `A`**, for any epimorphism `f` from a
projective: exactness and the quasi-isomorphism as for `ProjectiveResolution.of`, with the
degree-zero comparison through the cokernel cofork, as in `cards/TorFreeResolution.lean`. -/
noncomputable def presResolution : ProjectiveResolution A where
  complex := presComplex f
  projective := fun n => inferInstance
  π := presPi f
  quasiIso := by
    constructor
    intro n
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff]
      have hexact : Function.Exact (Projective.d f).hom f.hom :=
        LinearMap.exact_iff.mpr (exact_d_f f).moduleCat_range_eq_ker.symm
      have hsurj : Function.Surjective f.hom :=
        (ModuleCat.epi_iff_surjective f).mp inferInstance
      have hc := ModuleCat.isColimitCokernelCofork
        (f := ModuleCat.ofHom (Projective.d f).hom) (g := f) hexact hsurj
      refine (ShortComplex.quasiIso_iff_of_zeros'
        (φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) 1 0
          0).map
          (presPi f)) rfl rfl rfl).2 ?_
      exact ⟨ShortComplex.exact_of_g_is_cokernel (S := _) hc, Limits.epi_of_isColimit_cofork hc⟩
    · rw [quasiIsoAt_iff_exactAt']
      · apply presComplex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj

end Splice

section TensorSplice

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P] (B : ModuleCat ℤ)

/-- The tensored splice complex: the tensor functor applied degreewise to `presComplex f`. -/
noncomputable abbrev tensorSplice : ChainComplex (ModuleCat ℤ) ℕ :=
  ((tensorLeft B).mapHomologicalComplex (ComplexShape.down ℕ)).obj (presComplex f)

/-- **The bridge at an arbitrary presentation.** `Tor₁(A,B)` is the first homology of the tensored
splice, exactly as `ProjectiveResolution.isoLeftDerivedObj` computes it for the canonical
resolution. -/
noncomputable def torOneIsoTensorSplice :
    torOne A B ≅ (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
      (tensorSplice f B) :=
  (presResolution f).isoLeftDerivedObj (tensorLeft B) 1

end TensorSplice

section DimensionShift

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P] (B : ModuleCat ℤ)

/-- **The dictionary**: the underlying linear map of a morphism tensored by `B` on the left is
`lTensor`. -/
theorem hom_lTensor {X Y : ModuleCat ℤ} (g : X ⟶ Y) :
    ((tensorLeft B).map g).hom = LinearMap.lTensor ↥B g.hom := rfl

/-- The tensored first differential of the splice is the tensor of the kernel cover followed by
the tensor of the kernel inclusion. -/
theorem tensorSplice_d_1_0 :
    (tensorSplice f B).d 1 0 =
      (tensorLeft B).map (Projective.π (Limits.kernel f)) ≫
        (tensorLeft B).map (Limits.kernel.ι f) := by
  show (tensorLeft B).map (Projective.d f) = _
  show (tensorLeft B).map (Projective.π (Limits.kernel f) ≫ Limits.kernel.ι f) = _
  rw [Functor.map_comp]

end DimensionShift

section ThirdIso

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P] (B : ModuleCat ℤ)

/-- The surjectivity input: tensoring the projective cover of the kernel stays surjective. -/
theorem kerCov_lTensor_surjective :
    Function.Surjective (LinearMap.lTensor ↥B (Projective.π (Limits.kernel f)).hom) :=
  LinearMap.lTensor_surjective ↥B
    ((ModuleCat.epi_iff_surjective (Projective.π (Limits.kernel f))).mp inferInstance)

/-- The kernel of the first differential of the splice is the kernel of the kernel cover, because
the kernel inclusion is injective. -/
theorem ker_dOne_eq_kerCov :
    LinearMap.ker ((HomologicalComplex.sc' (presComplex f) 2 1 0).g).hom =
      LinearMap.ker (Projective.π (Limits.kernel f)).hom := by
  have hinj : Function.Injective (Limits.kernel.ι f).hom :=
    (ModuleCat.mono_iff_injective (Limits.kernel.ι f)).mp inferInstance
  show LinearMap.ker ((Limits.kernel.ι f).hom.comp (Projective.π (Limits.kernel f)).hom) = _
  rw [LinearMap.ker_comp,
    show LinearMap.ker (Limits.kernel.ι f).hom = ⊥ from LinearMap.ker_eq_bot.mpr hinj,
    Submodule.comap_bot]

/-- The untensored second differential and the kernel cover form an exact pair. -/
theorem exact_dTwo_kerCov :
    Function.Exact ((HomologicalComplex.sc' (presComplex f) 2 1 0).f).hom
      (Projective.π (Limits.kernel f)).hom :=
  LinearMap.exact_iff.mpr (by
    have h1 := (HomologicalComplex.exactAt_iff' (presComplex f) 2 1 0 (by simp) (by simp)).mp
      (presComplex_exactAt_succ f 0)
    have h2 := h1.moduleCat_range_eq_ker
    exact (ker_dOne_eq_kerCov f).symm.trans h2.symm)

/-- **The tensored exactness, in dictionary form.** -/
theorem exact_tensored :
    Function.Exact (((tensorLeft B).map ((presComplex f).d 2 1)).hom)
      (((tensorLeft B).map (Projective.π (Limits.kernel f))).hom) := by
  have hsurj : Function.Surjective (Projective.π (Limits.kernel f)).hom :=
    (ModuleCat.epi_iff_surjective (Projective.π (Limits.kernel f))).mp inferInstance
  exact lTensor_exact ↥B (exact_dTwo_kerCov f) hsurj

/-- **The boundaries of the tensored splice are the kernel of the tensored kernel cover.** -/
theorem range_dTwoT_eq :
    LinearMap.range (((tensorSplice f B).sc' 2 1 0).f.hom) =
      LinearMap.ker (((tensorLeft B).map (Projective.π (Limits.kernel f))).hom) :=
  (LinearMap.exact_iff.mp (exact_tensored f B)).symm

end ThirdIso


/-! ## The third isomorphism and the dimension-shift bridge

The third isomorphism for a surjective `q` and any `g` reads `ker (g ∘ q) ⧸ ker q ≅ ker g`,
realised by the ψ-map `x ↦ q x`. At the tensored splice the rôle of `q` is played by the
tensored kernel cover — surjective by `kerCov_lTensor_surjective` — and the rôle of `g` by the
tensored kernel inclusion, so the homology of the tensored splice, whose boundaries are `ker q`
by `range_dTwoT_eq`, is the kernel of the tensored kernel inclusion: the dimension-shift
statement `Tor₁(A,B) ≅ ker(B ⊗ ker f → B ⊗ P)` of Weibel, Exercise 2.4.3, for **any**
epimorphism `f : P ⟶ A` from a projective and for every abelian group `A`, not only finitely
generated `A`.

The route is the submodule level, so that no linear map is built between the two subtype
carriers by hand — the carrier-level attempt could not elaborate (the instance diamond
`addCommGroup.toIntModule` against `Submodule.module` on the `presComplex` carriers, recorded
in the issue). The equality of this section, `mapCycles_eq_kerIncl`, is the surjectivity half
of the ψ-map at the submodule level: the image of the cycles under the tensored kernel cover
is the kernel of the tensored kernel inclusion, proved by rewriting the cycles as the comap of
the cover (`LinearMap.ker_comp` on `d 1 0 = q ≫ g'`, i.e. the cycle condition read through
the composite) and then `Submodule.map_comap_eq_self`, whose hypothesis is the surjectivity of
the cover — the lifts of the zeros of the inclusion through cycles.

What is **not** yet discharged is the packaging of the isomorphism: the kernel and the range
of the ψ-map as a linear map on the subtype carriers — `ker ψ = range moduleCatToCycles` and
`range ψ = ⊤`, from `range_dTwoT_eq` and the cycle check — and the composition of
`LinearMap.quotKerEquivRange` with those two equalities and the top equivalence. Every spelling
of the ψ-map tried so far (the six variants of the previous chat and the composite, the
restriction and the corestriction of this one) meets the same instance diamond on the cycles'
carrier, which is the blocker the issue records for the carrier level.
-/

section ThirdIsoSubmodule

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P] (B : ModuleCat ℤ)

/-- The cycles of the tensored splice in degree one: the kernel of its first differential. -/
noncomputable abbrev spliceCycles : Submodule ℤ ↥((tensorSplice f B).X 1) :=
  LinearMap.ker (((tensorSplice f B).sc' 2 1 0).g).hom

/-- The kernel of the tensored kernel inclusion: the target of the dimension shift. -/
noncomputable abbrev kerIncl : Submodule ℤ ↥((tensorLeft B).obj (Limits.kernel f)) :=
  LinearMap.ker ((tensorLeft B).map (Limits.kernel.ι f)).hom

/-- **The image of the cycles under the tensored kernel cover is the kernel of the tensored
kernel inclusion**: the surjectivity half of the ψ-map, at the submodule level. The left side
rewrites the cycles as the comap of the cover — `LinearMap.ker_comp` on `d 1 0 = q ≫ g'`, the
cycle condition — and the right side is `Submodule.map_comap_eq_self`, whose hypothesis is the
surjectivity of the cover. -/
theorem mapCycles_eq_kerIncl :
    Submodule.map ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom
      (spliceCycles f B) = kerIncl f B := by
  have hsurj : Function.Surjective
      ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom := by
    have h := kerCov_lTensor_surjective f B
    rw [← hom_lTensor (B := B) (Projective.π (Limits.kernel f))] at h
    exact h
  have hker : spliceCycles f B = Submodule.comap
      ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom (kerIncl f B) := by
    simp only [spliceCycles, kerIncl]
    rw [show ((tensorSplice f B).sc' 2 1 0).g = (tensorSplice f B).d 1 0 from rfl,
      tensorSplice_d_1_0 f B]
    exact LinearMap.ker_comp _ _
  rw [hker]
  refine Submodule.map_comap_eq_self fun y _ =>
    LinearMap.mem_range.mpr (hsurj y)

end ThirdIsoSubmodule



/-! ## The ψ-map of the third isomorphism, at the level of additive groups

An `AddMonoidHom` between the two subtype carriers mentions no `Module ℤ` instance, so the
instance diamond of the linear spellings (`addCommGroup.toIntModule` against
`Submodule.module`) does not arise. The homomorphism is the tensored kernel cover on the
cycles, corestricted to the kernel of the tensored kernel inclusion; it is surjective by the
containment `≥` of `mapCycles_eq_kerIncl`, and the additive-group kernel is the additive-group
view of the boundaries of the tensored splice (the preimage of zero is the preimage under the
cover of the zero of the inclusion, which is `range d 2 1` by `range_dTwoT_eq`), so that —
since `Submodule.Quotient` is `Quotient (leftRel p.toAddSubgroup)` — the additive-group
quotient of the cycles by the kernel of ψ is the submodule quotient of the cycles by the
boundaries, which is the target of `ShortComplex.moduleCatHomologyIso`. -/

section PsiGroup

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P] (B : ModuleCat ℤ)

/-- The membership half of the image equality: the image of a cycle under the tensored kernel
cover lies in the kernel of the tensored kernel inclusion. -/
theorem mem_kerIncl_of_mem_cycles (x : ↥(spliceCycles f B)) :
    ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom x.1 ∈ kerIncl f B := by
  have h : ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom x.1 ∈
      Submodule.map ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom
        (spliceCycles f B) :=
    Submodule.mem_map.mpr ⟨x.1, x.2, rfl⟩
  rw [mapCycles_eq_kerIncl f B] at h
  exact h

/-- **The ψ-map of the third isomorphism, as a homomorphism of additive groups**: the tensored
kernel cover on the cycles, corestricted to the kernel of the tensored kernel inclusion. Not a
linear map: an `AddMonoidHom` mentions no `Module ℤ` instance, so the instance diamond of the
nine linear spellings does not arise. -/
noncomputable def psiAdd : ↥(spliceCycles f B) →+ ↥(kerIncl f B) where
  toFun x := ⟨((tensorLeft B).map (Projective.π (Limits.kernel f))).hom x.1,
    mem_kerIncl_of_mem_cycles f B x⟩
  map_zero' := Subtype.ext (LinearMap.map_zero _)
  map_add' x y := Subtype.ext (LinearMap.map_add _ _ _)

/-- ψ is surjective: every element of the kernel of the tensored kernel inclusion is the image
of a cycle, the containment `≥` of `mapCycles_eq_kerIncl`. -/
theorem psiAdd_surjective : Function.Surjective (psiAdd f B) := by
  rintro ⟨y, hy⟩
  rw [← mapCycles_eq_kerIncl f B] at hy
  obtain ⟨x, hx, hq⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hq⟩

end PsiGroup

/-! ## The kernel of the ψ-map and the third isomorphism

The kernel of the ψ-map — the preimage of zero — is the additive-group view of the boundaries of
the tensored splice: the range of the second differential corestricted to the cycles, stated as
an `AddSubgroup` directly by `AddMonoidHom.range` of the underlying additive map, so that no
`Submodule.toAddSubgroup` transport and no `Module ℤ` instance on the carrier is needed. The
additive quotient of the cycles by the kernel of ψ is identified with the additive quotient by
the boundaries along that equation by `QuotientAddGroup.quotientAddEquivOfEq`, and the ψ-map is
surjective, so `QuotientAddGroup.quotientKerEquivOfSurjective` identifies the latter with the
kernel of the tensored kernel inclusion; the homology identifications come through
`LinearEquiv.toAddEquiv`, and the composite is promoted to a ℤ-linear equivalence by extending
the `AddEquiv` with a `map_smul'` proof, which `int_smul_eq_zsmul` and `map_zsmul` supply for
every `Module ℤ` instance, so the diamond of the two ℤ-module structures on the carrier does
not arise. -/

section PsiQuotient

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P] (B : ModuleCat ℤ)

/-- **The kernel of ψ is the boundaries of the tensored splice.** The kernel of the ψ-map, as a
subgroup of the cycles, is the range of the second differential corestricted to the cycles: a
cycle dies under ψ exactly when the tensored kernel cover kills its underlying vector, which is
membership in the kernel of the cover, the range of the second differential by
`range_dTwoT_eq`. -/
theorem psiAdd_ker :
    AddMonoidHom.ker (psiAdd f B) =
      AddMonoidHom.range ((tensorSplice f B).sc' 2 1 0).moduleCatToCycles.toAddMonoidHom := by
  ext x
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  constructor
  · intro h
    have hx : ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom x.1 = 0 :=
      congrArg Subtype.val h
    obtain ⟨y, hy⟩ := (exact_tensored f B x.1).mp hx
    exact ⟨y, Subtype.ext hy⟩
  · rintro ⟨y, hy⟩
    have hdy : ((tensorSplice f B).sc' 2 1 0).f.hom y = x.1 := congrArg Subtype.val hy
    have h0 : ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom x.1 = 0 := by
      have hq : ((tensorLeft B).map (Projective.π (Limits.kernel f))).hom
          (((tensorSplice f B).sc' 2 1 0).f.hom y) = 0 :=
        (exact_tensored f B _).mpr (Set.mem_range_self y)
      rw [← hdy]
      exact hq
    exact Subtype.ext h0

/-- **The third isomorphism, additive form**: the additive quotient of the cycles by the kernel
of ψ is the kernel of the tensored kernel inclusion. -/
noncomputable def psiAddQuotientEquiv :
    ↥(spliceCycles f B) ⧸ AddMonoidHom.ker (psiAdd f B) ≃+ ↥(kerIncl f B) :=
  QuotientAddGroup.quotientKerEquivOfSurjective (psiAdd f B) (psiAdd_surjective f B)

/-- **The third isomorphism on the boundaries quotient**: transporting
`psiAddQuotientEquiv` along `psiAdd_ker` with `quotientAddEquivOfEq`. -/
noncomputable def boundariesQuotientEquiv :
    ↥(spliceCycles f B) ⧸
      AddMonoidHom.range ((tensorSplice f B).sc' 2 1 0).moduleCatToCycles.toAddMonoidHom ≃+
      ↥(kerIncl f B) :=
  (QuotientAddGroup.quotientAddEquivOfEq (psiAdd_ker f B)).symm.trans
    (psiAddQuotientEquiv f B)


end PsiQuotient


/-! ## #138 — the two ℤ-linear equivalences and the dimension-shift bridge

An `AddEquiv` between two carriers with `Module ℤ` structures is a `LinearEquiv` for **any**
choice of the two structures: every `Module ℤ` structure agrees with `zsmul` (`int_smul_eq_zsmul`)
and an additive homomorphism preserves `zsmul` (`AddMonoidHom.map_zsmul`). The two `Module ℤ`
instances are the lemma's explicit instance arguments, so that no instance is synthesized on the
carrier at the application site. -/

section IntLinearEquiv

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- **#138.** An additive equivalence `e : M ≃+ N` is a ℤ-linear equivalence `M ≃ₗ[ℤ] N`, for
any two `Module ℤ` instances on the carriers. -/
noncomputable def addEquivIntLinearEquiv (e : M ≃+ N)
    [_i : Module ℤ M] [_j : Module ℤ N] : M ≃ₗ[ℤ] N := by
  refine e.toLinearEquiv fun c a ↦ ?_
  convert! e.toAddMonoidHom.map_zsmul c a using 1
  · exact congr(e $(int_smul_eq_zsmul _i c a))
  · exact int_smul_eq_zsmul _j c (e a)

end IntLinearEquiv


/-! ## #139 — the dimension-shift bridge, assembled

The homology of the tensored splice is the kernel of the tensored kernel inclusion, and `Tor₁`
is that homology: the composite of the committed `torOneIsoTensorSplice`, the Mathlib
`homologyIsoSc'`, `moduleCatHomologyIso` and the ℤ-linear homology equivalence above, packaged
as an isomorphism in `ModuleCat ℤ` by `LinearEquiv.toModuleIso`. -/

section Bridge

variable {A P : ModuleCat ℤ} (f : P ⟶ A) [Epi f] [Projective P] (B : ModuleCat ℤ)

/-- **#138, the homology equivalence.** The carrier of the homology of the tensored splice is
the kernel of the tensored kernel inclusion, as a ℤ-linear equivalence — the promotion of the
additive composite `boundariesQuotientEquiv` under the instance `H.isModule` on the left
carrier, the instance `Submodule.module` on the right. -/
noncomputable def homologyEquiv :
    ↥((tensorSplice f B).sc' 2 1 0).moduleCatLeftHomologyData.H ≃ₗ[ℤ] ↥(kerIncl f B) :=
  addEquivIntLinearEquiv (boundariesQuotientEquiv f B)
    (_i := ((tensorSplice f B).sc' 2 1 0).moduleCatLeftHomologyData.H.isModule)
    (_j := AddCommGroup.toIntModule (↥(kerIncl f B)))

/-- **#139.** `Tor₁(A, B) ≅ ker(ι ⊗ B)`: the composite of the committed
`torOneIsoTensorSplice`, Mathlib's `homologyIsoSc'`, `moduleCatHomologyIso`, and the ℤ-linear
homology equivalence above, as an isomorphism in `ModuleCat ℤ`. -/
noncomputable def torOneIsoKerIncl :
    torOne A B ≅ ModuleCat.of ℤ ↥(kerIncl f B) :=
  (torOneIsoTensorSplice f B) ≪≫
    ((tensorSplice f B).homologyIsoSc' 2 1 0
      (ComplexShape.prev_eq' (c := ComplexShape.down ℕ) (by simp))
      (ComplexShape.next_eq' (c := ComplexShape.down ℕ) (by simp))) ≪≫
    (((tensorSplice f B).sc' 2 1 0).moduleCatHomologyIso) ≪≫
    (homologyEquiv f B).toModuleIso

end Bridge


end LeanCategories.Homological.TorArbitrary

