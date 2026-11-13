/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# TorBridge: the projective-resolution bridge for Tor

Card `E-HAT-3.A-6 / E-HAT-3.A-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/TorBridge.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/TorBridge.lean`.
-/


/-!
# The projective-resolution bridge for `Tor`

`Tor₁` is the first left derived functor of `tensorLeft B`. `ProjectiveResolution.isoLeftDerivedObj`
computes that derived functor from a chosen projective resolution: the value at `A` is the first
homology of the complex `P.complex ⊗ B`. This file records that bridge as an elaborated theorem, at
  the
generality of `ModuleCat ℤ`, takes the finite step that identifies that homology with the kernel of
  the
degree-1 differential for a two-term resolution, and packages the result as the kernel of the
right-tensored differential — the presentation-level `torKernel` of `cards/TorReductions.lean`.

Nothing here rebuilds homology: the derived functor, the projective resolution,
  `mapHomologicalComplex`
and the homology functor are the maintained ones.
-/

open CategoryTheory Limits MonoidalCategory

namespace LeanCategories.Homological.TorBridge

/-- `Tor₁(A, B)`, as the first left derived functor of `tensorLeft B` evaluated at `A`. -/
noncomputable abbrev torOne (A B : ModuleCat ℤ) : ModuleCat ℤ :=
  ((tensorLeft B).leftDerived 1).obj A

/-- The complex `P ⊗ B` attached to a projective resolution `P` of `A`: the tensor functor applied
degreewise to `P.complex`. -/
noncomputable abbrev resolutionTensor (B : ModuleCat ℤ) {A : ModuleCat ℤ}
    (P : ProjectiveResolution A) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((tensorLeft B).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

/-- **The bridge.** For every abelian group `A` and `B` and every projective resolution `P` of `A`,
`Tor₁(A, B)` is the first homology of the tensored resolution `P ⊗ B`. This is
`ProjectiveResolution.isoLeftDerivedObj` applied to the additive functor `tensorLeft B` at degree
  one:
no new machinery, and no hypothesis on the resolution beyond its being projective. -/
noncomputable def torOneIsoHomology {A B : ModuleCat ℤ} (P : ProjectiveResolution A) :
    torOne A B ≅
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
        (resolutionTensor B P) :=
  P.isoLeftDerivedObj (tensorLeft B) 1

/-- The degree-`1` differential of the tensored resolution, in the form the kernel step needs. -/
noncomputable abbrev tensorDiffOne (B : ModuleCat ℤ) {A : ModuleCat ℤ}
    (P : ProjectiveResolution A) :
    (resolutionTensor B P).X 1 ⟶ (resolutionTensor B P).X 0 :=
  (resolutionTensor B P).d 1 0

/-! ## The step this file takes, and what it still does not claim

For a two-term resolution — `P.complex` with `X 2 = 0`, so that the complex is `K → F → 0` — the
  first
homology of `P.complex ⊗ B` is the kernel of `d 1 0 ⊗ B`, because there is nothing in degree two to
quotient by. Proved below as `torOneIsoKernel`, with `IsZero ((P.complex).X 2)` the hypothesis, and
composed with the tensor symmetry into `torOneIsoTorKernel`, which identifies `Tor₁(A,B)` with the
presentation-level `torKernel` of `cards/TorReductions.lean` — `ker(K ⊗ B → F ⊗ B)` for `A = F/K` —
as the kernel of the right-tensored differential.

Hatcher's use of Lemma 3A.2 in `E-HAT-3.A-6` remains the *unrestricted* application: any resolution,
then passage to the colimit of the finitely generated stages. That citation is not formalized here,
  and
nothing in this file substitutes for it; what is formalized is the presentation-level identification
above plus the finite-stage descent of `cards/TorStages.lean`. -/

/-! ## The two-term step: the homology is the kernel of the incoming differential

`ShortComplex.LeftHomologyData.ofHasKernel S hf` (`hf : S.f = 0`) has its homology object
  *definitionally*
the kernel of `S.g`, so `homologyIso` is the identification; `HomologicalComplex.homologyIsoSc'`
presents the degree-`1` homology of a complex as the homology of the short complex
`K.X 2 → K.X 1 → K.X 0`; and `ModuleCat.kernelIsoKer` turns the categorical kernel into the
linear-map kernel, with `kernelIsoKer_hom_ker_subtype` recording what the map actually is.
-/

/-- **A short complex with vanishing incoming differential.** -/
noncomputable def homologyIsoKernelOfZero {S : ShortComplex (ModuleCat ℤ)} (hf : S.f = 0) :
    S.homology ≅ Limits.kernel S.g :=
  (ShortComplex.LeftHomologyData.ofHasKernel S hf).homologyIso

/-- **The two-term step at the level of the complex**, with the vanishing incoming differential as
the visible hypothesis. `homologyIsoSc'` moves to the short complex `K.X 2 → K.X 1 → K.X 0` (the
`prev`/`next` equalities for `ComplexShape.down ℕ` are supplied explicitly), and there the homology
  is
the kernel of the outgoing differential. -/
noncomputable def homologyOneIsoKernelOfD {K : ChainComplex (ModuleCat ℤ) ℕ}
    (h : K.d 2 1 = 0) : K.homology 1 ≅ Limits.kernel (K.d 1 0) :=
  (K.homologyIsoSc' 2 1 0
      (ComplexShape.prev_eq' (c := ComplexShape.down ℕ) (by simp))
      (ComplexShape.next_eq' (c := ComplexShape.down ℕ) (by simp))) ≪≫
    homologyIsoKernelOfZero (S := K.sc' 2 1 0) h

/-- The same, with the shape hypothesis `IsZero (K.X 2)`: any map out of a zero object is zero, so
  the
incoming differential vanishes. `K.shape` would *not* give this — `2 → 1` is an allowed differential
of `ComplexShape.down ℕ`. -/
noncomputable def homologyOneIsoKernel {K : ChainComplex (ModuleCat ℤ) ℕ} (h2 : IsZero (K.X 2)) :
    K.homology 1 ≅ Limits.kernel (K.d 1 0) :=
  homologyOneIsoKernelOfD (K := K) (IsZero.eq_of_src h2 _ _)

/-- The map-level check on the differential: the tensored complex's differential *is* the tensor
functor applied to the resolution's differential. -/
theorem resolutionTensor_d {A B : ModuleCat ℤ} (P : ProjectiveResolution A) (i j : ℕ) :
    (resolutionTensor B P).d i j = (tensorLeft B).map ((P.complex).d i j) :=
  rfl

/-- The vanishing of the incoming differential of the tensored complex, from the two-term shape of
  the
resolution: `eq_of_src` on the resolution, then `map_zero` of the additive tensor functor. -/
theorem tensor_d_two_one_eq_zero {A B : ModuleCat ℤ} (P : ProjectiveResolution A)
    (h2 : IsZero ((P.complex).X 2)) : (resolutionTensor B P).d 2 1 = 0 := by
  have hd : (P.complex).d 2 1 = 0 := IsZero.eq_of_src h2 _ _
  rw [resolutionTensor_d, hd, Functor.map_zero]

/-- **The two-term bridge.** For a projective resolution of `A` that is two-term
(`IsZero (P.complex.X 2)`), `Tor₁(A,B)` is the kernel of the tensored degree-`1` differential
`K ⊗ B → F ⊗ B` — the presentation-level `torKernel` of `cards/TorReductions.lean`, with the
differential identified at the level of maps by `resolutionTensor_d`. Projectivity and exactness of
  the
resolution are carried by `P : ProjectiveResolution A`; the two-term shape is the explicit `h2`. -/
noncomputable def torOneIsoKernel {A B : ModuleCat ℤ} (P : ProjectiveResolution A)
    (h2 : IsZero ((P.complex).X 2)) :
    torOne A B ≅ Limits.kernel ((resolutionTensor B P).d 1 0) :=
  torOneIsoHomology P ≪≫
    homologyOneIsoKernelOfD (K := resolutionTensor B P) (tensor_d_two_one_eq_zero P h2)

/-- The bridge composed with `ModuleCat.kernelIsoKer`, as an isomorphism of `Tor₁(A,B)` with the
module-theoretic kernel of the tensored differential. (`ModuleCat.kernelIsoKer` is the maintained
identification of the categorical kernel with `LinearMap.ker` of the underlying linear map; the
accompanying map identity `kernelIsoKer_hom_ker_subtype` is what makes the object name mean what it
says. Composing it *inside a named statement* here runs into a `ℤ`-module instance diamond on the
kernel subtype — `Submodule.module` against `AddCommGroup.toIntModule` — which is a Mathlib-side
instance wrinkle, not a gap in the bridge, so the composition is recorded as a term below with its
  type
left to the elaborator.) -/
noncomputable def torOneIsoKerLinear {A B : ModuleCat ℤ} (P : ProjectiveResolution A)
    (h2 : IsZero ((P.complex).X 2)) :=
  torOneIsoKernel P h2 ≪≫
    ModuleCat.kernelIsoKer (R := ℤ) (f := (resolutionTensor B P).d 1 0)

/-! ## The orientation glue, and the pinned kernel module

`tensorLeft B` is `B ⊗ -`, so the bridge's kernel lives in `B ⊗ K`; the presentation-level
`TorReductions.torKernel f` is the kernel of `f.rTensor B`, living in `K ⊗ B`. `TensorProduct.comm`
carries one to the other, and `LinearMap.lTensor_comm` is the naturality that makes this exact
  rather
than an assumption. The kernel module is also pinned at this boundary, so that `ModuleCat.of` and
`ModuleCat.kernelIsoKer` agree on which `ℤ`-module structure the kernel carries.
-/

/-- **The orientation glue.** The kernel of `f.rTensor N` in `M ⊗ N` is the inverse image under the
tensor symmetry of the kernel of `f.lTensor N` in `N ⊗ M`. Naturality is `LinearMap.lTensor_comm`;
nothing is assumed. -/
theorem ker_rTensor_eq_comap_ker_lTensor {M P : Type*} [AddCommGroup M] [AddCommGroup P]
    (f : M →ₗ[ℤ] P) (N : Type*) [AddCommGroup N] :
    (f.rTensor N).ker
      = Submodule.comap (TensorProduct.comm ℤ M N).toLinearMap (f.lTensor N).ker := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro hx
    show (LinearMap.lTensor N f) ((TensorProduct.comm ℤ M N) x) = 0
    rw [LinearMap.lTensor_comm, hx, map_zero]
  · intro hx
    have h2 : (TensorProduct.comm ℤ P N) ((LinearMap.rTensor N f) x) = 0 := by
      rw [← LinearMap.lTensor_comm (N := N) f x]
      exact hx
    exact (TensorProduct.comm ℤ P N).injective (by rw [h2, map_zero])

/-- The kernel of a morphism in `ModuleCat ℤ`, with its module structure pinned to the submodule
structure. This is the boundary at which `Submodule.module` and `AddCommGroup.toIntModule` would
otherwise clash, so both sides of the identification below are stated over this abbreviation. -/
noncomputable abbrev kerModule {M N : ModuleCat ℤ} (f : M ⟶ N) : ModuleCat ℤ :=
  letI := f.hom.ker.module
  ModuleCat.of ℤ ↥(f.hom.ker)

/-- `ModuleCat.kernelIsoKer` stated at that pinned boundary: the categorical kernel is the
linear-map kernel, as objects. -/
noncomputable def kernelIsoKerModule {M N : ModuleCat ℤ} (f : M ⟶ N) :
    Limits.kernel f ≅ kerModule f :=
  ModuleCat.kernelIsoKer (R := ℤ) f

/-- The differential-map identity on the `ModuleCat` side: the tensored complex's degree-`1`
differential is the resolution's differential with `B` tensored on the left. -/
theorem tensor_d_hom_eq_lTensor {A B : ModuleCat ℤ} (P : ProjectiveResolution A) :
    ((resolutionTensor B P).d 1 0).hom = (P.complex.d 1 0).hom.lTensor (↥B) :=
  rfl

/-! ## The composed isomorphism, at an explicitly ascribed boundary

Every module structure that the composition touches is named here: the tensor products get
`TensorProduct.instModule` built from the given structures, declared as inherited instances in the
section below, so that the map's typing and the kernel's ambient instance resolve to the *same*
structure; the kernels then get their submodule structure pinned by `submoduleModule`. This is the
ascription the earlier attempts lacked, and it does not weaken the statement or assume any map.
-/

section Boundary

variable {M P N : Type*} [AddCommGroup M] [AddCommGroup P] [AddCommGroup N]
  [Module ℤ M] [Module ℤ P] [Module ℤ N]

/-- The module structure on `M ⊗ N` built from the given structures on `M` and `N`. -/
noncomputable def tensorMod : Module ℤ (TensorProduct ℤ M N) :=
  TensorProduct.instModule

/-- The module structure on `P ⊗ N`. -/
noncomputable def tensorModPN : Module ℤ (TensorProduct ℤ P N) :=
  TensorProduct.instModule

/-- The module structure on `N ⊗ M`. -/
noncomputable def tensorModNM : Module ℤ (TensorProduct ℤ N M) :=
  TensorProduct.instModule

/-- The module structure on `N ⊗ P`. -/
noncomputable def tensorModNP : Module ℤ (TensorProduct ℤ N P) :=
  TensorProduct.instModule

attribute [local instance] tensorMod tensorModPN tensorModNM tensorModNP

/-- A submodule as a `ModuleCat`, with its `ℤ`-module structure pinned. -/
noncomputable abbrev submoduleModule (p : Submodule ℤ (TensorProduct ℤ M N)) : ModuleCat ℤ :=
  letI := p.module
  ModuleCat.of ℤ ↥p

/-- The orientation equality under the pinned instances: the same statement as
`ker_rTensor_eq_comap_ker_lTensor`, restated here so that its tensor module structures are the
  pinned
ones of this section. -/
theorem ker_rTensor_eq_comap_ker_lTensor' (f : M →ₗ[ℤ] P) :
    (f.rTensor N).ker
      = Submodule.comap (TensorProduct.comm ℤ M N).toLinearMap (f.lTensor N).ker := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro hx
    show (LinearMap.lTensor N f) ((TensorProduct.comm ℤ M N) x) = 0
    rw [LinearMap.lTensor_comm, hx, map_zero]
  · intro hx
    have h2 : (TensorProduct.comm ℤ P N) ((LinearMap.rTensor N f) x) = 0 := by
      rw [← LinearMap.lTensor_comm (N := N) f x]
      exact hx
    exact (TensorProduct.comm ℤ P N).injective (by rw [h2, map_zero])

/-- **The tensor symmetry on the two kernels, with its maps.** -/
noncomputable def kerCommEquiv (f : M →ₗ[ℤ] P) :
    (f.rTensor N).ker ≃ₗ[ℤ] (f.lTensor N).ker where
  toFun x := ⟨(TensorProduct.comm ℤ M N) x.1, by
    have h : (x : TensorProduct ℤ M N) ∈ Submodule.comap (TensorProduct.comm ℤ M N).toLinearMap
        (f.lTensor N).ker := by
      rw [← ker_rTensor_eq_comap_ker_lTensor']
      exact x.2
    exact Submodule.mem_comap.mp h⟩
  invFun y := ⟨(TensorProduct.comm ℤ M N).symm (y : TensorProduct ℤ N M), by
    have h : (TensorProduct.comm ℤ M N) ((TensorProduct.comm ℤ M N).symm (y : TensorProduct ℤ N M))
        ∈ (f.lTensor N).ker := by
      rw [LinearEquiv.apply_symm_apply]
      exact y.2
    have h' : ((TensorProduct.comm ℤ M N).symm (y : TensorProduct ℤ N M)) ∈
        Submodule.comap (TensorProduct.comm ℤ M N).toLinearMap (f.lTensor N).ker :=
      Submodule.mem_comap.mpr h
    rwa [← ker_rTensor_eq_comap_ker_lTensor'] at h'⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

end Boundary

/-! ## The packaged composition

`Tor₁(A,B)` is the kernel of the left-tensored differential `B ⊗ d`; the presentation-level
`torKernel` of `cards/TorReductions.lean` is the kernel of the right-tensored `d ⊗ B`. The tensor
symmetry `comm` carries one to the other, and `LinearMap.lTensor_comm` is exactly the statement that
the square it induces commutes. Stating the composition between *bundled* kernels keeps every module
structure bundled, so no submodule instance is synthesized anywhere in the statement.

The transport is oriented from the right-tensored kernel to the left-tensored one, which is the
direction `lTensor_comm` is stated in; the ambient tensor instances are ascribed in this section so
that both sides of each isomorphism mention the same one. -/

section PackagedBridge

variable {A B : ModuleCat ℤ} (P : ProjectiveResolution A) (h2 : IsZero ((P.complex).X 2))

/-- The ambient module structure on `X₁ ⊗ B`. -/
private abbrev mX1B : Module ℤ (TensorProduct ℤ ↥((P.complex).X 1) ↥B) := TensorProduct.instModule

/-- The ambient module structure on `X₀ ⊗ B`. -/
private abbrev mX0B : Module ℤ (TensorProduct ℤ ↥((P.complex).X 0) ↥B) := TensorProduct.instModule

attribute [local instance] mX1B mX0B

/-- The right-tensored differential of the resolution, bundled: this is the map whose kernel is the
presentation-level `torKernel`. -/
noncomputable abbrev diffRight : ModuleCat.of ℤ (TensorProduct ℤ ↥((P.complex).X 1) ↥B) ⟶
    ModuleCat.of ℤ (TensorProduct ℤ ↥((P.complex).X 0) ↥B) :=
  ModuleCat.ofHom (((P.complex).d 1 0).hom.rTensor ↥B)

/-- The tensor symmetry at the domain, going from the right-tensored side to `B ⊗ X₁`. -/
noncomputable def commDom :
    ModuleCat.of ℤ (TensorProduct ℤ ↥((P.complex).X 1) ↥B) ≅ (resolutionTensor B P).X 1 :=
  (TensorProduct.comm ℤ ↥((P.complex).X 1) ↥B).toModuleIso

/-- The tensor symmetry at the codomain. -/
noncomputable def commCod :
    ModuleCat.of ℤ (TensorProduct ℤ ↥((P.complex).X 0) ↥B) ≅ (resolutionTensor B P).X 0 :=
  (TensorProduct.comm ℤ ↥((P.complex).X 0) ↥B).toModuleIso

/-- The square commutes: this is `LinearMap.lTensor_comm` and nothing else. It says that the
left-tensored differential, precomposed with the tensor symmetry, is the symmetry applied to the
right-tensored differential. -/
theorem diff_square :
    diffRight (B := B) P ≫ (commCod P).hom = (commDom P).hom ≫ (resolutionTensor B P).d 1 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.comp_apply, ModuleCat.ofHom_apply, commCod, commDom,
    LinearEquiv.toModuleIso_hom, LinearEquiv.coe_toLinearMap, resolutionTensor_d]
  exact (LinearMap.lTensor_comm ((P.complex).d 1 0).hom x).symm

/-- **The packaged bridge.** For a two-term projective resolution, `Tor₁(A,B)` is isomorphic to the
kernel of the right-tensored differential `K ⊗ B → F ⊗ B`, the presentation-level `torKernel` of
`cards/TorReductions.lean`: `torOneIsoKernel` gives the kernel of the tensored (left-tensored)
differential, and `kernel.mapIso` transports it across the tensor symmetry using `diff_square`. -/
noncomputable def torOneIsoTorKernel :
    torOne A B ≅ Limits.kernel (diffRight (B := B) P) :=
  torOneIsoKernel P h2 ≪≫
    (kernel.mapIso (f := diffRight (B := B) P) ((resolutionTensor B P).d 1 0)
      (commDom P) (commCod P) (diff_square P)).symm

end PackagedBridge

end LeanCategories.Homological.TorBridge

