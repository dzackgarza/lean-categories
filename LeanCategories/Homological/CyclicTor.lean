/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
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
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# CyclicTor: the cyclic stage and the index transport

Card `E-HAT-3.A-6 / E-HAT-3.A-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/CyclicTor.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/CyclicTor.lean` with the `def` names carrying underscores renamed per the
  `defsWithUnderscore` lint (`coker_subtype_iso` -> `cokerSubtypeIso`, `torOne_iso_kernel` ->
    `torOneIsoKernel`, `torOne_cyclicIso_torsionBy` -> `torOneCyclicIsoTorsionBy`); theorem names
      keep the certificate's spelling.
-/


/-!
# `E-HAT-3.A-6` / `E-HAT-3.A-2`: the cyclic stage, the index transport

The cyclic stage of the torsion statement is `Tor₁(ℤ/n, B) ≅ B[n]`. The two ends of it are already
certified elsewhere: `cards/TorFreeResolution.lean` identifies `Tor₁(A,B)` with the kernel of the
tensored first differential of a two-term free resolution and provides the cyclic one
(`cyclicResolution n`, with `syzygyEquiv` identifying its syzygy with `ℤ` on the generator `n`), and
`cards/TorReductions.lean` identifies the kernel of `(n · id) ⊗ id_B` inside `ℤ ⊗ B` with `B[n]`
(`map_torKernel_mulByInt`). This file writes the index transport that joins them.

**What is certified here.** The index transport the cyclic stage needs, in two steps.

`d_apply`: the cyclic resolution's first differential is `constOne ∘ (n · id) ∘ syzygyEquiv`,
  because a
syzygy vector is `fun _ => n * c` with `c = syzygyEquiv x`. In words: the resolution's first
differential is the subtype of the syzygy, and under `syzygyEquiv` that subtype is `n · id` followed
  by
the constant-vector identification `constOne : ℤ → (Fin 1 → ℤ)`.

`ker_d_rTensor_eq`: **the kernel of the tensored first differential is the preimage, under
`syzygyEquiv ⊗ id_B`, of the kernel of `(n · id) ⊗ id_B`.** That is the transport: the left side is
what `Tor₁` is computed from (`cards/TorFreeResolution.lean`), and the right side is the
presentation-level `torKernel` whose image under `TensorProduct.lid` is `B[n]`
(`cards/TorReductions.lean`, `map_torKernel_mulByInt`). Supporting facts, all proved here:
`projZero_comp_constOne` (the zeroth coordinate retracts `constOne`), `constOne_tmul_eq_zero`, and
`ker_constOne_rTensor_eq_bot` (`constOne ⊗ id_B` is injective, because `projZero` retracts it); the
generic form is `ker_subtype_rTensor_eq`.

Two notes on why this is stated the way it is, since both cost a failed attempt. First, the carrier:
`↑((twoTermComplex 1 (cyclicPresentation n)).X 1)` and `↥(LinearMap.ker (cyclicPresentation n))` are
not interchangeable in the `⊗ₜ` notation even though `twoTermComplex_X_one` gives their equality by
`rfl`, so the transport is proved in the generic form for `(LinearMap.ker f).subtype` — whose
  carrier
is `↥(LinearMap.ker f)` by construction — and `ker_d_rTensor_eq` specializes it by the `rfl` step
`hsub`. Second, the instances: stating the factorisation as a composite of `ModuleCat.ofHom`s and
taking `.hom` puts `ModuleCat.isModule` on both sides, where a composite written with
`LinearMap.comp` alone is headed by `Int.instRing.toSemiring` and does not unify.

**What is certified about the last hop.** `map_ker_d_rTensor_eq` closes it as far as the two
mathematics steps go: mapping the kernel by `σ ⊗ id_B` recovers `ker ((n · id) ⊗ id_B)`, because
`σ ⊗ id_B` is invertible and the kernel therefore lies in its range
(`Submodule.map_comap_eq_self`). Composing that with `TorReductions.map_torKernel_mulByInt` — the
statement that this kernel, carried by `TensorProduct.lid`, is `Submodule.torsionBy ℤ ↥B n` — is the
final `Tor₁(ℤ/n, B) ≅ B[n]` sentence, and `map_comp_map` proves the composition step it needs.

**What used not to be written** is that one composition, and the obstruction was ascription, not
mathematics: writing `Submodule.map (((TensorProduct.lid ℤ ↥B).toLinearMap).comp (σ ⊗ id_B)) (ker
  ∂⊗B) = torsionBy`
and rewriting with `map_comp_map` fails to unify the two `Submodule` types, whose implicit instance
arguments are the `TensorProduct.instModule` path here and the `Int.instCommSemiring` path there.

**The composition is now written, and the repair was at the instance.** The original
`map_torKernel_mulByInt` is stated over `{B : Type*} [AddCommGroup B]`, so its tensor products
carry `AddCommGroup.toIntModule`, the instance found from `[AddCommGroup B]` alone, while this
file's `Transport` section carries `B : ModuleCat ℤ` and therefore the carrier instance
`ModuleCat.isModule`, whose priority (1100) beats `AddCommGroup.toIntModule` — two `Submodule`
types that are the same structure on paper and different terms in the elaborator, so the
composition cannot cite the lemma directly. Restating it with an explicit `[Module ℤ B]` binder
next to `[AddCommGroup B]` fails in the elaborator: with two `Module ℤ B` instances in scope, the
`SMulCommClass ℤ ℤ B` that `DistribSMul.toLinearMap` demands cannot be synthesized. The working
repair is the pinned-instance pattern of `cards/TorBridge.lean` realised the other way round: the
lemma is restated in the carrier-instance section itself (`lid_rTensor_mulByInt_carrier`,
`map_torKernel_mulByInt_carrier`), where `ModuleCat.isModule` is the only candidate, with the
multiplication by `n` written as `lid (n ⊗ₜ b)` so that the `SMul`-instance diamond never enters
a statement. On top of the composition
`map_ker_d_rTensor_lid_eq_torsionBy`, the file proves `Tor₁(ℤ/n, B) ≅ B[n]` as a named isomorphism:
`torOneCyclicIsoTorsionBy`, the packaged bridge at the cyclic resolution composed with
`ModuleCat.kernelIsoKer` and with `kerEquivTorsionBy` — the restriction of the injective transport
map `cycTransport` to the kernel, which the composition theorem identifies with `B[n]`.
-/


open CategoryTheory Limits MonoidalCategory
open scoped ZeroObject

namespace CyclicTransport

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
noncomputable abbrev diffRight :
    @ModuleCat.of ℤ _ (TensorProduct ℤ ↥((P.complex).X 1) ↥B) _ TensorProduct.instModule ⟶
      @ModuleCat.of ℤ _ (TensorProduct ℤ ↥((P.complex).X 0) ↥B) _ TensorProduct.instModule :=
  @ModuleCat.ofHom ℤ Int.instRing (TensorProduct ℤ ↥((P.complex).X 1) ↥B)
      (TensorProduct ℤ ↥((P.complex).X 0) ↥B) _ TensorProduct.instModule
      _ TensorProduct.instModule (((P.complex).d 1 0).hom.rTensor ↥B)

/-- The tensor symmetry at the domain, going from the right-tensored side to `B ⊗ X₁`. -/
noncomputable def commDom :
    @ModuleCat.of ℤ _ (TensorProduct ℤ ↥((P.complex).X 1) ↥B) _ TensorProduct.instModule ≅
      (resolutionTensor B P).X 1 :=
  (TensorProduct.comm ℤ ↥((P.complex).X 1) ↥B).toModuleIso

/-- The tensor symmetry at the codomain. -/
noncomputable def commCod :
    @ModuleCat.of ℤ _ (TensorProduct ℤ ↥((P.complex).X 0) ↥B) _ TensorProduct.instModule ≅
      (resolutionTensor B P).X 0 :=
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


namespace Cyclic

variable {A : Type} [AddCommGroup A] [Module ℤ A]

/-- The syzygy of a map out of `ℤⁿ` is finitely generated: it is a submodule of a Noetherian
module. -/
theorem syzygy_finite (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A) :
    Module.Finite ℤ ↥(LinearMap.ker f) :=
  inferInstance

/-- The syzygy is torsion-free, being a submodule of a free `ℤ`-module. -/
theorem syzygy_torsionFree (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A) :
    Module.IsTorsionFree ℤ ↥(LinearMap.ker f) :=
  inferInstance

/-- **The syzygy of a finite free presentation is free.** This is the hypothesis that makes the
two-term complex `0 → K → ℤⁿ → A → 0` a *projective* resolution, and it is exactly what §5b's
instantiation was missing. Over a PID, finitely generated plus torsion-free is free. -/
theorem syzygy_free (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A) :
    Module.Free ℤ ↥(LinearMap.ker f) :=
  Module.free_of_finite_type_torsion_free'

/-- The syzygy, as an object of `ModuleCat ℤ`, is projective — so it may sit in degree `1` of a
projective resolution. -/
theorem syzygy_projective (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A) :
    CategoryTheory.Projective (ModuleCat.of ℤ ↥(LinearMap.ker f)) :=
  inferInstance

/-- The middle term of the presentation, `ℤⁿ`, is projective. -/
theorem free_projective (n : ℕ) :
    CategoryTheory.Projective (ModuleCat.of ℤ (Fin n → ℤ)) :=
  inferInstance

/-- Both terms of the two-term presentation are projective, which is the condition
`ProjectiveResolution` imposes degreewise; stated together because that is how the resolution
consumes it. -/
theorem presentation_projective (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A) :
    CategoryTheory.Projective (ModuleCat.of ℤ ↥(LinearMap.ker f)) ∧
      CategoryTheory.Projective (ModuleCat.of ℤ (Fin n → ℤ)) :=
  ⟨syzygy_projective n f, free_projective n⟩

/-! ## The two-term projective complex of a finite free presentation

`0 → K → ℤⁿ → A → 0` as a chain complex concentrated in degrees `0` and `1`. It is built with
`ChainComplex.mk'`, whose inductive continuation is the zero complex, so degree `2` and above are
literally the zero object — which is the shape `torOneIsoTorKernel` needs (`IsZero (X 2)`). -/

section TwoTerm

variable (r : ℕ) (f : (Fin r → ℤ) →ₗ[ℤ] A)

/-- The two-term complex `K → ℤⁿ → 0 → 0 → ⋯` attached to a finite free presentation. -/
noncomputable def twoTermComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.mk' (ModuleCat.of ℤ (Fin r → ℤ)) (ModuleCat.of ℤ ↥(LinearMap.ker f))
    (ModuleCat.ofHom (LinearMap.ker f).subtype)
    (fun _ => ⟨0, 0, by simp⟩)

/-- Degree `0` of the complex is `ℤⁿ`. -/
theorem twoTermComplex_X_zero : (twoTermComplex r f).X 0 = ModuleCat.of ℤ (Fin r → ℤ) :=
  ChainComplex.mk'_X_0 ..

/-- Degree `1` of the complex is the syzygy. -/
theorem twoTermComplex_X_one : (twoTermComplex r f).X 1 = ModuleCat.of ℤ ↥(LinearMap.ker f) :=
  ChainComplex.mk'_X_1 ..

/-- The only nonzero differential is the inclusion of the syzygy. -/
theorem twoTermComplex_d_one_zero :
    (twoTermComplex r f).d 1 0 = ModuleCat.ofHom (LinearMap.ker f).subtype :=
  ChainComplex.mk'_d_1_0 ..

/-- **Degree two vanishes**: the complex is two-term, which is the hypothesis `torOneIsoTorKernel`
carries. -/
theorem twoTermComplex_isZero_X_two : IsZero ((twoTermComplex r f).X 2) :=
  IsZero.of_iso (isZero_zero (ModuleCat ℤ))
    (ChainComplex.mk'XIso (ModuleCat.of ℤ (Fin r → ℤ)) (ModuleCat.of ℤ ↥(LinearMap.ker f))
      (ModuleCat.ofHom (LinearMap.ker f).subtype) (fun _ => ⟨0, 0, by simp⟩) 0)

/-- Every degree from `2` up is the zero object: the complex really is two-term. -/
theorem twoTermComplex_isZero_X (n : ℕ) (hn : 2 ≤ n) : IsZero ((twoTermComplex r f).X n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact IsZero.of_iso (isZero_zero (ModuleCat ℤ))
    (ChainComplex.mk'XIso (ModuleCat.of ℤ (Fin r → ℤ)) (ModuleCat.of ℤ ↥(LinearMap.ker f))
      (ModuleCat.ofHom (LinearMap.ker f).subtype) (fun _ => ⟨0, 0, by simp⟩) k)

/-- The differential of the two-term complex is a monomorphism: it is the inclusion of the syzygy
into `ℤⁿ`. This is what makes `H₁` vanish. -/
theorem twoTermComplex_mono_d_one_zero :
    Mono ((twoTermComplex r f).d 1 0) := by
  rw [twoTermComplex_d_one_zero]
  exact ModuleCat.mono_as_hom'_subtype (R := ℤ) (X := ModuleCat.of ℤ (Fin r → ℤ))
    (LinearMap.ker f)

/-- Every degree of the two-term complex is projective, so it can be a `ProjectiveResolution`. -/
theorem twoTermComplex_projective (n : ℕ) : Projective ((twoTermComplex r f).X n) := by
  match n with
  | 0 => exact free_projective r
  | 1 => exact syzygy_projective r f
  | k + 2 =>
    exact Projective.of_iso (Iso.symm (ChainComplex.mk'XIso (ModuleCat.of ℤ (Fin r → ℤ))
      (ModuleCat.of ℤ ↥(LinearMap.ker f)) (ModuleCat.ofHom (LinearMap.ker f).subtype)
      (fun _ => ⟨0, 0, by simp⟩) k)) (inferInstance : Projective (0 : ModuleCat ℤ))

/-- The augmentation of the two-term complex onto `A`, i.e. the map `F → A` in degree zero and zero
above it. It exists precisely because `f` kills the syzygy, which is the side condition
`ChainComplex.toSingle₀Equiv` asks for. -/
noncomputable def twoTermPi :
    twoTermComplex r f ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ A) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom f, by
    rw [twoTermComplex_d_one_zero]
    apply ModuleCat.hom_ext
    ext x
    exact x.2⟩

/-! ## The homology of the two-term complex

`H₁` vanishes because the differential is the inclusion of the syzygy, and every degree from `2` up
is the zero object. These are the vanishing half of the quasi-isomorphism computation; `H₀` is
`F/K ≅ A`, which needs `f` surjective and is treated separately. -/

/-- A short complex with vanishing incoming differential has homology its kernel. Copied from the
sibling certificate rather than imported: a file under `proofs/cards/` has no olean of its siblings
on the search path. -/
noncomputable def homologyIsoKernelOfZero {S : ShortComplex (ModuleCat ℤ)} (hf : S.f = 0) :
    S.homology ≅ Limits.kernel S.g :=
  (ShortComplex.LeftHomologyData.ofHasKernel S hf).homologyIso

/-- The degree-`1` homology of a chain complex, with the incoming differential vanishing, is the
kernel of the outgoing one. -/
noncomputable def homologyOneIsoKernelOfD {K : ChainComplex (ModuleCat ℤ) ℕ}
    (h : K.d 2 1 = 0) : K.homology 1 ≅ Limits.kernel (K.d 1 0) :=
  (K.homologyIsoSc' 2 1 0
      (ComplexShape.prev_eq' (c := ComplexShape.down ℕ) (by simp))
      (ComplexShape.next_eq' (c := ComplexShape.down ℕ) (by simp))) ≪≫
    homologyIsoKernelOfZero (S := K.sc' 2 1 0) h

/-- The same from the shape hypothesis `IsZero (K.X 2)`. -/
noncomputable def homologyOneIsoKernel {K : ChainComplex (ModuleCat ℤ) ℕ} (h2 : IsZero (K.X 2)) :
    K.homology 1 ≅ Limits.kernel (K.d 1 0) :=
  homologyOneIsoKernelOfD (K := K) (IsZero.eq_of_src h2 _ _)

/-- A kernel module with its structure pinned to the submodule structure, so that
`ModuleCat.kernelIsoKer` and the surrounding statements mention one instance. -/
noncomputable abbrev kerModule {M N : ModuleCat ℤ} (g : M ⟶ N) : ModuleCat ℤ :=
  letI := g.hom.ker.module
  ModuleCat.of ℤ ↥(g.hom.ker)

/-- `ModuleCat.kernelIsoKer` stated at that pinned boundary. -/
noncomputable def kernelIsoKerModule {M N : ModuleCat ℤ} (g : M ⟶ N) :
    Limits.kernel g ≅ kerModule g :=
  ModuleCat.kernelIsoKer (R := ℤ) g

/-- **A kernel of a map out of a zero object is zero.** This is the step that makes the homology
vanish in every degree where the complex itself is zero: `ModuleCat.kernelIsoKer` presents the
categorical kernel as the linear-map kernel, and a map out of a trivial module has all of its domain
in its kernel. -/
theorem isZero_kernel_of_isZero_source {X Y : ModuleCat ℤ} (g : X ⟶ Y) (hX : IsZero X) :
    IsZero (Limits.kernel g) := by
  haveI : Subsingleton ↥X := ModuleCat.subsingleton_of_isZero hX
  haveI : Subsingleton ↥(g.hom.ker) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim (a : ↥X) (b : ↥X))⟩
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton (kerModule g)) (kernelIsoKerModule g)

/-- The degree-`k+2` homology of a chain complex, when the incoming differential vanishes, is the
kernel of the outgoing one. -/
noncomputable def homologyIsoKernelAt (K : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : K.d (k + 3) (k + 2) = 0) :
    K.homology (k + 2) ≅ Limits.kernel (K.d (k + 2) (k + 1)) :=
  (K.homologyIsoSc' (k + 3) (k + 2) (k + 1)
      (ComplexShape.prev_eq' (c := ComplexShape.down ℕ) (by simp))
      (ComplexShape.next_eq' (c := ComplexShape.down ℕ) (by simp))) ≪≫
    homologyIsoKernelOfZero (S := K.sc' (k + 3) (k + 2) (k + 1)) h

/-- **The two-term complex has no homology above degree zero**, besides the vanishing of `H₁`
proved separately: for `n ≥ 2` the degree-`n` term is the zero object, so the degree-`n` homology is
the kernel of a map out of it. -/
theorem twoTermComplex_homology_isZero (k : ℕ) :
    IsZero ((twoTermComplex r f).homology (k + 2)) := by
  have hzero3 : IsZero ((twoTermComplex r f).X (k + 3)) :=
    twoTermComplex_isZero_X r f (k + 3) (by omega)
  have hd : (twoTermComplex r f).d (k + 3) (k + 2) = 0 := IsZero.eq_of_src hzero3 _ _
  refine IsZero.of_iso (isZero_kernel_of_isZero_source
    ((twoTermComplex r f).d (k + 2) (k + 1)) (twoTermComplex_isZero_X r f (k + 2) (by omega)))
    (homologyIsoKernelAt (twoTermComplex r f) k hd)

/-- **The cokernel of the inclusion of the syzygy is `A`**, for a surjective presentation: this is
the first isomorphism theorem, `ℤⁿ ⧸ ker f ≅ A`, transported to the categorical cokernel by
`ModuleCat.cokernelIsoRangeQuotient`. It is the `H₀` half of the quasi-isomorphism. -/
noncomputable def cokerSubtypeIso (hf : Function.Surjective f) :
    Limits.cokernel (ModuleCat.ofHom (LinearMap.ker f).subtype :
        ModuleCat.of ℤ ↥(LinearMap.ker f) ⟶ ModuleCat.of ℤ (Fin r → ℤ)) ≅
      ModuleCat.of ℤ A := by
  refine (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (LinearMap.ker f).subtype)).trans ?_
  rw [ModuleCat.hom_ofHom, Submodule.range_subtype]
  exact LinearEquiv.toModuleIso (f.quotKerEquivOfSurjective hf)

/-- **`H₁` of the two-term complex vanishes**: the differential is the inclusion of the syzygy,
which is a monomorphism, so its kernel is the zero object. -/
theorem twoTermComplex_homology_one_isZero :
    IsZero ((twoTermComplex r f).homology 1) := by
  haveI : Mono ((twoTermComplex r f).d 1 0) := twoTermComplex_mono_d_one_zero r f
  exact IsZero.of_iso (isZero_kernel_of_mono ((twoTermComplex r f).d 1 0))
    (homologyOneIsoKernel (twoTermComplex_isZero_X_two r f))

/-! ## The quasi-isomorphism, above degree zero

Both complexes have vanishing homology in every positive degree — the two-term complex by
`twoTermComplex_homology_one_isZero` and `twoTermComplex_homology_isZero`, and `single₀ A` because
  it
is concentrated in degree `0` — so the comparison map is an isomorphism on homology there by
`IsZero.isIso`. Degree `0`, where the map is `F/K ≅ A`, is treated separately since it needs
surjectivity of the presentation. -/

/-- The homology of the two-term complex vanishes in every positive degree. -/
theorem twoTermComplex_homology_pos_isZero (i : ℕ) (hi : i ≠ 0) :
    IsZero ((twoTermComplex r f).homology i) := by
  match i with
  | 0 => exact absurd rfl hi
  | 1 => exact twoTermComplex_homology_one_isZero r f
  | k + 2 => exact twoTermComplex_homology_isZero r f k

/-- The homology of `single₀ A` vanishes in every positive degree. -/
theorem single₀_homology_pos_isZero (i : ℕ) (hi : i ≠ 0) :
    IsZero (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ A)).homology i) := by
  have h := HomologicalComplex.isZero_single_obj_homology (C := ModuleCat ℤ)
    (c := ComplexShape.down ℕ) (j := 0) (ModuleCat.of ℤ A) i hi
  simpa using h

/-- **The comparison map is a quasi-isomorphism in degree zero.** This is the degree where the
complex really carries homology, so the statement is that `F/K → A` is an isomorphism. It is proved
as `ShortComplex.quasiIso_iff_of_zeros'` asks: the short complex `K → F → A` is exact because `A` is
a cokernel of the inclusion — `ModuleCat.isColimitCokernelCofork` builds that colimit from
`Function.Exact` and surjectivity of `f` — and `f` is an epimorphism for the same reason. -/
theorem quasiIsoAt_twoTermPi_zero (hf : Function.Surjective f) :
    QuasiIsoAt (twoTermPi r f) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  have hexact : Function.Exact (Submodule.subtype (LinearMap.ker f)) f :=
    LinearMap.exact_iff.mpr (Submodule.range_subtype (LinearMap.ker f)).symm
  have hc := ModuleCat.isColimitCokernelCofork
    (f := (ModuleCat.ofHom (LinearMap.ker f).subtype :
      ModuleCat.of ℤ ↥(LinearMap.ker f) ⟶ ModuleCat.of ℤ (Fin r → ℤ)))
    (g := (ModuleCat.ofHom f : ModuleCat.of ℤ (Fin r → ℤ) ⟶ ModuleCat.of ℤ A)) hexact hf
  refine (ShortComplex.quasiIso_iff_of_zeros'
    (φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) 1 0 0).map
      (twoTermPi r f)) rfl rfl rfl).2 ?_
  exact ⟨ShortComplex.exact_of_g_is_cokernel (S := _) hc, Limits.epi_of_isColimit_cofork hc⟩

/-- **The comparison map is a quasi-isomorphism above degree zero**: both sides have zero homology
there. -/
theorem quasiIsoAt_twoTermPi_of_pos (i : ℕ) (hi : i ≠ 0) :
    QuasiIsoAt (twoTermPi r f) i := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsZero.isIso (twoTermComplex_homology_pos_isZero r f i hi)
    (single₀_homology_pos_isZero (A := A) i hi) _

/-- **The comparison map is a quasi-isomorphism**, all degrees: degree zero by `hf`, and every
positive degree because both sides vanish there. -/
theorem quasiIso_twoTermPi (hf : Function.Surjective f) : QuasiIso (twoTermPi r f) where
  quasiIsoAt := fun i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact quasiIsoAt_twoTermPi_zero r f hf
    · exact quasiIsoAt_twoTermPi_of_pos r f i h.ne'

/-- **The two-term complex is a projective resolution of `A`**, for a surjective finite free
presentation: the complex is two-term and degreewise projective, and its augmentation is a
quasi-isomorphism. This is the genuine free resolution that §5b's card application needs. -/
noncomputable def twoTermProjectiveResolution (hf : Function.Surjective f) :
    ProjectiveResolution (ModuleCat.of ℤ A) where
  complex := twoTermComplex r f
  projective := twoTermComplex_projective r f
  π := twoTermPi r f
  quasiIso := quasiIso_twoTermPi r f hf

end TwoTerm

/-! ## The instantiation: `Tor₁` of a finite free presentation

The `Tor` layer of `cards/TorBridge.lean`, restated here so that the instantiation is in one
self-contained file (a certificate under `proofs/cards/` has no olean of its sibling on the search
path). -/

section TorBridgeLocal

/-- `Tor₁(A,B)`, the first left derived functor of `tensorLeft B` at `A`. -/
noncomputable abbrev torOne (A B : ModuleCat ℤ) : ModuleCat ℤ :=
  ((tensorLeft B).leftDerived 1).obj A

/-- The complex `P ⊗ B` attached to a projective resolution `P` of `A`. -/
noncomputable abbrev resolutionTensor (B : ModuleCat ℤ) {A : ModuleCat ℤ}
    (P : ProjectiveResolution A) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((tensorLeft B).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

/-- `Tor₁(A,B)` is the first homology of the tensored resolution: the derived functor computed from
any chosen projective resolution. -/
noncomputable def torOneIsoHomology {A B : ModuleCat ℤ} (P : ProjectiveResolution A) :
    torOne A B ≅
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
        (resolutionTensor B P) :=
  P.isoLeftDerivedObj (tensorLeft B) 1

/-- For a two-term projective resolution, `Tor₁(A,B)` is the kernel of the tensored first
differential — the presentation-level `torKernel` of `cards/TorReductions.lean`. -/
noncomputable def torOneIsoKernel {A B : ModuleCat ℤ} (P : ProjectiveResolution A)
    (h2 : IsZero (P.complex.X 2)) :
    torOne A B ≅ Limits.kernel ((resolutionTensor B P).d 1 0) :=
  torOneIsoHomology P ≪≫
    homologyOneIsoKernelOfD (K := resolutionTensor B P) (by
      have hd : (P.complex).d 2 1 = 0 := IsZero.eq_of_src h2 _ _
      rw [show (resolutionTensor B P).d 2 1 =
        (tensorLeft B).map ((P.complex).d 2 1) from rfl, hd, Functor.map_zero])

/-- **`Tor₁(A,B)` is the kernel of `K ⊗ B → F ⊗ B`** for a surjective finite free presentation of
`A`: the free-resolution instantiation that §5b records as missing. It is `torOneIsoKernel` applied
to `twoTermProjectiveResolution`, whose degree two is the zero object by construction. -/
noncomputable def torOneIsoKernelCyclic (r : ℕ) (f : (Fin r → ℤ) →ₗ[ℤ] A) (hf : Function.Surjective f)
    (B : ModuleCat ℤ) :
    torOne (ModuleCat.of ℤ A) B ≅
      Limits.kernel ((resolutionTensor B (twoTermProjectiveResolution r f hf)).d 1 0) :=
  torOneIsoKernel (twoTermProjectiveResolution r f hf) (twoTermComplex_isZero_X_two r f)

/-- **`Tor₁` of a projective module vanishes**, in every second argument: the higher left derived
functors of `tensorLeft B` die on projectives. This is `ModuleCat ℤ`'s projectivity used through
Mathlib's `Functor.isZero_leftDerived_obj_projective_succ`, and it is the vanishing half of the
`Tor` statements the cards need, at the level of the derived functor rather than of a chosen
presentation. -/
theorem isZero_torOne_of_projective {A : ModuleCat ℤ} [Projective A] (B : ModuleCat ℤ) :
    IsZero (torOne A B) :=
  Functor.isZero_leftDerived_obj_projective_succ (tensorLeft B) 0 A

/-- **`Tor₁(A,B) = 0` for finitely generated torsion-free `A`** — the direction of §3.A exercise 2
that the card records as a citation. Over `ℤ` a finitely generated torsion-free module is free
(`Module.free_of_finite_type_torsion_free'`, the primed form at this pin), a free module is
projective (`Module.Projective.of_free`, `ModuleCat.projective_of_category_module_projective`), and
`Tor₁` of a projective module vanishes. No presentation is chosen and no resolution is built: the
statement holds for every `B` at once. -/
theorem isZero_torOne_of_finite_torsionFree (A : Type) [AddCommGroup A] [Module ℤ A]
    [Module.Finite ℤ A] [Module.IsTorsionFree ℤ A] (B : ModuleCat ℤ) :
    IsZero (torOne (ModuleCat.of ℤ A) B) :=
  isZero_torOne_of_projective (A := ModuleCat.of ℤ A) B


/-! ### The cyclic computation

`Tor₁(ℤ/n, B)` is the `n`-torsion of `B`. The syzygy of the canonical presentation `ℤ → ℤ/n` is `ℤ`
with generator `n`, and tensoring its inclusion with `B` turns it into multiplication by `n`, so the
kernel of `torOneIsoKernel` is `B[n]` up to the tensor unit isomorphisms.

This file carries the first half of that: the presentation, its surjectivity, the divisibility
describing its syzygy, and `syzygyEquiv`, which identifies that syzygy with `ℤ`. The second half —
transporting `kernel ((resolutionTensor B (cyclicResolution n)).d 1 0)` to `kernel (mulByIntEndo B
  n)`
— is **not** here. What follows is the isolated blocker, with the facts checked in the pinned
elaborator, so that the next attempt starts from them.

1. `↥((resolutionTensor B (cyclicResolution n)).X j)` is **not** definitionally
   `TensorProduct ℤ ↥B ↥((cyclicResolution n).complex.X j)`: `rfl` fails for both `j`, so the
   left-tensored objects cannot be used as the ambient type of a pure tensor.
2. Consequently the square has to be stated on the *right*-tensored objects, i.e. on the packaging
   that `cards/TorBridge.lean` already carries (`diffRight`, `commDom`, `commCod`, `diff_square`,
   `torOneIsoDiffRight`); a certificate cannot import it, so the packaging was copied in, elaborated
   cleanly — with the ambient tensor module structure pinned by `[local instance]`, exactly as
   `mX1B`/`mX0B` do there — and then removed again, because nothing here consumes it yet. That is
   where the cyclic computation has to live.
3. On those objects the residual obstruction is the *coordinate*: an element of `X 1` does not
  coerce
   to `Fin 1 → ℤ` by ascription, although `↥(X 1) = ↥(LinearMap.ker (cyclicPresentation n))` holds
     by
   `rfl` (checked); it needs `cycSyzygy`-style transport first, because the coercion is elaborated
   where the `Module` structure, not the carrier, is what has to unify.
4. Matching `TensorProduct.congr_tmul` then fails on `(TensorProduct.congr f g) (x ⊗ₜ b)` when `x`
   is typed through `X 1` rather than through `ker`: the pattern is syntactic in the tensor factor's
   type. `erw` closes the gap but exceeds the default 200000-heartbeat budget on this term.
5. Two syntactic walls remain for the final arithmetic, both quote-able: `ModuleCat.Hom.hom` versus
   `ConcreteCategory.hom` blocks `ModuleCat.comp_apply` from rewriting `(f ≫ g) y`; and the closed
   scalar equation `(↑x 0 / ↑n) • b = (↑x 0 / ↑n) • b` is *not* `rfl`, because the two sides carry
   `DistribMulAction.toDistribSMul.toSMul` and `ZSMul.toSMul` respectively. The bridging lemma for
   the second is `Int.cast_smul_eq_zsmul`; the first needs `change` to a `(cycCod …).hom ((…) y)`
   shape, which does work.

Nothing above is a mathematical obstruction: `Tor₁(ℤ/n, B) ≅ B[n]` is the standard computation, and
`n * (a / n) = a` for `n ∣ a` is `Int.mul_ediv_cancel'`. What is missing is the plumbing through the
three shapes in items 1, 3 and 5. -/

/-- The canonical cyclic presentation `ℤ → ℤ/n`, sending `1` to a generator. -/
noncomputable def cyclicPresentation (n : ℕ) : (Fin 1 → ℤ) →ₗ[ℤ] ZMod n where
  toFun x := (x 0 : ZMod n)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The cyclic presentation is surjective: `ℤ` maps onto `ℤ/n`. -/
theorem cyclicPresentation_surjective (n : ℕ) : Function.Surjective (cyclicPresentation n) := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective (n := n) y
  exact ⟨fun _ => a, by simp [cyclicPresentation]⟩

/-- The syzygy of the cyclic presentation is the subgroup of vectors whose first coordinate is
divisible by `n`. -/
theorem cyclicPresentation_ker_dvd (n : ℕ) {x : Fin 1 → ℤ} (hx : cyclicPresentation n x = 0) :
    (n : ℤ) ∣ x 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd (x 0) n).mp hx

/-- **The syzygy is `ℤ`**, with generator the vector `n`. -/
noncomputable def syzygyEquiv (n : ℕ) (hn : n ≠ 0) :
    ↥(LinearMap.ker (cyclicPresentation n)) ≃ₗ[ℤ] ℤ where
  toFun x := x.1 0 / (n : ℤ)
  invFun c := ⟨fun _ => (n : ℤ) * c, by
    show ((((n : ℤ) * c : ℤ)) : ZMod n) = 0
    rw [Int.cast_mul]
    have h : ((n : ℤ) : ZMod n) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) n).mpr (dvd_refl _)
    rw [h, zero_mul]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i
    dsimp
    exact Int.mul_ediv_cancel' (cyclicPresentation_ker_dvd n x.2)
  right_inv c := by
    dsimp
    rw [mul_comm]
    exact Int.mul_ediv_cancel c (by exact_mod_cast hn)
  map_add' x y := by
    show (x.1 + y.1) 0 / (n : ℤ) = x.1 0 / (n : ℤ) + y.1 0 / (n : ℤ)
    rw [Pi.add_apply, Int.add_ediv_of_dvd_right (cyclicPresentation_ker_dvd n y.2)]
  map_smul' c x := by
    show (c • x.1) 0 / (n : ℤ) = c • (x.1 0 / (n : ℤ))
    rw [Pi.smul_apply, smul_eq_mul, Int.mul_ediv_assoc c (cyclicPresentation_ker_dvd n x.2),
      smul_eq_mul]

/-- The two-term projective resolution attached to the cyclic presentation. -/
noncomputable abbrev cyclicResolution (n : ℕ) :
    ProjectiveResolution (ModuleCat.of ℤ (ZMod n)) :=
  twoTermProjectiveResolution 1 (cyclicPresentation n) (cyclicPresentation_surjective n)

/-- Multiplication by `n` on `B`, as an endomorphism of the bundled module. -/
noncomputable abbrev mulByIntEndo (B : ModuleCat ℤ) (n : ℕ) : B ⟶ B :=
  ModuleCat.ofHom (((n : ℤ) • LinearMap.id : ↥B →ₗ[ℤ] ↥B))

end TorBridgeLocal


end Cyclic

namespace Reductions

open TensorProduct

/-- Multiplication by an integer, as an endomorphism of `ℤ`. -/
def mulByInt (n : ℤ) : ℤ →ₗ[ℤ] ℤ where
  toFun r := n * r
  map_add' r s := by ring
  map_smul' c r := by
    show n * (c * r) = c * (n * r)
    ring

@[simp]
theorem mulByInt_apply (n r : ℤ) : mulByInt n r = n * r := rfl

variable {B : Type*} [AddCommGroup B]

/-- The presentation-level `Tor`: for a presentation `f : K →ₗ[ℤ] F` and a group `B`, the
kernel of `f ⊗ id_B`. -/
def torKernel {K F : Type*} [AddCommGroup K] [AddCommGroup F] (f : K →ₗ[ℤ] F) :=
  (f.rTensor B).ker

/-- Hatcher, Proposition 3A.5(3), the free case at the presentation level: a presentation
whose kernel is trivial presents a free group, and then `Tor` vanishes. -/
theorem torKernel_eq_bot_of_subsingleton {K F : Type*} [AddCommGroup K] [AddCommGroup F]
    [Subsingleton K] (f : K →ₗ[ℤ] F) : torKernel (B := B) f = ⊥ :=
  Subsingleton.elim _ _

/-- Hatcher, Proposition 3A.5(5), the group on the right: the `n`-torsion of `B` is the
kernel of multiplication by `n`. -/
theorem torsionBy_eq_ker (n : ℤ) :
    Submodule.torsionBy ℤ B n = (DistribSMul.toLinearMap ℤ B n).ker := rfl

/-- Hatcher, Proposition 3A.5(3), hypothesis: a torsion-free `ℤ`-module is flat. Reused from
Mathlib's Dedekind-domain instance rather than reproved. -/
theorem flat_of_torsionFree {M : Type*} [AddCommGroup M] [Module.IsTorsionFree ℤ M] :
    Module.Flat ℤ M :=
  inferInstance

/-- Hatcher, Proposition 3A.5(6), the flatness form: tensoring with a flat module preserves
injectivity, so a flat quotient kills the connecting map. Reused from Mathlib. -/
theorem rTensor_injective_of_flat {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module.Flat ℤ M] (f : N →ₗ[ℤ] P) (hf : Function.Injective f) :
    Function.Injective (LinearMap.rTensor M f) :=
  Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- `E-HAT-3.A-2`: the quotient by the torsion subgroup is torsion-free, which is the
hypothesis that makes `A/T(A)` flat and kills the connecting map of the Tor sequence for
`(T(A), A, A/T(A))`. Reused from Mathlib's `Submodule.torsion_eq_bot`. -/
theorem torsionFree_quotient_torsion (M : Type*) [AddCommGroup M] :
    Module.IsTorsionFree ℤ (M ⧸ Submodule.torsion ℤ M) :=
  inferInstance

/-- Consequece of the previous lemma and `flat_of_torsionFree`: the quotient of an abelian
group by its torsion subgroup is flat over `ℤ`. -/
theorem flat_quotient_torsion (M : Type*) [AddCommGroup M] :
    Module.Flat ℤ (M ⧸ Submodule.torsion ℤ M) :=
  @flat_of_torsionFree (M ⧸ Submodule.torsion ℤ M) _ (torsionFree_quotient_torsion M)

/-- `E-HAT-3.A-2`, exercise 5's first ingredient: a torsion-free `ℤ`-module spanned by a
finite family is free. Reused from Mathlib's principal-ideal-domain result
`Module.free_of_finite_type_torsion_free`; the finiteness hypothesis is kept explicit as a
`Finite` index type and a spanning family. -/
theorem free_of_finite_torsionFree {M : Type*} [AddCommGroup M]
    [Module.IsTorsionFree ℤ M] {ι : Type*} [Finite ι] {s : ι → M}
    (hs : Submodule.span ℤ (Set.range s) = ⊤) : Module.Free ℤ M :=
  Module.free_of_finite_type_torsion_free (R := ℤ) hs

/-- Under `ℤ ⊗ B ≅ B`, tensoring `n · id` with `id_B` is multiplication by `n` on `B`. -/
theorem lid_rTensor_mulByInt (n : ℤ) (x : TensorProduct ℤ ℤ B) :
    (TensorProduct.lid ℤ B) ((mulByInt n).rTensor B x) =
      (DistribSMul.toLinearMap ℤ B n) ((TensorProduct.lid ℤ B) x) := by
  have key :
      (TensorProduct.lid ℤ B).toLinearMap.comp ((mulByInt n).rTensor B) =
        (DistribSMul.toLinearMap ℤ B n).comp (TensorProduct.lid ℤ B).toLinearMap := by
    refine LinearMap.ext fun y => ?_
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
        simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, mulByInt_apply,
          TensorProduct.lid_tmul, DistribSMul.toLinearMap_apply]
        exact mul_smul n r b
    | add y z hy hz => simp only [map_add, hy, hz]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using congrArg (fun g => g x) key

/-- Hatcher, Proposition 3A.5(5) at the presentation level: the kernel of `(n · id) ⊗ id_B`
inside `ℤ ⊗ B` is carried by `ℤ ⊗ B ≅ B` onto the `n`-torsion of `B`, that is,
`Tor(ℤ/n, B) ≅ B[n]` for this resolution. -/
theorem map_torKernel_mulByInt (n : ℤ) :
    (torKernel (B := B) (mulByInt n)).map (TensorProduct.lid ℤ B).toLinearMap =
      Submodule.torsionBy ℤ B n := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (mulByInt n).rTensor B x = 0 := hx
    have h := lid_rTensor_mulByInt (B := B) n x
    rw [hx', map_zero] at h
    exact (Submodule.mem_torsionBy_iff n _).mpr h.symm
  · intro hb
    have hb' : (DistribSMul.toLinearMap ℤ B n) b = 0 :=
      (Submodule.mem_torsionBy_iff n b).mp hb
    refine ⟨(TensorProduct.lid ℤ B).symm b, ?_, ?_⟩
    · have h1 : (TensorProduct.lid ℤ B) ((mulByInt n).rTensor B ((TensorProduct.lid ℤ B).symm b)) =
      0 := by
        rw [lid_rTensor_mulByInt, LinearEquiv.apply_symm_apply, hb']
      exact (TensorProduct.lid ℤ B).injective (by rw [h1, map_zero])
    · exact LinearEquiv.apply_symm_apply (TensorProduct.lid ℤ B) b

/-- If `p • x = 0` forces `x = 0` then `p^k • x = 0` does. -/
theorem eq_zero_of_pow_smul_eq_zero {C : Type*} [AddCommGroup C] {p : ℤ}
    (h : ∀ x : C, p • x = 0 → x = 0) (k : ℕ) : ∀ x : C, p ^ k • x = 0 → x = 0 := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ, ← smul_smul] at hx
      exact h x (ih (p • x) hx)

/-- The form the card uses to kill the connecting map: if `C` has no `p`-torsion then
`C[p^k] = 0` for every `k`, and so `Tor(ℤ/p^k, C) = 0` by the identification above. This is
the correct hypothesis in that step: `B/B_p` has no `p`-torsion, but it is *not* torsion-free
(for `p = 2`, `B = ℤ/2 ⊕ ℤ/3` gives `B/B_2 = ℤ/3`). -/
theorem torsionBy_pow_eq_bot_of_no_p_torsion {C : Type*} [AddCommGroup C] {p : ℕ}
    (h : Submodule.torsionBy ℤ C (p : ℤ) = ⊥) (k : ℕ) :
    Submodule.torsionBy ℤ C ((p : ℤ) ^ k) = ⊥ := by
  have h' : ∀ x : C, (p : ℤ) • x = 0 → x = 0 := by
    intro x hx
    have hx' : x ∈ Submodule.torsionBy ℤ C (p : ℤ) :=
      (Submodule.mem_torsionBy_iff (p : ℤ) x).mpr hx
    rwa [h, Submodule.mem_bot] at hx'
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  exact eq_zero_of_pow_smul_eq_zero h' k x ((Submodule.mem_torsionBy_iff ((p : ℤ) ^ k) x).mp hx)

/-- The premise the card uses, with the hypothesis made explicit. If `P` is a subgroup
containing exactly the elements killed by some power of `p` — the `p`-primary torsion
subgroup `B_p` — then `P` is saturated for multiplication by `p`, which says precisely that
the quotient `B/P` has no `p`-torsion: `p • [x] = 0` means `p • x ∈ P`, hence `x ∈ P`, hence
`[x] = 0`.

This is the correct premise in that step and it is strictly weaker than torsion-freeness:
for `p = 2` and `B = ℤ/2 ⊕ ℤ/3` the quotient `B/B_2 = ℤ/3` is not torsion-free, but it has
no `2`-torsion. Rule (3) of Hatcher's Proposition 3A.5 cannot be applied to it; rule (5)
can, and that is what the card now does. -/
theorem mem_of_p_smul_mem_of_pPrimary {B : Type*} [AddCommGroup B] {p : ℤ}
    {P : Submodule ℤ B} (hP : ∀ x : B, x ∈ P ↔ ∃ k : ℕ, p ^ k • x = 0) {x : B}
    (hx : p • x ∈ P) : x ∈ P := by
  obtain ⟨k, hk⟩ := (hP (p • x)).mp hx
  exact (hP x).mpr ⟨k + 1, by rw [pow_succ, ← smul_smul]; exact hk⟩

/-- Hatcher, Proposition 3A.5(2), the computation: tensoring a product map with `id_B`
commutes with the distributivity isomorphism of `TensorProduct.prodLeft`. This is the
mathematical content of additivity at the presentation level. -/
theorem prodLeft_comp_rTensor {K₁ K₂ F₁ F₂ : Type*} [AddCommGroup K₁] [AddCommGroup K₂]
    [AddCommGroup F₁] [AddCommGroup F₂] (f₁ : K₁ →ₗ[ℤ] F₁) (f₂ : K₂ →ₗ[ℤ] F₂) :
    (TensorProduct.prodLeft ℤ ℤ F₁ F₂ B).toLinearMap.comp ((f₁.prodMap f₂).rTensor B) =
      ((f₁.rTensor B).prodMap (f₂.rTensor B)).comp
        (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.mk_zero_zero]
  | tmul k b => obtain ⟨k₁, k₂⟩ := k; simp [TensorProduct.prodLeft_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Hatcher, Proposition 3A.5(2) at the presentation level: the presentation of a direct
sum is the direct sum of the presentations, so the presentation-level `Tor` splits. Here
`torKernel (f₁ ⊕ f₂)` is the kernel of `(f₁ ⊕ f₂) ⊗ id_B` inside `(K₁ × K₂) ⊗ B`, and the
statement says that the distributivity isomorphism
`TensorProduct.prodLeft` carries it onto `Tor(f₁) × Tor(f₂)`.

The proof avoids the `.symm` of `prodLeft` on arbitrary elements — which is where the
earlier attempt stalled, because `prodLeft_tmul` and `apply_symm_apply` are available in
different coercion shapes — by rewriting the kernel as a `comap` and mapping it forward;
`Submodule.map_comap_eq_self` only needs `prodLeft` to be onto its kernel, and the whole
element-level content is the composition identity `prodLeft_comp_rTensor`. -/
theorem map_prodLeft_torKernel {K₁ K₂ F₁ F₂ : Type*} [AddCommGroup K₁] [AddCommGroup K₂]
    [AddCommGroup F₁] [AddCommGroup F₂] (f₁ : K₁ →ₗ[ℤ] F₁) (f₂ : K₂ →ₗ[ℤ] F₂) :
    (torKernel (B := B) (f₁.prodMap f₂)).map
        (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap =
      (torKernel (B := B) f₁).prod (torKernel (B := B) f₂) := by
  have key := prodLeft_comp_rTensor (B := B) f₁ f₂
  have hcomap : LinearMap.ker ((f₁.prodMap f₂).rTensor B)
      = (LinearMap.ker ((f₁.rTensor B).prodMap (f₂.rTensor B))).comap
          (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker]
    have h := LinearMap.congr_fun key x
    simp only [LinearMap.comp_apply] at h
    rw [← h]
    constructor
    · intro hx; rw [hx, map_zero]
    · intro hx
      exact (TensorProduct.prodLeft ℤ ℤ F₁ F₂ B).injective (by simpa using hx)
  simp only [torKernel]
  have hside : ((LinearMap.rTensor B f₁).prodMap (f₂.rTensor B)).ker ≤
      (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap.range := by
    intro y _
    exact ⟨(TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).symm y, LinearEquiv.apply_symm_apply _ y⟩
  rw [hcomap, Submodule.map_comap_eq_self hside, LinearMap.ker_prodMap]

/-! ## The filtered-colimit passage (Exercise 4 of §3.A): still open

With additivity proved, the remaining step shared by `E-HAT-3.A-6` and `E-HAT-3.A-2` is that
`Tor` commutes with the filtered colimit of the finitely generated subgroups of a torsion-free
group, and with the directed union of the `p`-primary subgroups in `A_p = colim A_{p,α}`. That
needs `⊗` commuting with filtered colimits of abelian groups together with additivity; it is
not proved here and is listed as an obligation in `proofs/README.md`. -/

/-- The vanishing transfers to the finite stage, which is the point of the Tor passage: for a
flat `F` — in the cards `F` is the free middle term of the presentation — the inclusion
`B' ≤ B` induces an injection `F ⊗ B' → F ⊗ B`, so a finite sum that vanishes in `F ⊗ B`
vanishes already in `F ⊗ B'`. Without this, a finitely supported tensor element would only
show that its image vanishes outside the finite stage.

Reused from Mathlib's `Module.Flat.lTensor_preserves_injective_linearMap` applied to
`Submodule.subtype`; nothing is rebuilt. -/
theorem lTensor_subtype_injective_of_flat {F B : Type*} [AddCommGroup F] [AddCommGroup B]
    [Module.Flat ℤ F] (B' : Submodule ℤ B) :
    Function.Injective (LinearMap.lTensor F B'.subtype) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ B'.subtype_injective

/-- The Tor passage the cards use, in the presentation-level model: every element of
`ker (f ⊗ id_B)` already comes from the Tor of a *finitely generated sub-presentation*
`P ≤ K`, together with the witness that its image vanishes there. This is the statement that
lets `E-HAT-3.A-6` say "the component of the class already lies in some stage" and that
`E-HAT-3.A-2` uses when it writes a torsion-free group as the directed union of its finitely
generated subgroups.

The finite support comes from Mathlib's `TensorProduct.exists_of_fg` (pinned
`RingTheory/TensorProduct/DirectLimitFG.lean`), and the vanishing at the stage is
functoriality of `rTensor` (`rTensor_comp`), not a descent argument: the element already
vanishes, and the stage inclusion is a tensor of linear maps. -/
theorem exists_fg_stage {K F B : Type*} [AddCommGroup K] [AddCommGroup F] [AddCommGroup B]
    (f : K →ₗ[ℤ] F) {x : TensorProduct ℤ K B} (hx : (LinearMap.rTensor B f) x = 0) :
    ∃ (P : Submodule ℤ K) (_ : P.FG) (t : TensorProduct ℤ P B),
      (LinearMap.rTensor B P.subtype) t = x ∧
        (LinearMap.rTensor B (f.comp P.subtype)) t = 0 := by
  obtain ⟨P, hP, t, ht⟩ := TensorProduct.exists_of_fg x
  refine ⟨P, hP, t, ht, ?_⟩
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, ht, hx]

/-- **`E-HAT-3.A-2`, the vanishing direction, at the presentation level.** Let `f : K →ₗ[ℤ] F` be
  the
relation map of a genuine two-term free resolution — injective, with `F` free — and suppose the
quotient `A = F ⧸ range f` is flat. Then the presentation-level kernel vanishes: `f ⊗ id_B` is
injective for every `B`.

This is `LinearMap.lTensor_injective_of_exact_of_flat` applied to the short exact sequence
`0 → K → F → A → 0` (the quotient map is the surjection, `range f` its kernel by
`Submodule.ker_mkQ`), transported from `lTensor` to the `rTensor` factor order that
`torKernel` uses by `LinearMap.lTensor_inj_iff_rTensor_inj`. No connecting map and no snake
lemma is invoked directly: that theory is inside the maintained lemma. -/
theorem rTensor_injective_of_flat_cokernel {K F B : Type*} [AddCommGroup K] [AddCommGroup F]
    [AddCommGroup B] (f : K →ₗ[ℤ] F) (hf : Function.Injective f)
    [Module.Flat ℤ (F ⧸ LinearMap.range f)] :
    Function.Injective (LinearMap.rTensor B f) := by
  have hex : Function.Exact f (LinearMap.range f).mkQ := fun x => by
    simp [Submodule.mkQ_apply, LinearMap.mem_range]
  have hL : Function.Injective (LinearMap.lTensor B f) :=
    LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _) f hf hex B
  exact (LinearMap.lTensor_inj_iff_rTensor_inj B f).mp hL

/-- The kernel form: for a genuine free resolution with flat cokernel, the presentation-level
`Tor` vanishes. -/
theorem torKernel_eq_bot_of_flat_cokernel {K F : Type*} [AddCommGroup K] [AddCommGroup F]
    (f : K →ₗ[ℤ] F) (hf : Function.Injective f) [Module.Flat ℤ (F ⧸ LinearMap.range f)] :
    torKernel (B := B) f = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr (rTensor_injective_of_flat_cokernel (B := B) f hf)


end Reductions

open Cyclic Reductions

section Transport

noncomputable def constOne : ℤ →ₗ[ℤ] (Fin 1 → ℤ) := LinearMap.pi fun _ => LinearMap.id
noncomputable def projZero : (Fin 1 → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj 0

theorem projZero_comp_constOne : projZero.comp constOne = LinearMap.id := by
  apply LinearMap.ext
  intro c
  change (constOne c) 0 = c
  simp only [constOne, LinearMap.pi_apply, LinearMap.id_apply]

theorem d_apply (n : ℕ) (hn : n ≠ 0) (x : ↥(LinearMap.ker (cyclicPresentation n))) :
    ((twoTermComplex 1 (cyclicPresentation n)).d 1 0).hom x
      = constOne ((mulByInt (n : ℤ)) ((syzygyEquiv n hn) x)) := by
  funext i
  fin_cases i
  show x.1 0 = (n : ℤ) * (x.1 0 / (n : ℤ))
  exact (Int.mul_ediv_cancel' (cyclicPresentation_ker_dvd n x.2)).symm

theorem constOne_tmul_eq_zero (B : ModuleCat ℤ) (y : ℤ) (b : ↥B)
    (h : constOne y ⊗ₜ[ℤ] b = (0 : TensorProduct ℤ (Fin 1 → ℤ) ↥B)) :
    y ⊗ₜ[ℤ] b = (0 : TensorProduct ℤ ℤ ↥B) := by
  have h2 := congrArg (LinearMap.rTensor ↥B projZero) h
  simp only [LinearMap.rTensor_tmul, map_zero] at h2
  have hy : projZero (constOne y) = y := LinearMap.congr_fun projZero_comp_constOne y
  rw [hy] at h2
  exact h2

/-- **`constOne` tensored with anything is injective**: `projZero` retracts it, so the tensored
composite `(projZero ⊗ id) ∘ (constOne ⊗ id)` is the identity. -/
theorem ker_constOne_rTensor_eq_bot (B : ModuleCat ℤ) :
    LinearMap.ker (constOne.rTensor ↥B) = ⊥ := by
  have h : (projZero.rTensor ↥B).comp (constOne.rTensor ↥B) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, projZero_comp_constOne, LinearMap.rTensor_id]
  have hlin : Function.LeftInverse (projZero.rTensor ↥B) (constOne.rTensor ↥B) := by
    intro x
    have := LinearMap.congr_fun h x
    simpa using this
  exact LinearMap.ker_eq_bot.mpr hlin.injective

/-- **The transport, for any presentation whose syzygy is identified with `ℤ` by `σ` and whose
relation map is `n · σ`.** The kernel of `subtype ⊗ id_B` is the preimage under `σ ⊗ id_B` of the
kernel of `(n · id) ⊗ id_B`. -/
theorem ker_subtype_rTensor_eq (B : ModuleCat ℤ) (n : ℕ)
    {F : Type*} [AddCommGroup F] [Module ℤ F] (f : (Fin 1 → ℤ) →ₗ[ℤ] F)
    (σ : ↥(LinearMap.ker f) ≃ₗ[ℤ] ℤ)
    (h : ∀ x : ↥(LinearMap.ker f), (LinearMap.ker f).subtype x = constOne ((n : ℤ) * σ x)) :
    LinearMap.ker ((LinearMap.ker f).subtype.rTensor ↥B)
      = Submodule.comap (σ.toLinearMap.rTensor ↥B)
          (LinearMap.ker ((mulByInt (n : ℤ)).rTensor ↥B)) := by
  have hcomp : (LinearMap.ker f).subtype
      = constOne.comp ((mulByInt (n : ℤ)).comp σ.toLinearMap) := by
    apply LinearMap.ext
    intro x
    exact h x
  rw [hcomp, LinearMap.rTensor_comp, LinearMap.rTensor_comp, LinearMap.ker_comp,
    ker_constOne_rTensor_eq_bot B, Submodule.comap_bot, LinearMap.ker_comp]

/-- **The cyclic transport, in the form `Tor₁` uses.** The first differential of the cyclic
resolution is the syzygy subtype, whose kernel under `⊗ B` is the preimage under `syzygyEquiv ⊗ B`
  of
`B[n]`. -/
theorem ker_d_rTensor_eq (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    LinearMap.ker (((twoTermComplex 1 (cyclicPresentation n)).d 1 0).hom.rTensor ↥B)
      = Submodule.comap ((syzygyEquiv n hn).toLinearMap.rTensor ↥B)
          (LinearMap.ker ((mulByInt (n : ℤ)).rTensor ↥B)) := by
  have hsub : ((twoTermComplex 1 (cyclicPresentation n)).d 1 0).hom
      = (LinearMap.ker (cyclicPresentation n)).subtype := rfl
  rw [hsub]
  refine ker_subtype_rTensor_eq (B := B) (n := n) (cyclicPresentation n) (syzygyEquiv n hn) ?_
  intro x
  show x.1 = constOne ((n : ℤ) * (syzygyEquiv n hn x))
  funext i
  fin_cases i
  show x.1 0 = (n : ℤ) * (x.1 0 / (n : ℤ))
  exact (Int.mul_ediv_cancel' (cyclicPresentation_ker_dvd n x.2)).symm

/-- **The preimage becomes an image.** Since `σ ⊗ id_B` is invertible, the image of the preimage of
`ker ((n · id) ⊗ id_B)` under it is that kernel itself. -/
theorem map_ker_d_rTensor_eq (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    (LinearMap.ker (((twoTermComplex 1 (cyclicPresentation n)).d 1 0).hom.rTensor ↥B)).map
        ((syzygyEquiv n hn).toLinearMap.rTensor ↥B)
      = LinearMap.ker ((mulByInt (n : ℤ)).rTensor ↥B) := by
  rw [ker_d_rTensor_eq]
  have h1 : ∀ y : TensorProduct ℤ ℤ ↥B,
      ((syzygyEquiv n hn).toLinearMap.rTensor ↥B)
        (((syzygyEquiv n hn).symm.toLinearMap.rTensor ↥B) y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb]
    | tmul a b =>
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
      congr 1
      exact (syzygyEquiv n hn).apply_symm_apply a
  refine Submodule.map_comap_eq_self ?_
  intro y _
  exact LinearMap.mem_range.mpr
    ⟨((syzygyEquiv n hn).symm.toLinearMap.rTensor ↥B) y, h1 y⟩

/-- Composing the two maps is mapping twice, for the pair this file uses. -/
theorem map_comp_map (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0)
    (p : Submodule ℤ (TensorProduct ℤ
      ↑((twoTermComplex 1 (cyclicPresentation n)).X 1) ↥B)) :
    Submodule.map (((TensorProduct.lid ℤ ↥B).toLinearMap).comp
        ((syzygyEquiv n hn).toLinearMap.rTensor ↥B)) p
      = Submodule.map (TensorProduct.lid ℤ ↥B).toLinearMap
          (Submodule.map ((syzygyEquiv n hn).toLinearMap.rTensor ↥B) p) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.comp_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-! ### The composition: `Tor₁(ℤ/n, B) ≅ B[n]`

The two halves proved above compose, and their composite carrier is injective, so it restricts to
an isomorphism of the cyclic stage's kernel onto `B[n]`. The isomorphism is then packaged through
the bridge `torOneIsoTorKernel` at the cyclic resolution and the categorical-to-linear kernel
identification `ModuleCat.kernelIsoKer`, which is the `Tor₁(ℤ/n, B) ≅ B[n]` sentence.

Two elaboration facts are forced on the spelling, and the file records them.

* The cyclic kernel is spelled through `(LinearMap.ker (cyclicPresentation n)).subtype` — which
  *is* the first differential by `twoTermComplex_d_one_zero` — rather than through the complex's
  `.d 1 0` and its `.hom`. The two spellings name the same submodule (the `hsub` step of
  `map_ker_d_rTensor_eq` is an `rfl`), but the `.hom` spelling's ambient tensor product is
  `↥((twoTermComplex …).X 1) ⊗ ↥B` while the transport map's domain is `↥(ker …) ⊗ ↥B`, and a
  `Submodule.map` that mixes the two is not type-correct at `implicit` transparency, which is what
  `rewrite` needs. Spelling the kernel through the subtype keeps kernel, map and image in the one
  instance world the `rTensor` signatures build.

* The last step is a restatement of `map_torKernel_mulByInt` in this section's instance world
  (`lid_rTensor_mulByInt_carrier`, `map_torKernel_mulByInt_carrier`). The original is stated over
  `{B : Type*} [AddCommGroup B]`, so its tensor products carry `AddCommGroup.toIntModule`, while
  here `B : ModuleCat ℤ` and `↥B` carries the carrier instance `ModuleCat.isModule` — two
  `Submodule` types that are the same structure on paper and different terms in the elaborator, so
  the composition cannot cite the lemma directly. Restating the lemma with an explicit
  `[Module ℤ B]` binder next to `[AddCommGroup B]` does not work either: with two `Module ℤ B`
  instances in scope the elaborator cannot synthesize the `SMulCommClass ℤ ℤ B` that
  `DistribSMul.toLinearMap` demands, and in the carrier world alone the same demand fails because
  the `SMul ℤ ↥B` of the carrier module and the `ZSMul.toSMul` of its additive group are not
  definitionally equal. The carrier-instance section, with the multiplication-by-`n` written as
  `lid (n ⊗ₜ b)` — equal to `n • b` by `TensorProduct.lid_tmul`, which is `rfl` — is the
  pinned-instance repair that works. -/

/-- **The image form of the cyclic transport, at the `.subtype` spelling.** The kernel of the
tensored differential is carried by `syzygyEquiv ⊗ id_B` onto the kernel of
`(n · id) ⊗ id_B`. -/
theorem map_ker_subtype_rTensor_eq (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    (LinearMap.ker (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B)).map
        ((syzygyEquiv n hn).toLinearMap.rTensor ↥B)
      = LinearMap.ker ((mulByInt (n : ℤ)).rTensor ↥B) := by
  have hcyc : ∀ x : ↥(LinearMap.ker (cyclicPresentation n)),
      (LinearMap.ker (cyclicPresentation n)).subtype x
        = constOne ((n : ℤ) * (syzygyEquiv n hn x)) := by
    intro x
    show x.1 = constOne ((n : ℤ) * (syzygyEquiv n hn x))
    funext i
    fin_cases i
    show x.1 0 = (n : ℤ) * (x.1 0 / (n : ℤ))
    exact (Int.mul_ediv_cancel' (cyclicPresentation_ker_dvd n x.2)).symm
  have h1 : ∀ y : TensorProduct ℤ ℤ ↥B,
      ((syzygyEquiv n hn).toLinearMap.rTensor ↥B)
        (((syzygyEquiv n hn).symm.toLinearMap.rTensor ↥B) y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb]
    | tmul a b =>
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
      congr 1
      exact (syzygyEquiv n hn).apply_symm_apply a
  rw [ker_subtype_rTensor_eq (B := B) (n := n) (cyclicPresentation n) (syzygyEquiv n hn) hcyc]
  exact Submodule.map_comap_eq_self fun y _ =>
    LinearMap.mem_range.mpr ⟨((syzygyEquiv n hn).symm.toLinearMap.rTensor ↥B) y, h1 y⟩

/-- The transport map of the cyclic stage: `syzygyEquiv ⊗ id_B` followed by `ℤ ⊗ B ≅ B`. The
type is left to inference, which is the `rTensor` instance world. -/
noncomputable def cycTransport (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :=
  ((TensorProduct.lid ℤ ↥B).toLinearMap).comp ((syzygyEquiv n hn).toLinearMap.rTensor ↥B)

/-- Tensoring the syzygy equivalence with `id_B` is retracted by tensoring its inverse with
`id_B`. -/
theorem rTensor_syzygy_symm_apply_apply (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0)
    (x : TensorProduct ℤ ↥(LinearMap.ker (cyclicPresentation n)) ↥B) :
    ((syzygyEquiv n hn).symm.toLinearMap.rTensor ↥B)
      (((syzygyEquiv n hn).toLinearMap.rTensor ↥B) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    exact congrArg (fun c => c ⊗ₜ[ℤ] b) ((syzygyEquiv n hn).symm_apply_apply a)

/-- The transport map is injective: `ℤ ⊗ B ≅ B` is an equivalence and `syzygyEquiv ⊗ id_B` is
retracted by `syzygyEquiv⁻¹ ⊗ id_B`. -/
theorem cycTransport_injective (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (cycTransport B n hn) := by
  have h2 : Function.Injective ((syzygyEquiv n hn).toLinearMap.rTensor ↥B) := by
    intro x y h
    rw [← rTensor_syzygy_symm_apply_apply B n hn x, ← rTensor_syzygy_symm_apply_apply B n hn y, h]
  intro x y h
  apply h2
  apply (TensorProduct.lid ℤ ↥B).injective
  exact h

/-- `lid_rTensor_mulByInt` restated in the `ModuleCat`-carrier instance world: under
`ℤ ⊗ B ≅ B`, tensoring `n · id` with `id_B` is multiplication by `n` on `B`. The multiplication
is written `lid (n ⊗ₜ b)`, which equals `n • b` by `TensorProduct.lid_tmul` — an `rfl` — because
the bare `n • b` elaborates with the additive group's `ZSMul.toSMul` while the torsion
submodule's membership uses the carrier module's `SMul`, and the two are not definitionally
equal. -/
theorem lid_rTensor_mulByInt_carrier (B : ModuleCat ℤ) (n : ℤ)
    (x : TensorProduct ℤ ℤ ↥B) :
    (TensorProduct.lid ℤ ↥B) ((mulByInt n).rTensor ↥B x) =
      (TensorProduct.lid ℤ ↥B) ((n : ℤ) ⊗ₜ[ℤ] ((TensorProduct.lid ℤ ↥B) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | tmul r b =>
    simp only [LinearMap.rTensor_tmul, mulByInt_apply, TensorProduct.lid_tmul]
    module

/-- **`map_torKernel_mulByInt` restated in the `ModuleCat`-carrier instance world**: the kernel
of `(n · id) ⊗ id_B` inside `ℤ ⊗ B` is carried by `ℤ ⊗ B ≅ B` onto the `n`-torsion of `B`. -/
theorem map_torKernel_mulByInt_carrier (B : ModuleCat ℤ) (n : ℤ) :
    (LinearMap.ker ((mulByInt n).rTensor ↥B)).map (TensorProduct.lid ℤ ↥B).toLinearMap =
      Submodule.torsionBy ℤ ↥B n := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (mulByInt n).rTensor ↥B x = 0 := hx
    have h := lid_rTensor_mulByInt_carrier B n x
    rw [hx', map_zero] at h
    refine (Submodule.mem_torsionBy_iff n _).mpr ?_
    show (TensorProduct.lid ℤ ↥B) ((n : ℤ) ⊗ₜ[ℤ] ((TensorProduct.lid ℤ ↥B) x)) = 0
    exact h.symm
  · intro hb
    have hb' : (TensorProduct.lid ℤ ↥B) ((n : ℤ) ⊗ₜ[ℤ] (b : ↥B)) = 0 :=
      (Submodule.mem_torsionBy_iff n b).mp hb
    refine ⟨(TensorProduct.lid ℤ ↥B).symm b, ?_, ?_⟩
    · have h1 : (TensorProduct.lid ℤ ↥B)
          ((mulByInt n).rTensor ↥B ((TensorProduct.lid ℤ ↥B).symm b)) = 0 := by
        rw [lid_rTensor_mulByInt_carrier, LinearEquiv.apply_symm_apply]
        exact hb'
      exact (TensorProduct.lid ℤ ↥B).injective (by rw [h1, map_zero])
    · exact LinearEquiv.apply_symm_apply (TensorProduct.lid ℤ ↥B) b

/-- **The cyclic stage's kernel is carried into `B[n]`.** An element of the kernel is carried by
the transport map into the `n`-torsion of `B`: its image under `syzygyEquiv ⊗ id_B` lies in the
kernel of `(n · id) ⊗ id_B` by the transport theorem, and `ℤ ⊗ B ≅ B` carries that kernel onto
`B[n]`. -/
theorem mem_torsionBy_of_mem_ker (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0)
    (x : ↥(LinearMap.ker (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B))) :
    cycTransport B n hn x ∈ Submodule.torsionBy ℤ ↥B (n : ℤ) := by
  have hker : ((syzygyEquiv n hn).toLinearMap.rTensor ↥B) x.val
      ∈ LinearMap.ker ((mulByInt (n : ℤ)).rTensor ↥B) := by
    have hmap : ((syzygyEquiv n hn).toLinearMap.rTensor ↥B) x.val ∈ (LinearMap.ker
        (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B)).map
        ((syzygyEquiv n hn).toLinearMap.rTensor ↥B) :=
      Submodule.mem_map.mpr ⟨x.val, x.2, rfl⟩
    rwa [map_ker_subtype_rTensor_eq B n hn] at hmap
  have h := lid_rTensor_mulByInt_carrier B (n : ℤ)
    (((syzygyEquiv n hn).toLinearMap.rTensor ↥B) x.val)
  rw [show ((mulByInt (n : ℤ)).rTensor ↥B)
      (((syzygyEquiv n hn).toLinearMap.rTensor ↥B) x.val) = 0 from LinearMap.mem_ker.mp hker,
    map_zero] at h
  refine (Submodule.mem_torsionBy_iff (n : ℤ) _).mpr ?_
  show (TensorProduct.lid ℤ ↥B) ((n : ℤ) ⊗ₜ[ℤ]
      ((TensorProduct.lid ℤ ↥B) (((syzygyEquiv n hn).toLinearMap.rTensor ↥B) x.val))) = 0
  exact h.symm

/-- Every element of `B[n]` is the image under the transport map of an element of the kernel:
`ℤ ⊗ B ≅ B` lifts it into the kernel of `(n · id) ⊗ id_B`, and the transport theorem maps the
cyclic kernel onto that kernel. -/
theorem exists_mem_ker_of_mem_torsionBy (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0)
    (y : ↥(Submodule.torsionBy ℤ ↥B (n : ℤ))) :
    ∃ x : ↥(LinearMap.ker (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B)),
      cycTransport B n hn x = (y : ↥B) := by
  have h0 : (TensorProduct.lid ℤ ↥B) ((n : ℤ) ⊗ₜ[ℤ] (y : ↥B)) = 0 :=
    (Submodule.mem_torsionBy_iff (n : ℤ) (y : ↥B)).mp y.2
  have h := lid_rTensor_mulByInt_carrier B (n : ℤ)
    ((TensorProduct.lid ℤ ↥B).symm (y : ↥B))
  rw [LinearEquiv.apply_symm_apply] at h
  have hz : (TensorProduct.lid ℤ ↥B)
      ((mulByInt (n : ℤ)).rTensor ↥B ((TensorProduct.lid ℤ ↥B).symm (y : ↥B))) = 0 := by
    rw [h]
    exact h0
  have hmem : ((mulByInt (n : ℤ)).rTensor ↥B)
      ((TensorProduct.lid ℤ ↥B).symm (y : ↥B)) = 0 :=
    (TensorProduct.lid ℤ ↥B).injective (by rw [hz, map_zero])
  have himg : (TensorProduct.lid ℤ ↥B).symm (y : ↥B)
      ∈ LinearMap.ker ((mulByInt (n : ℤ)).rTensor ↥B) := LinearMap.mem_ker.mpr hmem
  rw [← map_ker_subtype_rTensor_eq B n hn] at himg
  obtain ⟨a, ha, hfa⟩ := Submodule.mem_map.mp himg
  refine ⟨⟨a, ha⟩, ?_⟩
  show (TensorProduct.lid ℤ ↥B) (((syzygyEquiv n hn).toLinearMap.rTensor ↥B) a) = (y : ↥B)
  rw [hfa, LinearEquiv.apply_symm_apply]

/-- **The composition.** The kernel of the cyclic resolution's tensored first differential,
carried by `syzygyEquiv ⊗ id_B` and then by `ℤ ⊗ B ≅ B`, is exactly the `n`-torsion of `B`. The
membership lemmas on either side of the inclusion are the two halves, so the equality needs no
rewrite. -/
theorem map_ker_d_rTensor_lid_eq_torsionBy (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    Submodule.map (((TensorProduct.lid ℤ ↥B).toLinearMap).comp
        ((syzygyEquiv n hn).toLinearMap.rTensor ↥B))
        (LinearMap.ker (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B))
      = Submodule.torsionBy ℤ ↥B (n : ℤ) := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_torsionBy_of_mem_ker B n hn ⟨x, hx⟩
  · intro hb
    obtain ⟨x, hx⟩ := exists_mem_ker_of_mem_torsionBy B n hn ⟨b, hb⟩
    exact ⟨x, x.2, hx⟩

/-- The transport map restricted to the cyclic stage's kernel, corestricted to `B[n]`. -/
noncomputable def kerMapTorsionBy (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    ↥(LinearMap.ker (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B)) →ₗ[ℤ]
      ↥(Submodule.torsionBy ℤ ↥B (n : ℤ)) :=
  ((cycTransport B n hn).comp (LinearMap.ker
    (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B)).subtype).codRestrict _
    (fun x => mem_torsionBy_of_mem_ker B n hn x)

/-- The corestricted transport map is injective, because the transport map is. -/
theorem kerMapTorsionBy_injective (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (kerMapTorsionBy B n hn) := by
  intro x y h
  exact Subtype.ext (cycTransport_injective B n hn (congrArg Subtype.val h))

/-- The corestricted transport map is surjective, because every element of `B[n]` is the image
of an element of the kernel. -/
theorem kerMapTorsionBy_surjective (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (kerMapTorsionBy B n hn) := by
  intro y
  obtain ⟨x, hx⟩ := exists_mem_ker_of_mem_torsionBy B n hn y
  exact ⟨x, Subtype.ext hx⟩

/-- **The cyclic stage's kernel is the `n`-torsion of `B`.** Restricting the transport map to
the kernel of the tensored first differential gives a linear equivalence onto `B[n]`: the image
lies in `B[n]` and every element of `B[n]` is hit, and the restriction is injective because the
transport map is. -/
noncomputable def kerEquivTorsionBy (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    ↥(LinearMap.ker (((LinearMap.ker (cyclicPresentation n)).subtype).rTensor ↥B)) ≃ₗ[ℤ]
      ↥(Submodule.torsionBy ℤ ↥B (n : ℤ)) :=
  LinearEquiv.ofBijective (kerMapTorsionBy B n hn)
    ⟨kerMapTorsionBy_injective B n hn, kerMapTorsionBy_surjective B n hn⟩

/-- **`Tor₁(ℤ/n, B) ≅ B[n]`.** For every abelian group `B`, as an object of `ModuleCat ℤ`, and
every `n ≥ 1`: the first left derived functor of `tensorLeft B` at `ℤ/n` is isomorphic to the
`n`-torsion submodule of `B`. The isomorphism composes the packaged bridge `torOneIsoTorKernel`
at the cyclic resolution, the categorical-to-linear kernel identification
`ModuleCat.kernelIsoKer`, and the restriction `kerEquivTorsionBy` of the transport map to the
kernel. -/
noncomputable def torOneCyclicIsoTorsionBy (B : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0) :
    CyclicTransport.torOne (ModuleCat.of ℤ (ZMod n)) B ≅
      ModuleCat.of ℤ ↥(Submodule.torsionBy ℤ ↥B (n : ℤ)) :=
  (torOneIsoTorKernel (B := B) (P := cyclicResolution n)
      (twoTermComplex_isZero_X_two 1 (cyclicPresentation n))).trans
    ((ModuleCat.kernelIsoKer (diffRight (B := B) (cyclicResolution n))).trans
      (kerEquivTorsionBy B n hn).toModuleIso)

end Transport

end CyclicTransport

