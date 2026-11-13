/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Data.ZMod.Basic
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
# TorFreeResolution: the two-term free resolution and Tor one as the kernel of its tensored
  differential

Card `E-HAT-3.A-6 / E-HAT-3.A-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/TorFreeResolution.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/TorFreeResolution.lean` with the `def` names carrying underscores renamed per the
  `defsWithUnderscore` lint (`coker_subtype_iso` -> `cokerSubtypeIso`, `torOne_iso_kernel` ->
    `torOneIsoKernel`); theorem names keep the certificate's spelling.
-/


/-!
# The syzygy of a finite free presentation is free

`proofs/README.md` §5b records that the application of Hatcher's Lemma 3A.2 to the cards needs a
*genuine* free resolution of `A`, with the hypotheses of the stage lemmas checked, and that no file
here supplied that instantiation. The decisive hypothesis is that the kernel of a finite free
presentation is again projective — over `ℤ`, free.

This file supplies it, and the proof is an instance chain rather than new mathematics:

* `ℤⁿ` is a Noetherian module, so a submodule of it is finitely generated;
* a submodule of a torsion-free module is torsion-free;
* over a PID a finitely generated torsion-free module is free
  (`Module.free_of_finite_type_torsion_free'`, the primed form at this pin);
* a free module is projective, so both terms of `0 → K → ℤⁿ → A → 0` are projective — which is what
  `ProjectiveResolution` requires of every degree.

The general case — an arbitrary index set, i.e. "every subgroup of a free abelian group is free" —
is *not* available at this pin and is recorded as an upstream gap in §5b; it is not needed for the
cards, whose stages are finitely generated.

The second half of the file is the `Tor` layer. `twoTermProjectiveResolution` assembles the complex
`0 → K → ℤⁿ → 0`, its augmentation onto `single₀ A` and the quasi-isomorphism into a
`ProjectiveResolution`, and `torOneIsoKernel` identifies `Tor₁(A,B)` with the kernel of the
tensored first differential — the derived-functor computation at a genuine free resolution. On top
of it, `isZero_torOne_of_projective` records that `Tor₁` of a projective module vanishes in every
second argument, which makes `isZero_torOne_of_finite_torsionFree` — the finitely generated case of
the direction "torsion-free implies `Tor₁(A,B) = 0`" — an instance rather than a citation.
-/

open CategoryTheory Limits MonoidalCategory
open scoped ZeroObject

namespace LeanCategories.Homological.TorFreeResolution

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
noncomputable def torOneIsoKernelFinFree (r : ℕ) (f : (Fin r → ℤ) →ₗ[ℤ] A) (hf : Function.Surjective f)
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

end LeanCategories.Homological.TorFreeResolution

