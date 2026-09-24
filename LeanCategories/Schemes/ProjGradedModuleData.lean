/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
# Graded-module data on `Proj`

Definition-level realization of Hartshorne FC06-C02-U128.

For a graded ring `A = ⨁ Aₙ` and a `ℤ`-graded `A`-module `M = ⨁ M_d`,
the associated module sheaf on `Proj A` is locally made from fractions `m/s`
whose numerator and denominator have the same degree.  Mathlib already has the
corresponding homogeneous-localization construction for the structure sheaf,
but not the module-valued analogue.

This file records exactly the source data before the sheaf-law boundary:

* the predicate that a family of additive subgroups is a `ℤ`-grading compatible
  with the `ℕ`-grading on the ring;
* the degree-zero homogeneous part of the localized module at a projective
  point;
* raw section families, their restriction, and the local same-degree-fraction
  predicate;
* the degree-zero localization on a standard basic open `D₊(f)`.

No sheaf axiom, localization comparison, stalk identification, quasicoherence,
or coherence result is proved here.  Those are the result layer of Hartshorne
Proposition 5.11 (FC06-C02-U129).
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

namespace LeanCategories.Schemes

universe u

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (𝓜 : ℤ → AddSubgroup M)

/-- Predicate that `𝓜` is a `ℤ`-grading of the `A`-module `M`, compatible
with the `ℕ`-grading `𝒜` of `A`.

This is a predicate rather than a structure with proof-valued constructor
fields: Sweep III records the grading condition without asking a constructor to
prove it. -/
def IsZGradedModuleData : Prop :=
  DirectSum.IsInternal 𝓜 ∧
    ∀ (n : ℕ) (d : ℤ) (a : A) (m : M),
      a ∈ 𝒜 n → m ∈ 𝓜 d → a • m ∈ 𝓜 ((n : ℤ) + d)

/-- The degree-zero homogeneous part of the localization of `M` at a point of
`Proj 𝒜`: fractions `m/s` with `m` and homogeneous `s` of the same degree. -/
def projGradedModuleStalkData (x : ProjectiveSpectrum 𝒜) :
    Set (LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl M) :=
  {z | ∃ (n : ℕ) (m : M) (s : A),
    m ∈ 𝓜 (n : ℤ) ∧ s ∈ 𝒜 n ∧
      ∃ hs : s ∉ x.asHomogeneousIdeal,
        z = LocalizedModule.mk m ⟨s, hs⟩}

/-- A raw module-valued section family on an open subset of the projective
spectrum, before imposing the local same-degree-fraction condition. -/
def projGradedModuleSectionFamilyData
    (U : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)) :=
  ∀ x : U, LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M

/-- Restriction of a raw section family to a smaller open. -/
def projGradedModuleSectionFamilyRestrictData
    {U V : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)} (hVU : V ≤ U)
    (t : projGradedModuleSectionFamilyData (M := M) 𝒜 U) :
    projGradedModuleSectionFamilyData (M := M) 𝒜 V :=
  fun y => t ⟨y.1, hVU y.2⟩

/-- A raw section family is represented by one homogeneous fraction on `U`
when all its values are the same fraction `m/s`, with numerator and denominator
of one common degree and with `s` nonvanishing throughout `U`. -/
def IsProjGradedModuleFractionData
    {U : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)}
    (t : projGradedModuleSectionFamilyData (M := M) 𝒜 U) : Prop :=
  ∃ (n : ℕ) (m : M) (s : A),
    m ∈ 𝓜 (n : ℤ) ∧ s ∈ 𝒜 n ∧
      ∀ x : U, ∃ hs : s ∉ x.1.asHomogeneousIdeal,
        t x = LocalizedModule.mk m ⟨s, hs⟩

/-- Hartshorne's local-fraction condition for sections of the associated
graded-module sheaf. -/
def IsLocallyProjGradedModuleFractionData
    {U : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)}
    (t : projGradedModuleSectionFamilyData (M := M) 𝒜 U) : Prop :=
  ∀ x : U,
    ∃ (V : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜))
      (_hx : x.1 ∈ V) (hVU : V ≤ U),
      IsProjGradedModuleFractionData 𝒜 𝓜
        (projGradedModuleSectionFamilyRestrictData 𝒜 hVU t)

/-- The source-defined carrier of sections on `U`: raw stalk-valued functions
that are locally represented by same-degree homogeneous fractions.

This is deliberately a `Set` of candidate sections.  Promoting these carriers
and the raw restrictions to an actual sheaf of modules requires closure,
restriction, and sheaf-law proofs, which are result-layer obligations. -/
def projGradedModuleSectionData
    (U : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)) :
    Set (projGradedModuleSectionFamilyData (M := M) 𝒜 U) :=
  {t | IsLocallyProjGradedModuleFractionData 𝒜 𝓜 t}

/-- The degree-zero homogeneous localization `M_(f)` on the standard open
`D₊(f)`: in the localization away from `f`, retain fractions `m/f^k` whose
numerator has degree `k * deg(f)`. -/
def projGradedModuleBasicOpenDegreeZeroData
    {n : ℕ} (f : A) (_hf : f ∈ 𝒜 n) : Set (LocalizedModule.Away f M) :=
  {z | ∃ (k : ℕ) (m : M),
    m ∈ 𝓜 (((k * n : ℕ) : ℤ)) ∧
      z = LocalizedModule.mk m
        ⟨f ^ k, (Submonoid.powers f).pow_mem (Submonoid.mem_powers f) k⟩}

end LeanCategories.Schemes
