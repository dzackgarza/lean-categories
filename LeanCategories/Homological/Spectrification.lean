/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Prespectrum
public import LeanCategories.Homological.SpectrumLoop
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Spectrification of a CW prespectrum

Weibel, *An Introduction to Homological Algebra* (1994), §10.9,
pp. 407--416, 10.9.6 (FC05-C10-U105).

For a CW prespectrum `D`, spectrification is the spectrum `Ω^∞D` whose
`n`th level is the sequential colimit

`colim_i Ω^i D_{n+i}`.

The transition from stage `i` to stage `i+1` is obtained by iterating the
loop functor on the adjoint map `D_{n+i} ⟶ ΩD_{n+i+1}`.  The spectrum
structure is the one induced by shifting the colimit index.  This file
records that source construction directly; existence of the required
colimits and comparison theorems are separate results.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- The loop adjoint of a prespectrum structure map, as a continuous family
of based loops. -/
def prespectrumLoopAdjointFn (D : Prespectrum.{u}) (n : ℕ)
    (x : (D.space n).right) :
    Path (D.space (n + 1)).point (D.space (n + 1)).point where
  toFun t :=
    (D.structureMap n).right
      (Quotient.mk (suspensionSetoid (D.space n)) (t, x))
  source' := by
    have hq :
        Quotient.mk (suspensionSetoid (D.space n)) (0, x) =
          suspensionPoint (D.space n) := by
      apply Quotient.sound
      right
      constructor
      · exact Or.inl rfl
      · exact Or.inl rfl
    rw [hq]
    exact BasedTop.map_point (D.structureMap n)
  target' := by
    have hq :
        Quotient.mk (suspensionSetoid (D.space n)) (1, x) =
          suspensionPoint (D.space n) := by
      apply Quotient.sound
      right
      constructor
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    rw [hq]
    exact BasedTop.map_point (D.structureMap n)
  continuous_toFun :=
    (D.structureMap n).right.hom.continuous_toFun.comp
      (continuous_quotient_mk'.comp
        (Continuous.prodMk continuous_id continuous_const))

/-- The loop-adjoint family of a prespectrum structure map is continuous in
the point of the source space. -/
theorem continuous_prespectrumLoopAdjointFn (D : Prespectrum.{u}) (n : ℕ) :
    Continuous (prespectrumLoopAdjointFn D n) := by
  apply Path.continuous_uncurry_iff.mp
  exact (D.structureMap n).right.hom.continuous_toFun.comp
    (continuous_quotient_mk'.comp
      (Continuous.prodMk continuous_snd continuous_fst))

/-- The structure map of a prespectrum in its adjoint form
`D_n ⟶ ΩD_{n+1}`. -/
def prespectrumLoopAdjoint (D : Prespectrum.{u}) (n : ℕ) :
    D.space n ⟶ basedLoopObj (D.space (n + 1)) :=
  Under.homMk
    (TopCat.ofHom
      ⟨prespectrumLoopAdjointFn D n,
        continuous_prespectrumLoopAdjointFn D n⟩)
    (by
      apply TopCat.ext
      intro z
      rcases z with ⟨⟩
      apply Path.ext
      funext t
      change (D.structureMap n).right
          (Quotient.mk (suspensionSetoid (D.space n))
            (t, (D.space n).point)) =
        (D.space (n + 1)).point
      have hq :
          Quotient.mk (suspensionSetoid (D.space n))
              (t, (D.space n).point) =
            suspensionPoint (D.space n) := by
        apply Quotient.sound
        right
        constructor
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
      rw [hq]
      exact BasedTop.map_point (D.structureMap n))

/-- Iterated based loop space `Ω^i X`. -/
def iteratedBasedLoopObj : ℕ → BasedTop.{u} → BasedTop.{u}
  | 0, X => X
  | i + 1, X => basedLoopObj (iteratedBasedLoopObj i X)

/-- Iteration of the based-loop functor on a based map. -/
def iteratedBasedLoopMap : ∀ (i : ℕ) {X Y : BasedTop.{u}},
    (X ⟶ Y) → (iteratedBasedLoopObj i X ⟶ iteratedBasedLoopObj i Y)
  | 0, _, _, f => f
  | i + 1, _, _, f => basedLoopMap (iteratedBasedLoopMap i f)

/-- Iterating loops commutes with applying one additional loop. -/
lemma iteratedBasedLoopObj_loop (i : ℕ) (X : BasedTop.{u}) :
    iteratedBasedLoopObj i (basedLoopObj X) =
      basedLoopObj (iteratedBasedLoopObj i X) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [iteratedBasedLoopObj]
      rw [ih]

/-- Stage `i` of the sequential system defining the `n`th level of
spectrification: `Ω^i D_{n+i}`. -/
def spectrificationStage (D : Prespectrum.{u}) (n i : ℕ) : BasedTop.{u} :=
  iteratedBasedLoopObj i (D.space (n + i))

/-- The transition
`Ω^i D_{n+i} ⟶ Ω^{i+1} D_{n+i+1}` in Weibel's spectrification sequence. -/
def spectrificationTransition (D : Prespectrum.{u}) (n i : ℕ) :
    spectrificationStage D n i ⟶ spectrificationStage D n (i + 1) := by
  let f := iteratedBasedLoopMap i (prespectrumLoopAdjoint D (n + i))
  have hidx : n + i + 1 = n + (i + 1) := by omega
  have htarget :
      iteratedBasedLoopObj i (basedLoopObj (D.space (n + i + 1))) =
        iteratedBasedLoopObj (i + 1) (D.space (n + (i + 1))) := by
    rw [iteratedBasedLoopObj_loop]
    simp only [iteratedBasedLoopObj]
  exact f ≫ eqToHom htarget

/-- The sequential diagram `i ↦ Ω^i D_{n+i}` whose colimit is level `n` of
the spectrification. -/
def spectrificationStageFunctor (D : Prespectrum.{u}) (n : ℕ) :
    ℕ ⥤ BasedTop.{u} :=
  Functor.ofSequence (spectrificationTransition D n)

/-- The successor stage at level `n` is the based loop of the same stage at
level `n+1`. -/
lemma spectrificationStage_succ_eq_loop (D : Prespectrum.{u}) (n i : ℕ) :
    spectrificationStage D n (i + 1) =
      basedLoopObj (spectrificationStage D (n + 1) i) := by
  unfold spectrificationStage
  simp only [iteratedBasedLoopObj]
  rw [show n + (i + 1) = (n + 1) + i by omega]

/-- A realization of Weibel's spectrification `Ω^∞D`.

The `levelColimit` fields record `(Ω^∞D)_n = colim_i Ω^iD_{n+i}`.  The final
field records that the spectrum structure is induced by shifting the stage
index.

Source: Weibel, 10.9.6, pp. 409--410 (FC05-C10-U105). -/
structure SpectrificationRealization (D : Prespectrum.{u}) where
  /-- The resulting spectrum `Ω^∞D`. -/
  spectrum : Spectrum.{u}
  /-- A chosen colimit cocone for the stage diagram at each spectrum level. -/
  levelColimit : ∀ n : ℕ, Cocone (spectrificationStageFunctor D n)
  /-- The chosen cocone is a colimit. -/
  levelIsColimit : ∀ n : ℕ, IsColimit (levelColimit n)
  /-- Identification of the colimit object with the corresponding spectrum level. -/
  levelIso : ∀ n : ℕ, (levelColimit n).pt ≅ spectrum.space n
  /-- The spectrum structure is induced by shifting the sequential-colimit index. -/
  structure_from_shift : ∀ (n i : ℕ),
    (levelColimit n).ι.app i ≫ (levelIso n).hom ≫
        (spectrumStructureIso spectrum n).hom =
      spectrificationTransition D n i ≫
        eqToHom (spectrificationStage_succ_eq_loop D n i) ≫
        basedLoopMap ((levelColimit (n + 1)).ι.app i ≫
          (levelIso (n + 1)).hom)

/-- The spectrum represented by a spectrification realization. -/
def spectrification (D : Prespectrum.{u})
    (S : SpectrificationRealization D) : Spectrum.{u} :=
  S.spectrum

end LeanCategories.Homological
