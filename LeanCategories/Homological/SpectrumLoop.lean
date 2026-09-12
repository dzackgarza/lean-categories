/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Spectrum

/-!
# Looping and delooping spectra

Weibel, *An Introduction to Homological Algebra*, Construction 10.9.2, p. 408
(FC05-C10-U101).

The loop spectrum has `(ΩE)ₙ = Ω(Eₙ)`.  Delooping shifts levels,
`(Ω⁻¹E)ₙ = Eₙ₊₁`.  The structure isomorphisms of `E` identify `E` naturally with either
loop/deloop composite, which is the precise categorical content of Weibel's statement that looping
and delooping are inverse automorphisms of the category of spectra.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- The based loop space of a based space. -/
abbrev basedLoopObj (X : BasedTop.{u}) : BasedTop.{u} :=
  Under.mk (TopCat.ofHom ⟨fun _ : PUnit => Path.refl X.point, continuous_const⟩)

/-- Postcomposition of a based loop by a based map. -/
def basedLoopMapFn {X Y : BasedTop.{u}} (f : X ⟶ Y)
    (p : Path X.point X.point) : Path Y.point Y.point where
  toFun t := f.right (p t)
  source' := by rw [p.source, BasedTop.map_point]
  target' := by rw [p.target, BasedTop.map_point]
  continuous_toFun := f.right.hom.continuous_toFun.comp p.continuous_toFun

/-- The induced map on based loop spaces is continuous. -/
theorem continuous_basedLoopMapFn {X Y : BasedTop.{u}} (f : X ⟶ Y) :
    Continuous (basedLoopMapFn f) := by
  apply Path.continuous_uncurry_iff.mp
  exact f.right.hom.continuous_toFun.comp continuous_eval

/-- The based map `ΩX ⟶ ΩY` induced by a based map `X ⟶ Y`. -/
def basedLoopMap {X Y : BasedTop.{u}} (f : X ⟶ Y) : basedLoopObj X ⟶ basedLoopObj Y :=
  Under.homMk
    (TopCat.ofHom ⟨basedLoopMapFn f, continuous_basedLoopMapFn f⟩)
    (by
      apply TopCat.ext
      intro z
      rcases z with ⟨⟩
      apply Path.ext
      funext t
      simp [basedLoopMapFn, BasedTop.map_point])

@[simp]
theorem basedLoopMap_id (X : BasedTop.{u}) : basedLoopMap (𝟙 X) = 𝟙 (basedLoopObj X) := by
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro p
  apply Path.ext
  funext t
  rfl

@[simp]
theorem basedLoopMap_comp {X Y Z : BasedTop.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    basedLoopMap (f ≫ g) = basedLoopMap f ≫ basedLoopMap g := by
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro p
  apply Path.ext
  funext t
  rfl

/-- A based homeomorphism induces a homeomorphism of based loop spaces. -/
def basedLoopHomeomorph {X Y : BasedTop.{u}} (h : X.right ≃ₜ Y.right)
    (hpoint : h X.point = Y.point) :
    Path X.point X.point ≃ₜ Path Y.point Y.point where
  toFun p :=
    { toFun := fun t => h (p t)
      source' := by rw [p.source, hpoint]
      target' := by rw [p.target, hpoint]
      continuous_toFun := h.continuous.comp p.continuous_toFun }
  invFun q :=
    { toFun := fun t => h.symm (q t)
      source' := by
        rw [q.source]
        exact h.injective (by simp [hpoint])
      target' := by
        rw [q.target]
        exact h.injective (by simp [hpoint])
      continuous_toFun := h.symm.continuous.comp q.continuous_toFun }
  left_inv p := by
    apply Path.ext
    funext t
    simp
  right_inv q := by
    apply Path.ext
    funext t
    simp
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact h.continuous.comp continuous_eval
  continuous_invFun := by
    apply Path.continuous_uncurry_iff.mp
    exact h.symm.continuous.comp continuous_eval

/-- The loop spectrum `ΩE`, with `(ΩE)ₙ = Ω(Eₙ)`.

Source: Weibel, Construction 10.9.2 (FC05-C10-U101). -/
abbrev loopSpectrum (E : Spectrum.{u}) : Spectrum.{u} where
  space n := basedLoopObj (E.space n)
  loopHomeomorph n := basedLoopHomeomorph (E.loopHomeomorph n) (E.loopHomeomorph_point n)
  loopHomeomorph_point n := by
    apply Path.ext
    funext t
    exact E.loopHomeomorph_point n

/-- Looping a map of spectra levelwise. -/
def loopSpectrumMap {E F : Spectrum.{u}} (f : E ⟶ F) : loopSpectrum E ⟶ loopSpectrum F where
  app n := basedLoopMap (f.app n)
  comm n p t := by
    change Path (E.space n).point (E.space n).point at p
    apply Path.ext
    funext s
    exact f.comm n (p t) s

/-- Looping is an endofunctor of spectra.

Source: Weibel, Construction 10.9.2 (FC05-C10-U101). -/
def loopSpectrumFunctor : Spectrum.{u} ⥤ Spectrum.{u} where
  obj := loopSpectrum
  map := loopSpectrumMap
  map_id E := by
    apply Spectrum.Hom.ext
    funext n
    exact basedLoopMap_id _
  map_comp f g := by
    apply Spectrum.Hom.ext
    funext n
    exact basedLoopMap_comp _ _

/-- The delooped spectrum `Ω⁻¹E`, obtained by shifting levels upward.

Source: Weibel, Construction 10.9.2 (FC05-C10-U101). -/
abbrev deloopSpectrum (E : Spectrum.{u}) : Spectrum.{u} where
  space n := E.space (n + 1)
  loopHomeomorph n := E.loopHomeomorph (n + 1)
  loopHomeomorph_point n := E.loopHomeomorph_point (n + 1)

/-- Delooping a spectrum map by shifting its components. -/
def deloopSpectrumMap {E F : Spectrum.{u}} (f : E ⟶ F) : deloopSpectrum E ⟶ deloopSpectrum F where
  app n := f.app (n + 1)
  comm n := f.comm (n + 1)

/-- Delooping is an endofunctor of spectra.

Source: Weibel, Construction 10.9.2 (FC05-C10-U101). -/
def deloopSpectrumFunctor : Spectrum.{u} ⥤ Spectrum.{u} where
  obj := deloopSpectrum
  map := deloopSpectrumMap
  map_id E := by
    apply Spectrum.Hom.ext
    funext n
    rfl
  map_comp f g := by
    apply Spectrum.Hom.ext
    funext n
    rfl

/-- The structure homeomorphism of a spectrum, bundled as an isomorphism of based spaces. -/
abbrev spectrumStructureIso (E : Spectrum.{u}) (n : ℕ) :
    E.space n ≅ basedLoopObj (E.space (n + 1)) :=
  Under.isoMk (TopCat.isoOfHomeo (E.loopHomeomorph n)) (by
    apply TopCat.ext
    intro z
    rcases z with ⟨⟩
    exact E.loopHomeomorph_point n)

/-- The structure maps identify a spectrum with its loop-after-deloop composite. -/
def toLoopDeloop (E : Spectrum.{u}) : E ⟶ loopSpectrum (deloopSpectrum E) where
  app n := (spectrumStructureIso E n).hom
  comm n x t := by
    rfl

/-- The inverse identification from the loop-after-deloop composite back to the spectrum. -/
def fromLoopDeloop (E : Spectrum.{u}) : loopSpectrum (deloopSpectrum E) ⟶ E where
  app n := (spectrumStructureIso E n).inv
  comm n p t := by
    change Path (E.space (n + 1)).point (E.space (n + 1)).point at p
    simpa [spectrumStructureIso, basedLoopHomeomorph] using congrArg (fun q => q t)
      ((E.loopHomeomorph n).apply_symm_apply p)

/-- A spectrum is canonically isomorphic to its loop-after-deloop composite. -/
def loopDeloopIso (E : Spectrum.{u}) : E ≅ loopSpectrum (deloopSpectrum E) where
  hom := toLoopDeloop E
  inv := fromLoopDeloop E
  hom_inv_id := by
    apply Spectrum.Hom.ext
    funext n
    exact (spectrumStructureIso E n).hom_inv_id
  inv_hom_id := by
    apply Spectrum.Hom.ext
    funext n
    exact (spectrumStructureIso E n).inv_hom_id

/-- Looping and delooping are inverse up to the canonical natural isomorphism supplied by the
spectrum structure maps.

Source: Weibel, Construction 10.9.2 (FC05-C10-U101). -/
def loopDeloopNatIso : 𝟭 Spectrum.{u} ≅ deloopSpectrumFunctor ⋙ loopSpectrumFunctor :=
  NatIso.ofComponents loopDeloopIso (by
    intro E F f
    apply Spectrum.Hom.ext
    funext n
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    intro x
    apply Path.ext
    funext t
    exact (f.comm n x t).symm)

/-- The same structure maps identify a spectrum with its deloop-after-loop composite. Together
with `loopDeloopNatIso`, this exhibits looping and delooping as inverse automorphisms.

Source: Weibel, Construction 10.9.2 (FC05-C10-U101). -/
def deloopLoopNatIso : 𝟭 Spectrum.{u} ≅ loopSpectrumFunctor ⋙ deloopSpectrumFunctor :=
  NatIso.ofComponents loopDeloopIso (by
    intro E F f
    apply Spectrum.Hom.ext
    funext n
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    intro x
    apply Path.ext
    funext t
    exact (f.comm n x t).symm)

end LeanCategories.Homological
