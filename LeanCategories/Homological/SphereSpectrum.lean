/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Spectrification

/-!
# Sphere spectra

Weibel, *An Introduction to Homological Algebra* (1994), Example 10.9.3,
p. 408 (FC05-C10-U102).

The standard sphere prespectrum starts with the based two-point space `S⁰`
and defines `Sⁿ⁺¹` to be the reduced suspension of `Sⁿ`.  In this model the
prespectrum structure map `ΣSⁿ ⟶ Sⁿ⁺¹` is literally the identity.  Applying
the raw spectrification construction from FC05-C10-U105 therefore gives the
canonical level spaces

`colim_i Ω^i S^(n+p+i)`

for nonnegative shifts.  Negative shifts are represented by iterated based
loops of the stabilized zero-sphere levels.  Upgrading these raw level data to
bundled spectra requires the spectrification structure-homeomorphism result and
belongs to Sweep IV.

The mapped `plby/lean-proofs` implementation was used only as prior-art
evidence for the spherical transition construction; its files carry no
repository-level license grant, so no source code is copied here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- The based two-point space used as the suspension model of `S⁰`.

Source: Weibel, Example 10.9.3 (FC05-C10-U102). -/
def sphereZero : BasedTop.{u} :=
  let X : TopCat.{u} := TopCat.of (ULift.{u} (Fin 2))
  Under.mk
    (show TopCat.of PUnit.{u + 1} ⟶ X from
      TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit) (ULift.up (0 : Fin 2))))

/-- The suspension model of the based `n`-sphere, recursively defined by
`Sⁿ⁺¹ = ΣSⁿ`.

Source: Weibel, Example 10.9.3 (FC05-C10-U102). -/
def suspensionSphere : ℕ → BasedTop.{u}
  | 0 => sphereZero
  | n + 1 => suspensionObj (suspensionSphere n)

/-- The standard spherical prespectrum.  Because `Sⁿ⁺¹` is definitionally
`ΣSⁿ` in this model, every structure map is the identity.

Source: Weibel, Example 10.9.3 (FC05-C10-U102). -/
def spherePrespectrum : Prespectrum.{u} where
  space := suspensionSphere
  structureMap := fun _ => 𝟙 _

/-- The stabilized zero-sphere level `p`, i.e.
`colim_i Ω^i S^(p+i)`.

Source: Weibel, Example 10.9.3 (FC05-C10-U102), using Construction 10.9.6
(FC05-C10-U105). -/
def sphereZeroSpectrumLevel (p : ℕ) : BasedTop.{u} :=
  spectrificationLevel spherePrespectrum p

/-- Raw level spaces of the integer-indexed sphere spectra.

For `n ≥ 0`, level `p` is the `n`-fold delooping shift of the stabilized
zero-sphere level.  For `n = -(k+1)`, level `p` is the `(k+1)`-fold based loop
of the stabilized zero-sphere level.  The comparison with the tail formula
`colim_i Ω^i S^(n+p+i)` for negative `n` is result-layer content.

Source: Weibel, Example 10.9.3 (FC05-C10-U102). -/
def sphereSpectrumLevel (n : ℤ) (p : ℕ) : BasedTop.{u} :=
  match n with
  | Int.ofNat k => sphereZeroSpectrumLevel (k + p)
  | Int.negSucc k => iteratedBasedLoopObj (k + 1) (sphereZeroSpectrumLevel p)

/-- `Q^∞S^∞`, Weibel's name for level zero of the stabilized zero-sphere.

Source: Weibel, Example 10.9.3 (FC05-C10-U102). -/
abbrev qInfinitySInfinity : BasedTop.{u} := sphereSpectrumLevel 0 0

end LeanCategories.Homological
