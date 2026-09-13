/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Spectrification

/-!
# Suspension of spectra

Weibel, *An Introduction to Homological Algebra* (1994), Example 10.9.9,
§10.9, pp. 407--416 (FC05-C10-U109).

For a spectrum `E`, suspend its levels to obtain the prespectrum with level
`S(E_n)`, then spectrify.  The resulting spectrum is Weibel's suspension
`SE`.  The natural weak equivalence `Ω⁻¹E → SE` is a result about this
construction and is not asserted in the definition layer.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- A realization of the levelwise suspended prespectrum associated to a
spectrum `E`.

The structure maps are the ones induced from the spectrum structure of `E`;
the theorem that this construction compares weakly to delooping is separate.

Source: Weibel, Example 10.9.9 (FC05-C10-U109). -/
structure SpectrumSuspensionPrespectrumRealization (E : Spectrum.{u}) where
  /-- The prespectrum obtained by suspending each level of `E`. -/
  prespectrum : Prespectrum.{u}
  /-- Its `n`th level is the reduced suspension `S(E_n)`. -/
  levelIso : ∀ n : ℕ, prespectrum.space n ≅ suspensionObj (E.space n)

/-- A realization of Weibel's suspension spectrum `SE`: spectrify the
levelwise suspended prespectrum. -/
structure SpectrumSuspensionRealization (E : Spectrum.{u}) where
  /-- The levelwise suspended prespectrum. -/
  levelwise : SpectrumSuspensionPrespectrumRealization E
  /-- Its spectrification. -/
  spectrification : SpectrificationRealization levelwise.prespectrum

/-- Weibel's suspension spectrum `SE` attached to a chosen realization.

Source: Weibel, Example 10.9.9 (FC05-C10-U109). -/
def suspensionSpectrum (E : Spectrum.{u})
    (S : SpectrumSuspensionRealization E) : Spectrum.{u} :=
  S.spectrification.spectrum

end LeanCategories.Homological
