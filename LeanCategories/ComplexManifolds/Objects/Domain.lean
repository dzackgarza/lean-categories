module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace LeanCategories.ComplexManifolds

/-- A type-IV period domain represented by isotropic positive projective period vectors. -/
structure Domain where
  periodVector : Type
  conjugate : periodVector → periodVector
  pairing : periodVector → periodVector → ℂ
  points : Set periodVector
  isotropic : ∀ ω ∈ points, pairing ω ω = 0
  positive : ∀ ω ∈ points, 0 < (pairing ω (conjugate ω)).re
  symmetryGroup : Type
  maximalCompact : Type
  symmetricSpaceModel : Type
  quotientModel : symmetricSpaceModel ≃ symmetryGroup × maximalCompact

end LeanCategories.ComplexManifolds
