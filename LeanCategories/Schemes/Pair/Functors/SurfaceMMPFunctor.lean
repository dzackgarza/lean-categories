module

public import LeanCategories.Schemes.Pair.Morphisms.DltContraction

@[expose] public section

namespace LeanCategories.Schemes.Pair

/-- An MMP output records a minimal model and the contraction producing it. -/
structure SurfaceMMPOutput (P : LogPair) where
  minimalModel : LogPair
  contraction : DltContraction P minimalModel
  canonical_nef : Prop

/-- The surface MMP assigns a canonical output to each log pair. -/
axiom surfaceMMPFunctor (P : LogPair) : SurfaceMMPOutput P

end LeanCategories.Schemes.Pair
