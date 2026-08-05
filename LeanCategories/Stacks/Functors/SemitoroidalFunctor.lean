module

public import LeanCategories.Stacks.Objects.KSBAStack

@[expose] public section

namespace LeanCategories.Stacks

/-- A semitoroidal compactification together with its recognizable boundary divisors. -/
structure SemitoroidalCompactification (S : KSBAStack) where
  compactified : KSBAStack
  inclusion : S.stack → compactified.stack
  boundaryDivisor : Type
  recognizable : boundaryDivisor → Prop
  proper : compactified.proper

/-- Main Compactification Theorem: Normalized KSBA compactification is semitoroidal. -/
axiom normalized_ksba_is_semitoroidal (S : KSBAStack) :
    SemitoroidalCompactification S

end LeanCategories.Stacks
