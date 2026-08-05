module

public import LeanCategories.Schemes.Pair.Objects.LogPair

@[expose] public section

namespace LeanCategories.Schemes.Pair

open AlgebraicGeometry

/-- A log resolution of a pair, with its exceptional divisors and discrepancy comparison. -/
structure LogResolution (P : LogPair) where
  resolved : LogPair
  morphism : resolved.X ⟶ P.X
  exceptionalDivisors : Type
  smooth : Prop
  simpleNormalCrossings : Prop

/-- A dlt contraction extracts or contracts precisely the prescribed divisors. -/
structure DltContraction (source target : LogPair) where
  morphism : source.X ⟶ target.X
  exceptionalDivisors : Type
  source_dlt : HasSingularity source .dlt
  target_lc : HasSingularity target .lc
  contracts_exactly_exceptional : Prop

end LeanCategories.Schemes.Pair
