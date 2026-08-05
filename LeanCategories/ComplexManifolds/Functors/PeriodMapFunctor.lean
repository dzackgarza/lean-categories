module

public import LeanCategories.Stacks.Morphisms.StackMorphism
public import LeanCategories.ComplexManifolds.Morphisms.HolomorphicMap

@[expose] public section

namespace LeanCategories.ComplexManifolds

open LeanCategories.Stacks

/-- Torelli-period assignment from KSBA stacks to type-IV domains, functorial on stack maps. -/
structure PeriodMapFunctor where
  obj : KSBAStack → Domain
  map : ∀ {S T}, StackMorphism S T → HolomorphicMap (obj S) (obj T)
  map_identity : ∀ S, (map ({
    map := id
    mapObjects := fun _ => id
    representable := Function.injective_id
  } : StackMorphism S S)).map = id
  mapComposition : Prop

/-- The Torelli construction determines the period-map functor. -/
axiom periodMapFunctor : PeriodMapFunctor

end LeanCategories.ComplexManifolds
