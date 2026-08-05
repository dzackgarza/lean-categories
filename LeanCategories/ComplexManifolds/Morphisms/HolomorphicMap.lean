module

public import LeanCategories.ComplexManifolds.Objects.Domain

@[expose] public section

namespace LeanCategories.ComplexManifolds

/-- A holomorphic map of period domains preserving their distinguished points. -/
structure HolomorphicMap (D E : Domain) where
  map : D.periodVector → E.periodVector
  maps_domain : Set.MapsTo map D.points E.points
  holomorphic : Prop

/-- Composition of holomorphic period-domain maps. -/
def HolomorphicMap.comp {D E F : Domain} (g : HolomorphicMap E F)
    (f : HolomorphicMap D E) : HolomorphicMap D F where
  map := g.map ∘ f.map
  maps_domain := g.maps_domain.comp f.maps_domain
  holomorphic := g.holomorphic ∧ f.holomorphic

end LeanCategories.ComplexManifolds
