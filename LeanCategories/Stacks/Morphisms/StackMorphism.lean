module

public import LeanCategories.Stacks.Objects.KSBAStack

@[expose] public section

namespace LeanCategories.Stacks

/-- A representable 1-morphism between KSBA stacks. -/
structure StackMorphism (S T : KSBAStack) where
  map : S.stack → T.stack
  mapObjects : ∀ x, S.objects x → T.objects (map x)
  representable : Function.Injective map

end LeanCategories.Stacks
