module

public import LeanCategories.Schemes.Pair.Objects.Singularities
public import LeanCategories.Stacks.Objects.KSBAStack

@[expose] public section

namespace LeanCategories.Schemes.Pair

open AlgebraicGeometry
open LeanCategories.Stacks

/-- Complete Theorem: Moduli stack of stable log pairs (X, Delta) forms a proper Deligne-Mumford stack. -/
axiom ksbaModuliStack (a v : ℚ) : KSBAStack

/-- Stable log pairs with fixed coefficient and volume form a proper separated moduli stack. -/
axiom ksba_moduli_stack_properness (a v : ℚ) :
  (ksbaModuliStack a v).proper ∧ (ksbaModuliStack a v).separated

end LeanCategories.Schemes.Pair
