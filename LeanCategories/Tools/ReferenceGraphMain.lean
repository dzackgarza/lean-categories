/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Tools.ReferenceGraph

@[expose] public section

/-- Lake entry point. The graph itself is emitted at elaboration time by
`LeanCategories.Tools.ReferenceGraph`, following the pattern of the other audit tools; the
executable exists so the module has a build target. -/
def main : IO UInt32 := return 0
