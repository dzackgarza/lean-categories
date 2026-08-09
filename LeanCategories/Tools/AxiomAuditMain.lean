/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Tools.AxiomAudit

@[expose] public section

/-- Lake entry point for the kernel-axiom audit. -/
def main : IO UInt32 :=
  LeanCategories.Tools.AxiomAudit.main
