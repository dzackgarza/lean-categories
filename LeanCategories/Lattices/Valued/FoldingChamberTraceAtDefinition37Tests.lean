/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberTraceAtDefinition37

/-!
# Probe: Lemma 3.8 at Definition 3.7's set

The trace identity of `chamberOf_folded_trace` is stated at `foldedRootImage`, which the source's
Definition 3.7 (**printed p. 12**) filters down to the folds that are roots of `M^σ`. The probes
decide that the two sets agree once nothing is dropped, and that the trace identity transfers.

Both are stated with the "no fold is dropped" hypothesis carried explicitly: it is AEGS Lemma 3.4
forward's content, not a definitional triviality.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- Once every folded wall is a root of `M^σ`, the image and Definition 3.7's set have the same
ambient vectors. -/
example {L : FiniteProjectiveLatticeCat ℤ ℤ} (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (R : Set L.obj.obj.carrier)
    (hroot : ∀ v ∈ R,
      (⟨foldedVector g v, foldedVector_mem_fixed g hg v⟩ : involutionFixedSubmodule g) ∈
        foldedRootSet g R) :
    Set.range (fun v : {v // v ∈ foldedRootSet g R} =>
        ((v.1 : involutionFixedSubmodule g) : L.obj.obj.carrier)) = foldedRootImage g R :=
  foldedRootImage_eq_range g hg R hroot

end LeanCategories.Lattices.Valued
