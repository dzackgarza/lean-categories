---
title: "root-generated does not imply integral: counterexample at W strictly containing R"
---

**The statement is false (found 2026-08-08).** The catalogue plan had this row in its implications table: `root-generated ⟹ integral`. The proof in the cell was: "`b(x,x) = 2 ∈ R` on a generating family forces `𝔰(b) ≤ R`". That proof assumes a root norm. Roots have no fixed norm. The statement fails on `BilinMod(R, W)` when `W` is larger than `R`.

**Counterexample.** Let `R = ℤ`, `W = ℚ`, `L = ℤ`, and `b(x,y) = xy/3`.

- Take `α = 1`. Then `b(α,α) = 1/3`, which is regular.
- The reflection `s_α` is `−id`. It is an isometry of `L`. So `α` is a root.
- Therefore `⟨Rt(L)⟩ = L`, and `L` is root-generated.
- But `𝔰(b) = (1/3)`, which is not in `ℤ`. So `L` is not integral.

Every lattice of rank one is root-generated, because `−id` is always an isometry. This is enough to break any implication from root generation to a condition on values.

**Where the statement is still true.** On `Lattices(R) = BilinMod(R, R)`, the form `b` has values in `R`. Integrality is then automatic. The implication is true but empty.

**Why this was easy to miss.** The plan states its property atoms for a general `W`. Readers check them at `W = R`. At `W = R` the statement looks correct.

**Why this is in memory and not in the plan.** A plan lists work to do. It does not list statements that are false. The row was deleted. Without this record, a later pass adds the implication again, because the `b(x,x) = 2` proof looks obvious to a reader who assumes ADE roots.

**The correct definition.** `Rt(L) = { α ∈ L : s_α ∈ O(L) }`. A root is a vector whose reflection is an isometry. Norm has no part in it.

Related: a term of art belongs to its own field not to the nearest abstraction.
