/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicReductionRealQuotient
public import LeanCategories.Lattices.Valued.CobleQuotientSignature
public import LeanCategories.Lattices.Valued.LatticeCone

/-!
# The hyperbolic lattice `e^⊥/ℤe` at a 0-cusp of `T_Co` (#120)

For a primitive isotropic vector `e` of `cobleLattice` (`T_Co`, #115), the reduction
`M = e^⊥/ℤe` carries the form `T_Co` induces on it (`lineReductionForm`, #122: the value on a
class is the pairing of the representative), and this module packages it as a finite
projective integral lattice (`cobleCuspLattice`) — the hyperbolic lattice at the 0-cusp `e`.

**The signature of `M` is the signature of `T_Co` minus `(1, 1)` (#119, #126)**:
`cobleCuspLattice_sigPos_add` and `cobleCuspLattice_sigNeg_add` state that the positive and
negative indices of `M`, plus one, are those of `cobleFiniteLattice`; the numeric corollaries
give `1` and `8` from the Gram-matrix computation of `T_Co`'s signature
(`cobleFiniteLattice_sigPos`/`sigNeg`, #120's landed decision procedure). The signature of
`M` is never computed from coordinates of `e`: it is the general theorem of #126 — the real
partner of `e_ℝ` exists because `T_Co` is nondegenerate (`coble_isNondegenerate`) and
`e ≠ 0` — applied to `cobleLattice`.

The bridge to the Gram-matrix computation is definitional: the direct real form
`realQuadratic` of #124 is the functor real form `realFormQuadratic` of #36's cone theory
(`realQuadratic (L := L'.obj) = realFormQuadratic L'` by `rfl`, both being
`toQuadraticMap` of the same `baseChange`-and-`rid` pairing), and the real form of the
reduction is the real form of the cusp lattice
(`realQuadratic_cobleCuspLattice`, again `rfl`: the bundled reduction `lineReduction` carries
`lineReductionForm` as its bilinear map).

**The positive cone and `O⁺(M)` of #36 apply to `M`**: `cobleCuspPositiveCone` names the cone
`{x ∈ M ⊗ ℝ : x² > 0}`, `exists_cobleCuspLattice_positive` produces a positive vector from
the signature (Mathlib's `QuadraticForm.exists_finrank_eq_sigPos_and_posDef`, no
coordinates), and `cobleCuspLatticePositiveConeStabilizer` is `O⁺(M)` —
`latticePositiveConeStabilizer` at `M` — with index at most two in `O(M)`
(`cobleCuspLatticePositiveConeStabilizer_index_le_two`). The cone and component theory of
#36 (`positiveCone_eq_upper_union_lower`, `upper_disjoint_lower`, `mem_upper_or_mem_lower`)
applies verbatim at `realFormQuadratic (cobleCuspLattice e he hprim)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv.
  Akad. Nauk SSSR Ser. Mat. 43 (1979), §1: primitive isotropic vectors and the reduction
  `P^⊥/P`.
* R. E. Kottwitz, or D. Allcock, *The Leech lattice as a cross-section of the Coble lattice*:
  the hyperbolic lattice at a 0-cusp of the moduli of marked cubic surfaces.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

attribute [local instance 10000] Submodule.module
attribute [local instance 10000] Submodule.Quotient.module

variable {L : IntegralLatticeCat ℤ}

/-! ## The cusp lattice `M = e^⊥/ℤe` of a primitive isotropic vector of `T_Co` -/

section CuspLattice

/-- The form induced on the reduction is symmetric. -/
theorem lineReduction_isSymmetric (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    (lineReduction (L := L) hb e).IsSymmetric := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y => exact hb (x : L.obj.carrier) (y : L.obj.carrier)

variable [Module.Finite ℤ L.obj.carrier]

/-- **The hyperbolic lattice at a 0-cusp of `T_Co` (#120)**: for a primitive isotropic vector
`e` of `cobleLattice`, the reduction `M = e^⊥/ℤe` with the form `T_Co` induces on it, as a
finite projective integral lattice. Projectivity is the freeness of the reduction at a
primitive line (`moduleFree_isotropicLineQuotient`, #120); finiteness is inherited. -/
noncomputable def cobleCuspLattice (e : ↥cobleLattice.obj.carrier)
    (_he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) :
    FiniteProjectiveLatticeCat ℤ ℤ := by
  haveI : Module.Free ℤ (lineReduction coble_isSymmetric e).carrier :=
    moduleFree_isotropicLineQuotient (L := cobleLattice) e hprim
  exact ⟨⟨lineReduction coble_isSymmetric e,
      ⟨Module.Projective.of_free, lineReduction_isSymmetric coble_isSymmetric e⟩⟩,
    Module.Finite.of_surjective (isotropicLineKernel (L := cobleLattice) e).mkQ
      (Submodule.mkQ_surjective _)⟩

/-- The cusp lattice's underlying formed module is the reduction of #122. -/
theorem cobleCuspLattice_obj (e : ↥cobleLattice.obj.carrier)
    (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) :
    (cobleCuspLattice e he hprim).obj.obj = lineReduction coble_isSymmetric e :=
  rfl

/-- The real form of the cusp lattice is the real form of the reduction (#122): the bundled
reduction carries `lineReductionForm` as its bilinear map, and `realQuadratic` is the
`baseChange`-and-`rid` form of that map. -/
theorem realQuadratic_cobleCuspLattice (e : ↥cobleLattice.obj.carrier)
    (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) :
    realQuadratic (L := (cobleCuspLattice e he hprim).obj) =
      lineReductionRealQuadratic (L := cobleLattice) coble_isSymmetric e :=
  rfl

end CuspLattice

/-! ## The signature of the cusp lattice -/

section Signature

variable (e : ↥cobleLattice.obj.carrier)

/-- **The positive index of the cusp lattice, plus one, is that of `T_Co`**: the signature of
`M = e^⊥/ℤe` is the signature of `T_Co` minus one, by the general theorem of #126 applied to
`cobleLattice` (nondegenerate, `e ≠ 0`), never from coordinates of `e`. -/
theorem cobleCuspLattice_sigPos_add (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) (hne : e ≠ 0) :
    (integralSignature (cobleCuspLattice e he hprim)).1 + 1 =
      (integralSignature cobleFiniteLattice).1 := by
  have h1 := sigPos_lineReductionRealQuadratic_of_nondegenerate (L := cobleLattice)
    coble_isSymmetric coble_isNondegenerate he hne
  have h2 : sigPos (realQuadratic (L := cobleLattice)) =
      (integralSignature cobleFiniteLattice).1 :=
    realFormQuadratic_sigPos cobleFiniteLattice
  have h3 : sigPos (realQuadratic (L := (cobleCuspLattice e he hprim).obj)) =
      sigPos (lineReductionRealQuadratic (L := cobleLattice) coble_isSymmetric e) :=
    congrArg sigPos (realQuadratic_cobleCuspLattice e he hprim)
  have h4 : (integralSignature (cobleCuspLattice e he hprim)).1 =
      sigPos (realQuadratic (L := (cobleCuspLattice e he hprim).obj)) :=
    (realFormQuadratic_sigPos (cobleCuspLattice e he hprim)).symm
  calc (integralSignature (cobleCuspLattice e he hprim)).1 + 1
      = sigPos (realQuadratic (L := (cobleCuspLattice e he hprim).obj)) + 1 := by rw [h4]
    _ = sigPos (lineReductionRealQuadratic (L := cobleLattice) coble_isSymmetric e) + 1 := by
        rw [h3]
    _ = sigPos (realQuadratic (L := cobleLattice)) := h1
    _ = (integralSignature cobleFiniteLattice).1 := h2

/-- **The negative index of the cusp lattice, plus one, is that of `T_Co`.** -/
theorem cobleCuspLattice_sigNeg_add (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) (hne : e ≠ 0) :
    (integralSignature (cobleCuspLattice e he hprim)).2.1 + 1 =
      (integralSignature cobleFiniteLattice).2.1 := by
  have h1 := sigNeg_lineReductionRealQuadratic_of_nondegenerate (L := cobleLattice)
    coble_isSymmetric coble_isNondegenerate he hne
  have h2 : sigNeg (realQuadratic (L := cobleLattice)) =
      (integralSignature cobleFiniteLattice).2.1 :=
    realFormQuadratic_sigNeg cobleFiniteLattice
  have h3 : sigNeg (realQuadratic (L := (cobleCuspLattice e he hprim).obj)) =
      sigNeg (lineReductionRealQuadratic (L := cobleLattice) coble_isSymmetric e) :=
    congrArg sigNeg (realQuadratic_cobleCuspLattice e he hprim)
  have h4 : (integralSignature (cobleCuspLattice e he hprim)).2.1 =
      sigNeg (realQuadratic (L := (cobleCuspLattice e he hprim).obj)) :=
    (realFormQuadratic_sigNeg (cobleCuspLattice e he hprim)).symm
  calc (integralSignature (cobleCuspLattice e he hprim)).2.1 + 1
      = sigNeg (realQuadratic (L := (cobleCuspLattice e he hprim).obj)) + 1 := by rw [h4]
    _ = sigNeg (lineReductionRealQuadratic (L := cobleLattice) coble_isSymmetric e) + 1 := by
        rw [h3]
    _ = sigNeg (realQuadratic (L := cobleLattice)) := h1
    _ = (integralSignature cobleFiniteLattice).2.1 := h2

/-- **The positive index of the cusp lattice is `1`** — the signature of `T_Co` (computed
from its Gram matrix, `cobleFiniteLattice_sigPos`) minus one. -/
theorem cobleCuspLattice_sigPos (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) (hne : e ≠ 0) :
    (integralSignature (cobleCuspLattice e he hprim)).1 = 1 := by
  have h := cobleCuspLattice_sigPos_add e he hprim hne
  have h2 := cobleFiniteLattice_sigPos
  omega

/-- **The negative index of the cusp lattice is `8`** — the signature of `T_Co` (computed
from its Gram matrix, `cobleFiniteLattice_sigNeg`) minus one. -/
theorem cobleCuspLattice_sigNeg (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) (hne : e ≠ 0) :
    (integralSignature (cobleCuspLattice e he hprim)).2.1 = 8 := by
  have h := cobleCuspLattice_sigNeg_add e he hprim hne
  have h2 := cobleFiniteLattice_sigNeg
  omega

end Signature

/-! ## The positive cone and `O⁺` of the cusp lattice -/

section Cone

/-- **The positive cone of the cusp lattice**: `{x ∈ M ⊗ ℝ : x² > 0}` in the real form of
`M = e^⊥/ℤe`. The two components and the action of `O(M)` on them are #36's
`positiveCone`-theory at `realFormQuadratic (cobleCuspLattice e he hprim)`. -/
noncomputable def cobleCuspPositiveCone (e : ↥cobleLattice.obj.carrier)
    (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) :
    Set (realForm (cobleCuspLattice e he hprim)).obj.carrier :=
  positiveCone (realFormQuadratic (cobleCuspLattice e he hprim))

/-- **A positive vector of the cusp lattice's real form exists**, produced from the
signature by Mathlib's `QuadraticForm.exists_finrank_eq_sigPos_and_posDef` — a positive
definite line of the real form, never a coordinate computation. -/
theorem exists_cobleCuspLattice_positive (e : ↥cobleLattice.obj.carrier)
    (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) (hne : e ≠ 0) :
    ∃ t : (realForm (cobleCuspLattice e he hprim)).obj.carrier,
      0 < realFormQuadratic (cobleCuspLattice e he hprim) t := by
  have hpos : sigPos (realFormQuadratic (cobleCuspLattice e he hprim)) = 1 := by
    rw [realFormQuadratic_sigPos]
    exact cobleCuspLattice_sigPos e he hprim hne
  obtain ⟨V, hVrank, hVpd⟩ :=
    exists_finrank_eq_sigPos_and_posDef (realFormQuadratic (cobleCuspLattice e he hprim))
  rw [hpos] at hVrank
  obtain ⟨v, hvV, hv0⟩ := V.exists_mem_ne_zero_of_ne_bot (by
    intro hbot
    rw [hbot] at hVrank
    simp at hVrank)
  refine ⟨v, ?_⟩
  have hv := hVpd ⟨v, hvV⟩ (fun h => hv0 (congrArg Subtype.val h))
  rwa [QuadraticMap.restrict_apply] at hv

/-- **`O⁺(M)` of the cusp lattice (#36 applied to `M`)**: the isometries of
`M = e^⊥/ℤe` whose base change to `M ⊗ ℝ` preserves each sheet of the positive cone —
`latticePositiveConeStabilizer` at the cusp lattice. -/
noncomputable def cobleCuspLatticePositiveConeStabilizer (e : ↥cobleLattice.obj.carrier)
    (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) (hne : e ≠ 0)
    (t : (realForm (cobleCuspLattice e he hprim)).obj.carrier)
    (ht : 0 < realFormQuadratic (cobleCuspLattice e he hprim) t) :
    Subgroup (OrthogonalGroup (cobleCuspLattice e he hprim).obj) :=
  latticePositiveConeStabilizer (cobleCuspLattice e he hprim)
    (cobleCuspLattice_sigPos e he hprim hne) t ht

/-- **`O⁺(M)` has index at most two in `O(M)`**, for the cusp lattice as for every
Lorentzian lattice (#36). -/
theorem cobleCuspLatticePositiveConeStabilizer_index_le_two
    (e : ↥cobleLattice.obj.carrier) (he : cobleLattice.obj.pairing e e = 0)
    (hprim : IsPrimitiveSubmodule (isotropicLine (L := cobleLattice) e)) (hne : e ≠ 0)
    {t : (realForm (cobleCuspLattice e he hprim)).obj.carrier}
    (ht : 0 < realFormQuadratic (cobleCuspLattice e he hprim) t) :
    (cobleCuspLatticePositiveConeStabilizer e he hprim hne t ht).index ≤ 2 :=
  latticePositiveConeStabilizer_index_le_two (cobleCuspLattice e he hprim)
    (cobleCuspLattice_sigPos e he hprim hne) ht

end Cone

end LeanCategories.Lattices.Valued
