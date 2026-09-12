/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DiscreteProfiniteModule
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Continuous cochains of a profinite group

Weibel, *An Introduction to Homological Algebra*, Definition 6.11.12, pp. 206--215
(FC05-C06-U147).

For a profinite group `G` and a discrete `G`-module `A`, the degree-`n` continuous cochains are the
continuous maps `G^n → A`.  Since the target carries the discrete topology, these are exactly
Mathlib's locally constant maps.  The differential below is Weibel's usual inhomogeneous
cochain differential, restricted to locally constant maps.  The identity `d² = 0` is theorem-level
and is not part of this Definitions unit.
-/

@[expose] public section

open scoped BigOperators

namespace LeanCategories.Homological

universe u

variable (G : ProfiniteGrp.{u}) (A : Rep.{u} ℤ G)

/-- The degree-`n` continuous cochains `C^n(G,A)` of a profinite group with coefficients in a
discrete module.  With the coefficient module given the discrete topology, continuous maps are
exactly locally constant maps.

Source: Weibel, Definition 6.11.12, pp. 206--215 (FC05-C06-U147). -/
abbrev ContinuousProfiniteCochains (n : ℕ) := LocallyConstant (Fin n → G) A

private lemma contractNth_continuous (n : ℕ) (j : Fin (n + 1)) :
    Continuous (fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g) := by
  rw [continuous_pi_iff]
  intro k
  rcases lt_trichotomy (k : ℕ) (j : ℕ) with h | h | h
  · simp only [Fin.contractNth_apply_of_lt j (· * ·) _ k h]
    fun_prop
  · simp only [Fin.contractNth_apply_of_eq j (· * ·) _ k h]
    fun_prop
  · simp only [Fin.contractNth_apply_of_gt j (· * ·) _ k h]
    fun_prop

/-- The usual inhomogeneous differential on continuous cochains.

For `f : C^n(G,A)`, this is
`(df)(g₀,...,gₙ) = g₀ f(g₁,...,gₙ) + Σ_j (-1)^(j+1) f(...,g_j g_{j+1},...)`.
The discrete-module hypothesis ensures the action term is continuous.

Source: Weibel, Definition 6.11.12, pp. 206--215 (FC05-C06-U147). -/
noncomputable def continuousProfiniteCochainDifferential
    (hA : IsDiscreteProfiniteModule G A) (n : ℕ) :
    ContinuousProfiniteCochains G A n →+ ContinuousProfiniteCochains G A (n + 1) where
  toFun f :=
    { toFun := fun g =>
        A.ρ (g 0) (f fun i => g i.succ) +
          ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) g)
      isLocallyConstant := by
        letI : TopologicalSpace A := ⊥
        letI : DiscreteTopology A := discreteTopology_bot A
        letI : SMul G A := ⟨fun g a => A.ρ g a⟩
        letI : MulAction G A :=
          { one_smul := fun a => by
              change A.ρ 1 a = a
              rw [map_one]
              rfl
            mul_smul := fun g h a => by
              change A.ρ (g * h) a = A.ρ g (A.ρ h a)
              rw [map_mul]
              rfl }
        have hsmul : ContinuousSMul G A :=
          (continuousSMul_iff_stabilizer_isOpen).2 (fun a => by
            convert hA a using 1
            ext g
            simp only [Set.mem_setOf_eq]
            rfl)
        exact (IsLocallyConstant.iff_continuous _).2 <| by
          apply Continuous.add
          · change Continuous (fun g : Fin (n + 1) → G => (g 0) • f (fun i => g i.succ))
            have htail : Continuous (fun g : Fin (n + 1) → G => fun i : Fin n => g i.succ) :=
              continuous_pi fun i => continuous_apply i.succ
            have hf : Continuous (fun g : Fin (n + 1) → G => f (fun i => g i.succ)) :=
              f.isLocallyConstant.continuous.comp htail
            exact hsmul.continuous_smul.comp ((continuous_apply 0).prodMk hf)
          · exact continuous_finsetSum Finset.univ (fun j _ => by
              have hf : Continuous (fun g : Fin (n + 1) → G =>
                  f (Fin.contractNth j (· * ·) g)) :=
                (f.isLocallyConstant.comp_continuous (contractNth_continuous G n j)).continuous
              have hc : Continuous (fun _ : Fin (n + 1) → G =>
                  (-1 : ℤ) ^ ((j : ℕ) + 1)) := continuous_const
              exact hc.smul hf) }
  map_zero' := by
    ext g
    simp
  map_add' f f' := by
    ext g
    simp [Finset.sum_add_distrib, add_add_add_comm]

end LeanCategories.Homological
