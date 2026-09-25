/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CWPrespectrum
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Homotopy-group direct limits of a CW prespectrum

Definition-level realization of Hatcher FC07-C04-U138.

For an integer `i`, Hatcher defines

`π_i(K) = colim_n π_{i+n}(K_n)`

after passing to a cofinal tail on which the displayed ordinary homotopy
groups are defined in degree at least two.  The transition is suspension
followed by the structure map.

Sweep III records a canonical cofinal tail, the transition on homotopy-class
carriers through the loop adjoint and an exact cube-flattening graph, and the
actual sequential colimit in `Type`.  It does not prove that the selected
loop-shift map is well defined with respect to homotopy, that the transitions
are group homomorphisms, or that the colimit carrier inherits the source
abelian-group structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- Exact representative graph identifying an `m`-cube of based loops with
an `(m+1)`-cube.

The first `m` coordinates are fed to the outer generalized loop and the last
coordinate evaluates the resulting ordinary based loop. -/
def IsLoopHomotopyShiftRepresentativeData
    {Y : Type u} [TopologicalSpace Y] (y : Y) (m : ℕ)
    (p : GenLoop (Fin m) (Path y y) (Path.refl y))
    (q : GenLoop (Fin (m + 1)) Y y) : Prop :=
  ∀ t,
    q t =
      p (fun j : Fin m => t (Fin.castAdd 1 j))
        (t (Fin.last m))

/-- The flattened `(m+1)`-loop selected from the exact cube graph. -/
def loopHomotopyShiftRepresentativeData
    {Y : Type u} [TopologicalSpace Y] (y : Y) (m : ℕ)
    (p : GenLoop (Fin m) (Path y y) (Path.refl y)) :
    GenLoop (Fin (m + 1)) Y y :=
  Classical.epsilon
    (IsLoopHomotopyShiftRepresentativeData y m p)

/-- Exact quotient-level specification of the loop/dimension shift
`π_m(ΩY) → π_{m+1}(Y)`. -/
def IsLoopHomotopyGroupShiftData
    {Y : Type u} [TopologicalSpace Y] (y : Y) (m : ℕ)
    (shift :
      HomotopyGroup.Pi m (Path y y) (Path.refl y) →
        HomotopyGroup.Pi (m + 1) Y y) : Prop :=
  ∀ p : GenLoop (Fin m) (Path y y) (Path.refl y),
    shift (Quotient.mk' p) =
      Quotient.mk' (loopHomotopyShiftRepresentativeData y m p)

/-- Candidate loop/dimension shift selected from the exact representative
formula.  Homotopy descent is a Sweep-IV obligation. -/
def loopHomotopyGroupShiftData
    {Y : Type u} [TopologicalSpace Y] (y : Y) (m : ℕ) :
    HomotopyGroup.Pi m (Path y y) (Path.refl y) →
      HomotopyGroup.Pi (m + 1) Y y :=
  Classical.epsilon (IsLoopHomotopyGroupShiftData y m)

/-- Hatcher's stage transition
`π_m(K_n) → π_{m+1}(K_{n+1})`, expressed using the loop adjoint of the
prespectrum structure map followed by the selected loop/dimension shift. -/
def prespectrumHomotopyTransitionData
    (D : Prespectrum.{u}) (n m : ℕ) :
    HomotopyGroup.Pi m (D.space n).right (D.space n).point →
      HomotopyGroup.Pi (m + 1)
        (D.space (n + 1)).right (D.space (n + 1)).point :=
  fun x =>
    loopHomotopyGroupShiftData (D.space (n + 1)).point m
      (basedHomotopyGroupMap
        (prespectrumLoopAdjoint D n) (Fin m) x)

/-- First level of a canonical cofinal tail for Hatcher's integer degree
`i`.  At this level the ordinary homotopy degree is at least two. -/
def prespectrumHomotopyTailStart (i : ℤ) : ℕ :=
  Int.toNat (2 - i)

/-- Ordinary homotopy degree at the first level of the chosen cofinal tail. -/
def prespectrumHomotopyTailDegree (i : ℤ) : ℕ :=
  Int.toNat (i + prespectrumHomotopyTailStart i)

/-- Stage `k` of the direct system defining `π_i(K)`. -/
abbrev prespectrumHomotopyStageData
    (K : CWPrespectrum.{u}) (i : ℤ) (k : ℕ) : Type u :=
  HomotopyGroup.Pi (prespectrumHomotopyTailDegree i + k)
    (K.space (prespectrumHomotopyTailStart i + k)).right
    (K.space (prespectrumHomotopyTailStart i + k)).point

/-- Successor map in the chosen cofinal tail of Hatcher's homotopy-group
system. -/
def prespectrumHomotopyStageTransitionData
    (K : CWPrespectrum.{u}) (i : ℤ) (k : ℕ) :
    prespectrumHomotopyStageData K i k →
      prespectrumHomotopyStageData K i (k + 1) :=
  fun x => by
    let y :=
      prespectrumHomotopyTransitionData K.toPrespectrum
        (prespectrumHomotopyTailStart i + k)
        (prespectrumHomotopyTailDegree i + k) x
    have hs :
        prespectrumHomotopyTailStart i + k + 1 =
          prespectrumHomotopyTailStart i + (k + 1) := by
      omega
    have hd :
        prespectrumHomotopyTailDegree i + k + 1 =
          prespectrumHomotopyTailDegree i + (k + 1) := by
      omega
    rw [hs, hd] at y
    exact y

/-- Sequential diagram of the ordinary homotopy-group carriers in the chosen
cofinal tail. -/
def prespectrumHomotopyStageFunctor
    (K : CWPrespectrum.{u}) (i : ℤ) : ℕ ⥤ Type u :=
  Functor.ofSequence
    (X := fun k => prespectrumHomotopyStageData K i k)
    (fun k => TypeCat.ofHom (prespectrumHomotopyStageTransitionData K i k))

/-- Underlying direct-limit carrier of Hatcher's `π_i(K)`. -/
noncomputable abbrev PrespectrumHomotopyGroupData
    (K : CWPrespectrum.{u}) (i : ℤ) : Type u :=
  colimit (prespectrumHomotopyStageFunctor K i)

/-- Canonical map from stage `k` into the homotopy-group direct-limit
carrier. -/
noncomputable def prespectrumHomotopyStageClassData
    (K : CWPrespectrum.{u}) (i : ℤ) (k : ℕ) :
    prespectrumHomotopyStageData K i k →
      PrespectrumHomotopyGroupData K i :=
  fun x => (colimit.ι (prespectrumHomotopyStageFunctor K i) k) x

end LeanCategories.Homological
