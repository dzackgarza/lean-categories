/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.HomotopyLifting
public import Mathlib.Topology.Path

/-!
# Based path spaces and homotopy fibers

The pathspace replacement of a map is defined as the subspace of `A × C(I,B)` consisting of a
point `a` together with a path beginning at `f(a)`.  The projection remembers the other endpoint;
its fiber over a chosen basepoint is the homotopy fiber.  This is the literal construction used by
Hatcher in Chapter 4.

The theorem that the endpoint projection is a Hurewicz fibration is deliberately not built into
these definitions.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open scoped unitInterval

universe u v

/-- Paths in `X` beginning at a fixed basepoint, with the subspace topology inherited from the
compact-open topology on continuous maps `I → X`.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 378 (FC07-C04-U088). -/
def BasedPathSpace (X : Type u) [TopologicalSpace X] (x₀ : X) :=
  { γ : C(unitInterval, X) // γ 0 = x₀ }

instance basedPathSpaceTopologicalSpace (X : Type u) [TopologicalSpace X] (x₀ : X) :
    TopologicalSpace (BasedPathSpace X x₀) := by
  unfold BasedPathSpace
  infer_instance

/-- Endpoint evaluation on the based path space. -/
def basedPathEndpoint (X : Type u) [TopologicalSpace X] (x₀ : X) :
    C(BasedPathSpace X x₀, X) where
  toFun γ := γ.1 1
  continuous_toFun := (continuous_eval_const 1).comp continuous_subtype_val

/-- The fiber of endpoint evaluation over the basepoint. -/
def BasedPathLoopFiber (X : Type u) [TopologicalSpace X] (x₀ : X) :=
  { γ : BasedPathSpace X x₀ // basedPathEndpoint X x₀ γ = x₀ }

instance basedPathLoopFiberTopologicalSpace (X : Type u) [TopologicalSpace X] (x₀ : X) :
    TopologicalSpace (BasedPathLoopFiber X x₀) := by
  unfold BasedPathLoopFiber
  infer_instance

/-- The fiber of `PX → X` over the basepoint is canonically the based loop space.

Both sides carry the topology induced from the compact-open topology on `C(I,X)`.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 378 (FC07-C04-U088). -/
def basedPathLoopHomeomorph (X : Type u) [TopologicalSpace X] (x₀ : X) :
    BasedPathLoopFiber X x₀ ≃ₜ Path x₀ x₀ where
  toFun γ :=
    { toContinuousMap := γ.1.1
      source' := γ.1.2
      target' := γ.2 }
  invFun γ := ⟨⟨γ.toContinuousMap, γ.source⟩, γ.target⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    · apply Continuous.subtype_mk
      · exact continuous_induced_dom
      · intro γ
        exact γ.source
    · intro γ
      exact γ.target

/-- The pathspace replacement of `f : A → B`: pairs `(a,γ)` where `γ` begins at `f(a)`.

Source: Hatcher, *Algebraic Topology*, §4.3, pp. 379–380 (FC07-C04-U089–U090). -/
def PathReplacement {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) :=
  { p : A × C(unitInterval, B) // p.2 0 = f p.1 }

instance pathReplacementTopologicalSpace {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) :
    TopologicalSpace (PathReplacement f) := by
  unfold PathReplacement
  infer_instance

/-- Endpoint projection from the pathspace replacement to the target. -/
def pathReplacementProjection {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) :
    C(PathReplacement f, B) where
  toFun p := p.1.2 1
  continuous_toFun :=
    (continuous_eval_const 1).comp (continuous_snd.comp continuous_subtype_val)

/-- The original map includes into its pathspace replacement by the constant path at `f(a)`. -/
def pathReplacementInclusion {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) :
    C(A, PathReplacement f) where
  toFun a := ⟨(a, ContinuousMap.const unitInterval (f a)), rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk (ContinuousMap.continuous_const'.comp f.continuous)

/-- The homotopy fiber of `f : A → B` over `b₀` is the fiber of the pathspace-replacement
projection: pairs `(a,γ)` with `γ` a path from `f(a)` to `b₀`.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 380 (FC07-C04-U090). -/
def HomotopyFiber {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) (b₀ : B) :=
  { p : PathReplacement f // pathReplacementProjection f p = b₀ }

instance homotopyFiberTopologicalSpace {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) (b₀ : B) :
    TopologicalSpace (HomotopyFiber f b₀) := by
  unfold HomotopyFiber
  infer_instance

end LeanCategories.Topology
