/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.WittVector.Defs

/-!
# Truncated Witt affine-scheme data

Definition-level realization of Serre, *Local Fields*, Chapter II,
`FC10-C02-U051`.

Serre observes that the universal integral Witt polynomials give each truncated
Witt functor a finite affine ring-scheme presentation over `Spec ℤ`.  Sweep III
records only the geometric carrier and the polynomial structural maps.  The
facts that the displayed pair space is the fibre product of two copies of the
carrier, that these maps satisfy the ring-object laws, that the carrier is of
finite type, and that its `A`-points recover the truncated Witt ring are
result/comparison statements and are not bundled here.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

namespace LeanCategories.AlgebraicGeometry

/-- The base scheme `Spec ℤ` for Serre's truncated Witt ring schemes. -/
abbrev truncatedWittBase : _root_.AlgebraicGeometry.Scheme :=
  _root_.AlgebraicGeometry.Spec (CommRingCat.of ℤ)

/-- The finite affine-space carrier underlying the length-`n` truncated Witt
scheme. -/
abbrev truncatedWittAffineCarrier (n : ℕ) : _root_.AlgebraicGeometry.Scheme :=
  𝔸(Fin n; truncatedWittBase)

/-- Coordinate affine space for an ordered pair of length-`n` Witt vectors. -/
abbrev truncatedWittPairSpace (n : ℕ) : _root_.AlgebraicGeometry.Scheme :=
  𝔸(Fin 2 × Fin n; truncatedWittBase)

/-- Extend the finite coordinate family on `k` copies of the length-`n` carrier
to the infinite variable family used by the universal Witt polynomials.

Variables outside the first `n` coordinates are sent to zero; the relevant
Witt polynomial in target coordinate `i < n` only uses coordinates at most
`i`, so no truncation theorem is needed to define the map. -/
def truncatedWittSourceCoord (k n : ℕ) (a : Fin k × ℕ) :
    Γ(𝔸(Fin k × Fin n; truncatedWittBase), ⊤) :=
  if h : a.2 < n then
    _root_.AlgebraicGeometry.AffineSpace.coord truncatedWittBase (a.1, ⟨a.2, h⟩)
  else
    0

/-- Evaluate a universal integral Witt polynomial on the finite affine source
coordinates. -/
def evalTruncatedWittPolynomial {k n : ℕ}
    (φ : MvPolynomial (Fin k × ℕ) ℤ) :
    Γ(𝔸(Fin k × Fin n; truncatedWittBase), ⊤) :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (truncatedWittSourceCoord k n) φ

/-- The affine-scheme morphism whose target coordinates are supplied by a
family of universal integral polynomials. -/
def truncatedWittPolynomialMap {k : ℕ} (n : ℕ)
    (φ : ℕ → MvPolynomial (Fin k × ℕ) ℤ) :
    𝔸(Fin k × Fin n; truncatedWittBase) ⟶ truncatedWittAffineCarrier n :=
  _root_.AlgebraicGeometry.AffineSpace.homOfVector
    (𝔸(Fin k × Fin n; truncatedWittBase) ↘ truncatedWittBase)
    (fun i => evalTruncatedWittPolynomial (n := n) (φ i.1))

/-- Evaluate a universal Witt constant polynomial on `Spec ℤ`. -/
def evalTruncatedWittConstant
    (φ : MvPolynomial (Fin 0 × ℕ) ℤ) : Γ(truncatedWittBase, ⊤) :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun _ => 0) φ

/-- A constant section of the truncated Witt affine carrier specified by
universal Witt constant polynomials. -/
def truncatedWittConstantMap (n : ℕ)
    (φ : ℕ → MvPolynomial (Fin 0 × ℕ) ℤ) :
    truncatedWittBase ⟶ truncatedWittAffineCarrier n :=
  _root_.AlgebraicGeometry.AffineSpace.homOfVector (𝟙 truncatedWittBase)
    (fun i => evalTruncatedWittConstant (φ i.1))

/-- Evaluate a unary universal Witt polynomial on the length-`n` carrier. -/
def evalTruncatedWittUnaryPolynomial {n : ℕ}
    (φ : MvPolynomial (Fin 1 × ℕ) ℤ) :
    Γ(truncatedWittAffineCarrier n, ⊤) :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun a => if h : a.2 < n then
      _root_.AlgebraicGeometry.AffineSpace.coord truncatedWittBase ⟨a.2, h⟩ else 0) φ

/-- The unary affine-scheme morphism specified by universal Witt polynomials. -/
def truncatedWittUnaryPolynomialMap (n : ℕ)
    (φ : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ) :
    truncatedWittAffineCarrier n ⟶ truncatedWittAffineCarrier n :=
  _root_.AlgebraicGeometry.AffineSpace.homOfVector
    (truncatedWittAffineCarrier n ↘ truncatedWittBase)
    (fun i => evalTruncatedWittUnaryPolynomial (n := n) (φ i.1))

/-- The zero section supplied by the Witt zero polynomials. -/
def truncatedWittZeroMap (p n : ℕ) [Fact p.Prime] :
    truncatedWittBase ⟶ truncatedWittAffineCarrier n :=
  truncatedWittConstantMap n (WittVector.wittZero p)

/-- The unit section supplied by the Witt one polynomials. -/
def truncatedWittOneMap (p n : ℕ) [Fact p.Prime] :
    truncatedWittBase ⟶ truncatedWittAffineCarrier n :=
  truncatedWittConstantMap n (WittVector.wittOne p)

/-- The additive-inverse map supplied by the Witt negation polynomials. -/
def truncatedWittNegMap (p n : ℕ) [Fact p.Prime] :
    truncatedWittAffineCarrier n ⟶ truncatedWittAffineCarrier n :=
  truncatedWittUnaryPolynomialMap n (WittVector.wittNeg p)

/-- The binary addition map on Witt coordinates.  Its source is the explicit
affine coordinate model for two truncated Witt vectors. -/
def truncatedWittAddMap (p n : ℕ) [Fact p.Prime] :
    truncatedWittPairSpace n ⟶ truncatedWittAffineCarrier n :=
  truncatedWittPolynomialMap n (WittVector.wittAdd p)

/-- The binary multiplication map on Witt coordinates.  Its source is the
explicit affine coordinate model for two truncated Witt vectors. -/
def truncatedWittMulMap (p n : ℕ) [Fact p.Prime] :
    truncatedWittPairSpace n ⟶ truncatedWittAffineCarrier n :=
  truncatedWittPolynomialMap n (WittVector.wittMul p)

/-- Raw geometric data underlying Serre's truncated Witt ring scheme.

This structure deliberately carries no ring-object laws and no representability
or finite-type witnesses. -/
structure TruncatedWittAffineData (p n : ℕ) [Fact p.Prime] where
  carrier : _root_.AlgebraicGeometry.Scheme := truncatedWittAffineCarrier n
  pairSpace : _root_.AlgebraicGeometry.Scheme := truncatedWittPairSpace n
  zero : truncatedWittBase ⟶ carrier
  one : truncatedWittBase ⟶ carrier
  neg : carrier ⟶ carrier
  add : pairSpace ⟶ carrier
  mul : pairSpace ⟶ carrier

/-- The raw affine data obtained from the universal Witt structure
polynomials. -/
def truncatedWittAffineData (p n : ℕ) [Fact p.Prime] :
    TruncatedWittAffineData p n where
  carrier := truncatedWittAffineCarrier n
  pairSpace := truncatedWittPairSpace n
  zero := truncatedWittZeroMap p n
  one := truncatedWittOneMap p n
  neg := truncatedWittNegMap p n
  add := truncatedWittAddMap p n
  mul := truncatedWittMulMap p n

end LeanCategories.AlgebraicGeometry
