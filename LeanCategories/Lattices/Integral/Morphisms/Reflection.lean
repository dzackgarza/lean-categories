module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- The integral reflection in a root of square `2` or `-2`.

For `(r, r) = 2` this is `x ↦ x - (x, r) r`, and for `(r, r) = -2` it is
`x ↦ x + (x, r) r`; both are the usual `x ↦ x - 2(x, r)/(r, r) · r` with the
denominator cleared. -/
def reflectionMap (L : IntegralLattice) (r : L.carrier)
    (_hr : L.form r r = -2 ∨ L.form r r = 2) : L.carrier →ₗ[ℤ] L.carrier :=
  let f : L.carrier →+ L.carrier :=
    { toFun x := if L.form r r = -2 then x + (L.form x r) • r else x - (L.form x r) • r
      map_zero' := by simp
      map_add' := by
        intro x y
        by_cases h : L.form r r = -2
        · rw [if_pos h, if_pos h, if_pos h, map_add, LinearMap.add_apply, add_zsmul]
          abel
        · rw [if_neg h, if_neg h, if_neg h, map_add, LinearMap.add_apply, add_zsmul]
          abel }
  { toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro c x
      exact map_intCast_smul f ℤ ℤ c x }

theorem reflectionMap_apply_of_neg (L : IntegralLattice) (r : L.carrier)
    (hr : L.form r r = -2 ∨ L.form r r = 2) (h : L.form r r = -2) (x : L.carrier) :
    reflectionMap L r hr x = x + (L.form x r) • r := by
  simp [reflectionMap, h]

theorem reflectionMap_apply_of_pos (L : IntegralLattice) (r : L.carrier)
    (hr : L.form r r = -2 ∨ L.form r r = 2) (h : L.form r r = 2) (x : L.carrier) :
    reflectionMap L r hr x = x - (L.form x r) • r := by
  have h' : L.form r r ≠ -2 := by rw [h]; decide
  simp [reflectionMap, h']

/-- The root reflection preserves the lattice bilinear form. -/
theorem reflectionMap_isometry (L : IntegralLattice) (r : L.carrier)
    (hr : L.form r r = -2 ∨ L.form r r = 2) (x y : L.carrier) :
    L.form (reflectionMap L r hr x) (reflectionMap L r hr y) = L.form x y := by
  have hsymm : ∀ a b : L.carrier, L.form a b = L.form b a := fun a b => L.isSymm.eq a b
  rcases hr with h | h
  · rw [reflectionMap_apply_of_neg L r (Or.inl h) h x,
      reflectionMap_apply_of_neg L r (Or.inl h) h y]
    simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul, h]
    rw [hsymm r y]
    ring
  · rw [reflectionMap_apply_of_pos L r (Or.inr h) h x,
      reflectionMap_apply_of_pos L r (Or.inr h) h y]
    simp only [map_sub, LinearMap.sub_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul, h]
    rw [hsymm r y]
    ring

end LeanCategories.Lattices.Integral
