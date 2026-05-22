import Mathlib.Algebra.Group.Defs

universe u

instance H {G : Type u} [Group G] (a : G) : Group G := {
  mul := fun x y => x * a * y
  mul_assoc := fun x y z => calc (x * a * y) * a * z
    _ = x * a * (y * a * z) := by simp [mul_assoc]
  one := a⁻¹
  one_mul := fun x => calc (a⁻¹ * a * x)
    _ = x := by simp
  mul_one := fun x => calc (x * a * a⁻¹)
    _ = x := by simp
  inv := fun x => a⁻¹ * x⁻¹ * a⁻¹
  inv_mul_cancel := fun x => calc (a⁻¹ * x⁻¹ * a⁻¹ * a * x)
    _ = a⁻¹ := by simp
  div := fun x y => x * y⁻¹ * a⁻¹
  div_eq_mul_inv := fun x y => calc x * y⁻¹ * a⁻¹
    _ = x * a * a⁻¹ * y⁻¹ * a⁻¹ := by simp
    _ = x * a * (a⁻¹ * y⁻¹ * a⁻¹) := by simp [mul_assoc]
}
