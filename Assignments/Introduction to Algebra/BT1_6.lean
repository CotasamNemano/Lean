import Mathlib.Algebra.Group.Defs

universe u

instance {G : Type u} [Group G] (h : ∀ a : G, a * a = 1) : CommGroup G := {
  mul_comm := by
    have h1 : ∀ x : G, x⁻¹ = x := by
      intro x
      calc x⁻¹
        _ = x⁻¹ * x⁻¹ * x := by simp
        _ = 1 * x := by rw [h x⁻¹]
        _ = x := by simp

    intro x y
    calc x * y
      _ = y⁻¹ * y * x * y * x⁻¹ * x := by simp
      _ = y * y * x * y * x * x := by rw [h1 y, h1 x]
      _ = y * ((y * x) * (y * x)) * x := by simp [mul_assoc]
      _ = y * 1 * x := by rw [h (y * x)]
      _ = y * x := by simp
}
