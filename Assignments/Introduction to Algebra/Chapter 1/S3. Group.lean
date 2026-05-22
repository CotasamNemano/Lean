import Mathlib.Algebra.Group.Defs
import Paperproof

universe u

theorem unique_one {G : Type u} {k : Group G} (e : G)
(h : ∀ a, a * e = a ∧ e * a = a) : (e = 1) := by
  calc e
    _ = e * 1 := by rw [mul_one]
    _ = 1     := by rw [(h 1).2]

theorem unique_inverse {G : Type u} {k : Group G} {x y : G}
(h : x * y = 1 ∧ y * x = 1) : (y = x⁻¹) := by
  calc y
    _ = y * 1         := by rw [mul_one]
    _ = y * (x * x⁻¹) := by rw [mul_inv_cancel]
    _ = (y * x) * x⁻¹ := by rw [mul_assoc]
    _ = 1 * x⁻¹       := by rw [h.2]
    _ = x⁻¹           := by rw [one_mul]

theorem eq_inverse_of_inverse_self {G : Type u} {k : Group G} (x : G) : (x = (x⁻¹)⁻¹) :=
  unique_inverse ⟨inv_mul_cancel x, mul_inv_cancel x⟩
