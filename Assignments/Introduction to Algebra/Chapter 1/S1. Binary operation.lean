import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group

universe u

@[simp]
def is_left_neutral {M : Type u} {k : Mul M} (e : M) : Prop := ∀a, e * a = a

@[simp]
def is_right_neutral {M : Type u} {k : Mul M} (e : M) : Prop := ∀a, a * e = a

@[simp]
def is_neutral {M : Type u} {k : Mul M} (e : M) : Prop :=
  @is_left_neutral.{u} M k e ∧ @is_right_neutral.{u} M k e

theorem unique_neutral {M : Type u} {k : Mul M} (e₀ e₁ : M)
(h₀ : @is_neutral M k e₀) (h₁ : @is_neutral M k e₁) : (e₀ = e₁) := by
  simp at h₀ h₁
  calc e₀
    _ = e₀ * e₁ := Eq.symm (h₁.2 e₀)
    _ = e₁      := (h₀.1 e₁)

@[simp]
def is_inverse_of {M : Type u} {k : Mul M} {e : M} {_ : @is_neutral M k e} (x y : M) : Prop :=
  x * y = e ∧ y * x = e

theorem unique_inverse {M : Type u} {k : Semigroup M} {x y z e : M} {h : @is_neutral M k.toMul e}
(hy : @is_inverse_of M k.toMul e h y x) (hz : @is_inverse_of M k.toMul e h z x) : (y = z) := by
  simp at h hy hz
  calc y
    _ = y * e       := by rw [h.2]
    _ = y * (x * z) := by rw [hz.2]
    _ = (y * x) * z := by rw [mul_assoc]
    _ = e * z       := by rw [hy.1]
    _ = z           := by rw [h.1]
