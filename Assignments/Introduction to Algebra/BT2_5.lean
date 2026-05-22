import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing


universe u

open Ring

namespace BooleanRing

theorem eq_neg_self {R : Type u} [Ring R] (h : ∀ x : R, x * x = x)
  : ∀ x : R, x = -x := by
  intro x
  have h1 := h (x + x)

  have h2 : (x + x) * (x + x) = x + x + x + x := by
    calc (x + x) * (x + x)
    _ = x * x + x * x + x * x + x * x := by noncomm_ring
    _ = x + x + x + x := by rw [h x]

  have h3 : x + x + x + x = x + x := h2.symm.trans h1

  have h4 : x + x = 0 := by
    calc x + x
    _ = x + x + x + x + (-x) + (-x) := by abel
    _ = x + x + (-x) + (-x) := by rw [h3]
    _ = 0 := by abel

  calc x
    _ = x + x + (-x) := by simp
    _ = 0 + (-x) := by rw [h4]
    _ = -x := by simp


theorem mul_comm_of_mul_idempotent {R : Type u} [Ring R] (h : ∀ x : R, x * x = x)
  : ∀ x y : R, x * y = y * x := by
  intro x y
  have h1 : (x + y) * (x + y) = x + y := h (x + y)

  have h2 : (x + y) * (x + y) = x + x * y + y * x + y := by
    calc (x + y) * (x + y)
    _ = x * (x + y) + y * (x + y) := by noncomm_ring
    _ = x * x + x * y + y * x + y * y := by noncomm_ring
    _ = x + x * y + y * x + y := by rw [h x, h y]

  have h3 : x + x * y + y * x + y = x + y := h2.symm.trans h1

  have h4 : x * y + y * x = 0 := by
    calc x * y + y * x
    _ = x + (-x) + x * y + y * x + y + (-y) := by abel
    _ = (-x) + x + x * y + y * x + y + (-y) := by abel
    _ = (-x) + (x + x * y + y * x + y) + (-y) := by abel
    _ = (-x) + x + y + (-y) := by simp [h3]
    _ = 0 := by abel

  calc x * y
    _ = x * y + 0 := by simp
    _ = x * y + (x * y + y * x) := by rw [← h4]
    _ = x * y + x * y + y * x := by simp [add_assoc]
    _ = x * y + (- (x * y)) + y * x := by nth_rw 2 [eq_neg_self h (x * y)]
    _ = y * x := by simp


end BooleanRing
