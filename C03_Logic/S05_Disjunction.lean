import MIL.Common
import Mathlib.Data.Real.Basic
import Paperproof

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rw [le_abs]
  left
  rfl

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rw [le_abs]
  right
  rfl


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le, neg_add]
  constructor
  apply add_le_add
  exact neg_abs_le x
  exact neg_abs_le y
  apply add_le_add
  exact le_abs_self x
  exact le_abs_self y


theorem lt_abs (x y : ℝ) : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h
  intro a
  cases a
  next h₀ =>
    cases le_or_gt 0 y
    next h₁ =>
      rw [abs_of_nonneg h₁]
      assumption
    next h₁ =>
      calc
        x < y := by assumption
        _ < |y| := by
          apply lt_trans
          apply h₁
          exact abs_pos_of_neg h₁
  next h₀ =>
    cases le_or_gt 0 y
    next h₁ =>
      calc
        x < -y := by assumption
        _ ≤  |y| := neg_le_abs_self y
    next h₁ =>
      calc
        x < -y := by assumption
        _ ≤  |y| := neg_le_abs_self y



theorem abs_lt (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := _root_.abs_lt

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, p⟩
  have h₀ : x ^ 2 + y ^ 2 ≥ 0 := by
    rw [← add_zero 0]
    apply add_le_add (pow_two_nonneg x) (pow_two_nonneg y)
  cases p
  next h =>
    rw [h]
    exact h₀
  next h =>
    rw [h]
    apply le_trans
    change 0 ≤ 1
    linarith
    nth_rw 1 [← zero_add 1]
    apply add_le_add
    assumption
    rfl



example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
