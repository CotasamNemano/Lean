import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Defs
import Init.Data.Nat.Dvd
import Mathlib.Tactic.NormNum


theorem pow_two_eq_one_orderOf.{u} {G : Type u} [Group G]
  (a : G) (h : a ^ 2 = 1) : (orderOf a = 1 ∨ orderOf a = 2) := by
  have order_dvd_two := orderOf_dvd_iff_pow_eq_one.mpr h
  have order_le_two : orderOf a ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) order_dvd_two
  clear order_dvd_two
  have a_is_of_fin_order : IsOfFinOrder a := by
    have q : ∃ (n : ℕ), 0 < n ∧ a ^ n = 1 := by
      use 2
      constructor
      exact Nat.zero_lt_two
      exact h
    exact isOfFinOrder_iff_pow_eq_one.mpr q
  have zero_lt_order : 0 < orderOf a := IsOfFinOrder.orderOf_pos a_is_of_fin_order
  clear a_is_of_fin_order
  have one_le_order : 1 ≤ orderOf a := Nat.succ_le_of_lt zero_lt_order
  clear zero_lt_order
  by_contra h1
  push_neg at h1
  have one_lt_order : 1 < orderOf a := Ne.lt_of_le h1.left.symm one_le_order
  clear one_le_order
  have two_le_order : 2 ≤ orderOf a := Nat.succ_le_of_lt one_lt_order
  clear one_lt_order
  have order_eq_two : orderOf a = 2 := le_antisymm order_le_two two_le_order
  clear order_le_two two_le_order
  exact h1.right order_eq_two


theorem unique_order_two_element_mul_comm.{u} {G : Type u} [Group G]
  (a : G) (hA : orderOf a = 2) (hB : ∀ b : G, orderOf b = 2 → a = b)
  : (∀ x : G, a * x = x * a) := by
  intro x
  have key : (x * a * x⁻¹) ^ 2 = 1 := calc (x * a * x⁻¹) ^ 2
    _ = x * a * a * x⁻¹ := by simp [pow_two, mul_assoc]
    _ = x * (a ^ 2) * x⁻¹ := by simp [←pow_two, mul_assoc]
    _ = x * (a ^ (orderOf a)) * x⁻¹ := by rw [← hA]
    _ = x * 1 * x⁻¹ := by rw [pow_orderOf_eq_one]
    _ = 1 := by simp

  apply pow_two_eq_one_orderOf at key

  cases key with
  | inl h1 =>
    rewrite [orderOf_eq_one_iff] at h1
    have hx : a = 1 := by calc
      a = x⁻¹ * x * a * x⁻¹ * x := by simp
      _ = x⁻¹ * (x * a * x⁻¹) * x := by simp [mul_assoc]
      _ = x⁻¹ * 1 * x := by rw [h1]
      _ = 1 := by simp
    calc a * x
      _ = 1 * x := by rw [hx]
      _ = x * 1 := by simp
      _ = x * a := by rw [← hx]

  | inr h2 =>
    apply hB at h2
    calc a * x
      _ = x * a * x⁻¹ * x := by nth_rw 1 [h2]
      _ = x * a := by simp
