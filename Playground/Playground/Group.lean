import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.FiniteGroup
import Mathlib.Algebra.Group.Power

-- A clean formulation:
theorem group_of_order_15_commutative
    (G : Type*)
    [Group G] [Fintype G] (hcard : Fintype.card G = 15)
    (h : ∀ a b : G, a ^ 7 * b ^ 8 = b ^ 8 * a ^ 7) :
    ∀ a b : G, a * b = b * a :=
