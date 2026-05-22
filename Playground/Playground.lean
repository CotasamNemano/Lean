import Playground.Basic
import Paperproof

theorem tri {a b : Prop} : a -> (b -> a) := by
  intro h₁ h₂
  exact h₁
