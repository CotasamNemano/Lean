import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Paperproof

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  simp

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  rintro fssubv x xs
  apply fssubv ⟨x, xs, rfl⟩
  rintro ssubfiv y ⟨x, xs, rfl⟩
  apply ssubfiv at xs
  simp at xs
  exact xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h x xs
  --apply h
  apply h (mem_image_of_mem f xs)

  rintro h y ⟨x, xs, rfl⟩
  exact h xs


#check mem_image_of_mem

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := ⟨
  fun h _ xs ↦ h (mem_image_of_mem f xs),
  fun h _ ⟨_, xs, xeq⟩ ↦ Eq.subst xeq (h xs)
⟩


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x ⟨x₀, x₀s, x₀eq⟩
  have h₁ : x₀ = x := h x₀eq
  rw [← h₁]
  exact x₀s

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s :=
  fun _ ⟨_, x₀s, x₀eq⟩ ↦ Eq.subst (h x₀eq) x₀s

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xs, rfl⟩
  exact xs

example : f '' (f ⁻¹' u) ⊆ u :=
  fun _ ⟨_, xs, xeq⟩ ↦ Eq.subst xeq xs

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y h₀
  --simp
  --rw [Surjective] at h
  rcases h y with ⟨x, rfl⟩
  use x, h₀ --exact ⟨x, h₀, rfl⟩

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) :=
  fun y yu ↦ have ⟨x, xeq⟩ := h y;
  ⟨x, Set.mem_preimage.mpr (Eq.subst (Eq.symm xeq) yu), xeq⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, rfl⟩
  exact ⟨x, h xs, rfl⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
  fun _ ⟨x, xs, xeq⟩ ↦ ⟨x, h xs, xeq⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x h₀
  exact h h₀

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
  fun _ h₀ ↦ Set.mem_preimage.mpr (h (Set.mem_preimage.mp h₀))

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  simp

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  constructor

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  exact ⟨x, xs, rfl⟩
  exact ⟨x, xt, rfl⟩

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  fun _ ⟨x, ⟨xs, xt⟩, xeq⟩ ↦ ⟨⟨x, xs, xeq⟩, ⟨x, xt, xeq⟩⟩


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨⟨x, xs, xeq⟩, ⟨x₀, x₀t, x₀eq⟩⟩
  have x₀eqx : x₀ = x := h (Eq.trans x₀eq (Eq.symm xeq))
  have xt : x ∈ t :=  Eq.subst x₀eqx x₀t
  use x, ⟨xs, xt⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
  fun _ ⟨⟨x, xs, xeq⟩, ⟨_, x₀t, x₀eq⟩⟩ ↦ ⟨
    x,
    ⟨xs, Eq.subst (h (Eq.trans x₀eq (Eq.symm xeq))) x₀t⟩,
    xeq
  ⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨⟨x, xs, xeq⟩, ynft⟩
  refine ⟨x, ⟨xs, ?_⟩, xeq⟩
  contrapose! ynft
  rw [← xeq]
  exact ⟨x, ynft, rfl⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
  fun _ ⟨⟨x, xs, xeq⟩, ynft⟩ ↦
    have xnt : x ∉ t :=
      fun xt ↦ have yft :=
        Eq.subst xeq ⟨x, xt, rfl⟩;
        ynft yft;
    ⟨x, ⟨xs, xnt⟩, xeq⟩


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨xfs, xnft⟩
  simp
  constructor
  exact xfs
  contrapose! xnft
  exact xnft

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun _ ⟨xfs, xnft⟩ ↦ ⟨
    xfs,
    fun xft ↦ xnft xft
  ⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  rintro ⟨⟨x, xs, rfl⟩, yv⟩
  simp
  use x

  rintro ⟨x, ⟨xs, xfiv⟩, rfl⟩
  constructor
  use x
  apply xfiv

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
  Subset.antisymm (
    fun _ ⟨⟨x, xs, xeq⟩, yv⟩ ↦
      ⟨x, ⟨⟨xs, Set.mem_preimage.mpr (Eq.subst (Eq.symm xeq) yv)⟩, xeq⟩⟩
  )
  (
    fun _ ⟨x, ⟨xs, xfiv⟩, xeq⟩ ↦ ⟨⟨x, xs, xeq⟩, Eq.subst xeq xfiv⟩
  )

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  repeat constructor
  use xs
  rfl
  apply fxu

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u :=
  fun _ ⟨x, ⟨xs, fxu⟩, xeq⟩ ↦ ⟨⟨x, xs, xeq⟩, Eq.subst xeq fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, fxu⟩
  constructor
  exact ⟨x, xs, rfl⟩
  exact fxu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
  fun x ⟨xs, fxu⟩ ↦ ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  left
  exact ⟨x, xs, rfl⟩
  right
  exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  rintro ⟨x, ⟨⟨i, xAi⟩, rfl⟩⟩
  use i, x

  rintro ⟨i, x, xAi, rfl⟩
  use x
  constructor
  use i
  rfl

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  simp
  intro i x h
  simp
  use x
  simp at h
  constructor
  apply h i
  rfl

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rw [Injective] at injf
  rcases h i with ⟨x, xAi, rfl⟩
  use x
  constructor
  intro i₀
  rcases h i₀ with ⟨x₀, ⟨x₀Ai, x₀eq⟩⟩
  have x₀eqx := injf x₀eq
  rw [← x₀eqx]
  exact x₀Ai
  rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos e
  calc
    x = (√x) ^ 2 := Eq.symm (Real.sq_sqrt xpos)
    _ = (√y) ^ 2 := by rw [e]
    _ = y := Real.sq_sqrt ypos

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos e
  dsimp at e
  calc
    x = √(x ^ 2) := Eq.symm $ Real.sqrt_sq xpos
    _ = √(y ^ 2) := by rw [e]
    _ = y := Real.sqrt_sq ypos

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext s; constructor
  intro ⟨x, xpos, xeq⟩
  rw [← xeq]
  apply Real.sqrt_nonneg

  intro h
  simp
  use (s ^ 2)
  constructor
  exact sq_nonneg s
  exact sqrt_sq h


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  simp
  constructor
  intro ⟨x, xeq⟩
  rw [← xeq]
  exact sq_nonneg x

  intro ypos
  use √y
  apply Real.sq_sqrt ypos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

#print LeftInverse

example : Injective f ↔ LeftInverse (inverse f) f := by
  clear h P
  rw [Injective]
  rw [LeftInverse]
  constructor
  intro injf x
  apply injf
  apply inverse_spec
  use x

  intro leftInvf
  intro a₁ a₂
  intro feq
  calc
    a₁ = inverse f (f a₁) := Eq.symm $ leftInvf a₁
    _  = inverse f (f a₂) := by rw [feq]
    _  = a₂               := leftInvf a₂

example : Injective f ↔ LeftInverse (inverse f) f := ⟨
  fun injf x ↦ injf $ inverse_spec _ ⟨x, rfl⟩,
  fun leftInvf a₁ a₂ feq ↦ Eq.trans (Eq.symm $ leftInvf a₁) $
    Eq.trans (congr_arg _ feq) $ leftInvf a₂
⟩


example : Surjective f ↔ RightInverse (inverse f) f := by
  clear h P
  rw [Surjective]
  rw [RightInverse, LeftInverse]
  constructor
  intro surjf y
  apply inverse_spec
  apply surjf y

  intro rightInvf y
  use (inverse f y)
  apply rightInvf

example : Surjective f ↔ RightInverse (inverse f) f := ⟨
  fun surjf y ↦ inverse_spec y (surjf y),
  fun rightInvf y ↦ ⟨inverse f y, rightInvf y⟩
⟩

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    intro h₄
    rw [← h] at h₄
    contradiction
  contradiction

-- COMMENTS: TODO: improve this
end
