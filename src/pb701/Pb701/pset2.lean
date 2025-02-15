import Mathlib

namespace Pset2

namespace P2
open Set

variable
  (A B C D : Set ℕ)
  (ha : A = {1, 2, 3})
  (hb : B = {4, 5, 6})
  (hc : C = {7})
  (hd : D = ∅)

-- task: fill in the sorries

example : A ∩ B = sorry := by sorry
example : B ∩ C = sorry := by sorry
example : A ∪ B = sorry := by sorry
example : A ∩ (B ∪ C) = sorry := by sorry

section solution

example : A ∩ B = {} := by
  ext y
  constructor
  · --
    rw [inter_def, ha, hb]
    simp
    intro hx
    obtain (h|h|h) := hx
    repeat subst y <;> norm_num
  · --
    intro h
    simp at *

example : B ∩ C = {} := by
  ext y
  constructor
  · --
    simp [inter_def, hb, hc]
    intro hx
    obtain (h|h|h) := hx
    repeat subst y <;> norm_num
  · --
    intro h
    simp at *

example : A ∪ B = {1,2,3,4,5,6} := by
  ext y
  simp [ha, hb]

  constructor; repeat {
    intro hx
    obtain h|h|h|h|h|h := hx;
    all_goals rw [h]; subst h; norm_num
  }

example : A ∩ (B ∪ C) = {} := by
  ext y
  constructor
  · simp at *
    intro hy₁
    refine ⟨by aesop, by aesop⟩ -- todo
  · simp at *

end solution

end P2


namespace P20
open Function

-- one-to-one is injective, onto is surjective.

def f (x : α) : α := sorry
def g (x : α) : α := sorry

example : Injective f ∧ ¬Surjective f := by sorry
example : ¬Injective f ∧ Surjective f := by sorry

end P20


namespace P22
open Function

variable
  (A B C : Type)
  (f : A → B)
  (g : B → C)

-- a) If `f` and `g` are both one-to-one functions, show that `g ∘ f` is one-to-one.
example : Injective f → Injective g → (Injective (g ∘ f)) := by sorry

-- b) If `g ∘ f` is onto, show that `g` is onto.
example : Surjective (g ∘ f) → Surjective g := by sorry

-- c) If `g ∘ f` one-to-one, show that `f` is one-to-one.
example : Injective  (g ∘ f) → Injective f := by sorry

-- e) If `g ∘ f` onto and `g` is one-to-one, show that `f` is onto. <br>
example : Surjective (g ∘ f) → Injective g → Surjective f := by sorry

-- d) If `g ∘ f` one-to-one and `f` is onto, show that `g` is one-to-one. <br>
example : Injective (g ∘ f) → Surjective f → Injective g := by sorry

end P22

end Pset2
