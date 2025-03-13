import Mathlib

namespace Lecture6

variable
  (a b : ℤ)
  (S : Set ℤ)

-- Let S = { a - b * k | k ∈ ℤ, a - b * k ≥ 0 }, which is a subset of the natural
-- numbers.

namespace div_algo
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction
open Nat

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div (x - y) y + 1
  else
    0

end div_algo

theorem division_algorithm (hs : S = { x : ℤ | ∃ k : ℤ, x = a - b * k ∧ 0 ≤ x })
    (hb : 0 < b) : ∃ q r, 0 ≤ r ∧ r < b → (a = q * b + r ) := by

  -- If a ≥ 0, then a - b * 0 ∈ S.
  have ha : 0 ≤ a → (a - b * 0) ∈ S := by
    sorry

  -- If a < 0, then a - b ( 2a ) = a ( 1 - 2b ) ≥ 0, so a - b ( 2a ) ∈ S.

  -- In either case, S is not empty.
  have hs : S.Nonempty := by
    obtain ⟨h1, hf⟩ := hs
    simp
    use a
    simp
    constructor
    · use 0; simp
    · sorry



  -- By the well - ordering principle, there is a minimal element of S, call it r.

  -- Let q be an integer for which r = a - bq.

  -- We claim that 0 ≤ r < b.

  -- By definition of S, it must be that r ≥ 0.

  -- Consider the number a - b ( q + 1 ), which is smaller than r.

  -- Since r is minimal in S, we conclude that a - b ( q + 1 ) < 0, which implies
  -- that r - b < 0  or r < b.

  -- Therefore, there exist integers q and r such that a = bq + r and 0 ≤ r < b.

  -- To show that these numbers are unique, suppose that a = bq + r and a = bq ' +
  -- r ', with 0 ≤ r, r ' < b.

  -- Without loss of generality, assume that r ' ≥ r.

  -- Then, bq + r = bq ' + r ' ⇒ b ( q - q ' ) = r ' - r ≥ 0.

  -- Thus, b divides r ' - r and since r ' - r < b the only possibility is r ' - r
  -- = 0, so r ' = r and consequently q = q '.

  sorry
  done


end Lecture6


namespace example_1

-- @suhr on zulip says:
example (a b : ℤ) (h : a + b = 0) : -a = b := by
  suffices g: a + -a = a + b by
    apply_fun (-a + ·) at g
    simp at g
    exact g
  simp

  show 0 = a + b
  symm

  show a + b = 0
  exact h

end example_1
