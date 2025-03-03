import Undergrad
import Mathlib

namespace PSet1

namespace P1

def f (n : ℕ) :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) ^ 2 + (f n)

def g (n : ℕ) := n * (n + 1) * (2 * n + 1)

example (n : ℕ) (hn : 0 < n) : 6 * f n = g n := by
  induction' hn with k hk hki
  · done
  · done

-- solution
example (n : ℕ) (hn : 0 < n) : 6 * f n = g n := by
  induction' hn with k hk hki
  · simp; rfl
  · dsimp [f]
    rw [Nat.mul_add, hki]
    dsimp [g]
    ring

end P1


namespace P4

variable (α : Type) (A: Set α)

example : A ∪ ∅ = A ∧ A ∩ ∅ = ∅ := by
  sorry

section solution

example (A: Set α) : A ∪ ∅ = A ∧ A ∩ ∅ = ∅ := by
  simp


end solution

end P4


-- -------------------------------------------------------------
namespace P5

variable (α : Type) (A B: Set α)

example : A ∪ B = B ∪ A ∧ A ∩ B = B ∩ A := by
  sorry

section solution

example : A ∪ B = B ∪ A ∧ A ∩ B = B ∩ A := by
  constructor
  · exact Set.union_comm A B
  · exact Set.inter_comm A B


end solution

end P5


-- -------------------------------------------------------------
namespace P6

variable (α : Type) (A B C: Set α)

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry

section solution

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  -- todo ? there is a real question about where to draw the line between which
  -- automation is too much?
  exact Set.union_inter_distrib_left A B C

end solution

end P6



-- -------------------------------------------------------------
namespace P7

variable (α : Type) (A B C: Set α)

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  sorry

section solution

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  exact Set.inter_union_distrib_left A B C

end solution

end P7


-- -------------------------------------------------------------
namespace P8
open Set

variable (α : Type) (A B : Set α)

example : A ⊆ B ↔ A ∩ B = A := by
  sorry

section solution

example : A ⊆ B ↔ A ∩ B = A := by
  constructor
  · -- A ⊂ B → A ∩ B = A
    rw [inter_eq_left, imp_self]
    trivial
  · -- A ∩ B = A → A ⊂ B
    intro h
    rw [←h, inter_def]
    rw [sep_mem_eq]
    apply inter_subset_right

end solution

end P8





theorem Like_Example_6_1_2 (n : ℕ) : 3 ∣ n^3 + 2 * n := by
  induction' n  with k hk
  · -- Base case: n = 0
    norm_num

  · -- Inductive step: Assume the statement holds for some n, prove it for n + 1
    obtain ⟨p, hp⟩ := hk
    have :=
    calc (k + 1) ^ 3 + 2 * (k + 1)
      _ = 3 + 5 * k + 3 * k ^ 2 + k ^ 3 := by ring
      _ = k ^ 3 + 2 * k + 3 * k + 3 * k ^ 2 + 3  := by ring
      _ = 3 * p + 3 * k + 3 * k ^ 2 + 3  := by rw [hp]
      _ = 3 * (p + k + k ^ 2 + 1) := by ring

    rw [this]
    apply dvd_mul_right
