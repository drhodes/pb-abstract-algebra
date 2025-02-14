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
