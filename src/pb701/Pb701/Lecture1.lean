import Mathlib

set_option autoImplicit true

-- @suhr says:

-- For equality such functions are rfl, Eq.subst, Eq.symm, Eq.trans, Eq.subst
-- and congrArg. For pairs, it's Pair.fst and Pair.snd. For natural numbers,
-- it's Nat.zero, Nat.succ, Nat.recOn and Nat.noConfusion.

-- It seems to be a rather unpopular opinion though, since most tutorials do not
-- even mention congrArg.


namespace Lecture1.SetAlgebra
open Set

variable
  (A B C : Set α)


-- 1) (Idempotency) A ∪ A = A and A ∩ A = A;

example : A ∪ A = A := by
  ext x
  constructor
  · intro ha
    rw [Set.union_self] at ha
    use ha
  · intro ha
    simp
    use ha

-- 2) (Identity) A ∪ ∅ = A and A ∩ U = A;
example : A ∪ ∅ = A ∧ A ∩ univ = A := by
  constructor
  · exact Set.union_empty A
  · --
    ext x
    constructor
    · intro h
      exact h.left
    · intro h
      rw [mem_inter_iff]
      refine ⟨h, by rw [mem_def]; trivial⟩



-- 3) (Absorption) A ∪ U = U , A ∩ ∅ = ∅, and A r ∅ = A;
-- 4) (Complements) A ∪ A′ = U , A ∩ A′ = ∅, and A r A = ∅;
-- 5) (Commutativity) A ∪ B = B ∪ A and A ∩ B = B ∩ A;
-- 6) (Associativity) A ∪ (B ∪ C) = (A ∪ B) ∪ C and A ∩ (B ∩ C) = (A ∩ B) ∩ C;
-- 7) (Distributivity) A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) and A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C);
-- 8) (De Morgan’s Laws) (A ∩ B)′ = A′ ∪ B′ and (A ∪ B)′ = A′ ∩ B′.

end Lecture1.SetAlgebra



namespace Tao_Exercise_3_6_6

-- Let A, B, C be sets. Show that the sets (A ^ B) ^ C and A ^ (B × C) have
-- equal cardinality by constructing an explicit bijection between the two sets.
-- Conclude that (a^b)*c = a^(b*c) for any natural numbers a, b, c. Use a
-- similar argument to also conclude ab × ac = ab+c.

-- Formalization:
--  rewrite set exponentiation A ^ B in terms of functions B → A.

-- Let A, B, C be types. Show that the family of functions C → (B → A) and
-- (B × C) → A have equal cardinality by constructing an explicit bijection between
-- the two families. Conclude that (a^b)^c = a^(b*c) for any natural numbers a,
-- b, c. Use a similar argument to also conclude a ^ b * a ^ c = a ^ (b + c).

variable (A B C : Type)

-- variable {α : Sort u} {β : Sort v} {γ : Sort w}

-- /-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
-- structure Equiv (α : Sort*) (β : Sort _) where
--   protected toFun : α → β
--   protected invFun : β → α
--   protected left_inv : LeftInverse invFun toFun
--   protected right_inv : RightInverse invFun toFun

def Equiv.toFun : (C → (B → A)) → (B × C) → A := sorry


example : C → (B → A) ≃ (B × C) → A := by



end Tao_Exercise_3_6_6
