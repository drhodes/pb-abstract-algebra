import Undergrad.Basic


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
