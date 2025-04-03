import Mathlib
import Pb701.pset7

namespace U
end U

namespace QuaternionGroupExample
noncomputable section

-- establish shorthand for 2x2 complex matrix.
abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev im := Complex.I


-- define the elements
@[simp, match_pattern, reducible] def Id : M := !![1, 0; 0, 1]
@[simp, match_pattern, reducible] def I  : M := !![0, 1; -1, 0]
@[simp, match_pattern, reducible] def J  : M := !![0, im; im, 0]
@[simp, match_pattern, reducible] def K  : M := !![im, 0; 0, -im]

-- @[simp] lemma mat_one_eq_one : Id = (1 : M) := by
--   simp at *

-- collect the elements with their negations
@[simp] def S : Set M := {Id, -Id, I, -I, J, -J, K, -K}

-- maybe a subtype isn't the best choice for showing the group structure
abbrev Q₈ := {m : M // m ∈ S}

lemma neg_mem_of_mem (m : M) : m ∈ S → -m ∈ S := by
  intro h
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp

-- satisfying the subtype hypotheses for the instance Mul.mul on Q₈

-- thanks Wang JingTing
set_option profiler true
lemma mul_closed (m n : M) (hm : m ∈ S) (hn : n ∈ S): m * n ∈ S := by
  simp [S] at *
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals (rcases hn with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))
  all_goals simp

instance : Mul Q₈ where
  mul m n := ⟨m.val * n.val, mul_closed m.val n.val m.prop n.prop⟩

lemma Q₈.mul_eq (m n : Q₈) : m * n = ⟨m.val * n.val, mul_closed m.val n.val m.prop n.prop⟩ := rfl

--                         row ---, ,-- column
--                                | |
@[simp] def a (m : Q₈) : ℂ := m.1 0 0
@[simp] def b (m : Q₈) : ℂ := m.1 0 1
@[simp] def c (m : Q₈) : ℂ := m.1 1 0
@[simp] def d (m : Q₈) : ℂ := m.1 1 1


lemma inv_helper (m : Q₈) : !![d m, -b m; -c m, a m] ∈ S := by
    simp [S] at *
    obtain h|h|h|h|h|h|h|h := m.prop
    all_goals {
      rw [h]
      simp
    }

lemma inv_helper' (m : Q₈) : !![d m, -b m; -c m, a m] ∈ S := by
    simp [S] at *
    rcases m.prop with h|h|h|h|h|h|h|h
    all_goals {
      rw [h]
      simp
    }

instance : Inv Q₈ where
  inv m := ⟨!![d m, -(b m); -(c m), a m], by apply inv_helper⟩

lemma Q₈.inv_eq (m : Q₈) : m⁻¹ = ⟨!![d m, -(b m); -(c m), a m], by apply inv_helper⟩ := by rfl

instance : One Q₈ where
  one := ⟨Id, by simp⟩

lemma Q₈.one_eq : (1 : Q₈) = ⟨Id, by simp⟩ := rfl

instance : U.Group Q₈ where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  --

  one_mul := by
    intro x
    have : (Id : M) * (x.val : M) = (x.val : M) := by aesop -- todo
    rw [Q₈.one_eq, Q₈.mul_eq]
    simp_rw [this]

  mul_one := by
    intro x
    have : (x.val : M) * (Id : M) = (x.val : M) := by aesop -- todo
    simp [Q₈.one_eq, Q₈.mul_eq, Id]
    simp_rw [this]
    rfl

  inv_mul_cancel := by
    intro m
    simp [Q₈.inv_eq, Q₈.mul_eq]
    sorry

  mul_assoc := by
    intro x y z
    simp [Q₈.mul_eq]
    group


end
end QuaternionGroupExample













namespace clues

-- lemma mul_closed'' (m n : M) (hm : m ∈ S) (hn : n ∈ S) : m * n ∈ S := by
--   simp [S] at *
--   rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> {
--     all_goals {
--       · rcases hn with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
--         all_goals simp
--     }
--   }

-- theorem mul_closed'''' (m n : M) (hm : m ∈ S) (hn : n ∈ S) : m * n ∈ S := by
--   simp [S] at *
--   obtain -|-|-|-|-|-|- := hm
--   all_goals {
--     · obtain h₂|h₂|h₂|h₂|h₂|h₂|h₂|h₂ := hn
--       all_goals {
--         rw [_, h₂]
--         conv => rhs; simp
--         sorry
--       }
--   }


end clues
