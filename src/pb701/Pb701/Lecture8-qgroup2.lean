import Mathlib
import Pb701.pset7

namespace QuaternionGroupExample2
noncomputable section

-- create a custom 2x2 complex matrix
@[ext]
structure M where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  deriving DecidableEq

abbrev im := Complex.I

set_option profiler true

instance : Neg M where
  neg m := M.mk (-m.a) (-m.b) (-m.c) (-m.d)

@[simp] lemma neg_m (m : M) : -m = M.mk (-m.a) (-m.b) (-m.c) (-m.d) := rfl

instance : Mul M where
  mul v w := M.mk
    (v.a * w.a + v.b * w.c) (v.a * w.b + v.b * w.d)
    (v.c * w.a + v.d * w.c) (v.c * w.b + v.d * w.d)

@[simp]
lemma mul_eq (v w : M) : v * w = M.mk
    (v.a * w.a + v.b * w.c) (v.a * w.b + v.b * w.d)
    (v.c * w.a + v.d * w.c) (v.c * w.b + v.d * w.d) := by rfl

instance : Inv M where
  inv m := M.mk (m.d) (-m.b) (-m.c) (m.a)

@[simp] lemma inv_m (m : M) : m⁻¹ = M.mk (m.d) (-m.b) (-m.c) (m.a) := rfl


instance : One M where
  one := M.mk 1 0 0 1

@[simp] lemma one_m : (1 : M) = M.mk 1 0 0 1 := rfl

-- define the elements
@[simp] def I  : M := M.mk 0 1 (-1) 0
@[simp] def J  : M := M.mk 0 im im 0
@[simp] def K  : M := M.mk im 0 0 (-im)

-- collect the elements with their negations
@[simp] def S : Set M := {1, -1, I, -I, J, -J, K, -K}

-- maybe a subtype isn't the best choice for showing the group structure
abbrev Q₈ := {m : M // m ∈ S}

lemma neg_mem_of_mem (m : M) : m ∈ S → -m ∈ S := by
  intro h
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp

lemma neg_mem_of_mem' (m : M) : m ∈ S → -m ∈ S := by
  intro h
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp


-- satisfying the subtype hypotheses for the instance Mul.mul on Q₈
-- thanks Wang JingTing
lemma mul_closed (m n : M) (hm : m ∈ S) (hn : n ∈ S): m * n ∈ S := by
  simp [S] at *
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals (rcases hn with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))
  all_goals simp

instance : Mul Q₈ where
  mul m n := ⟨m.val * n.val, mul_closed m.val n.val m.prop n.prop⟩

lemma Q₈.mul_eq (m n : Q₈) : m * n =
  ⟨m.val * n.val, mul_closed m.val n.val m.prop n.prop⟩ := rfl

lemma inv_helper (m : Q₈) : m.1⁻¹ ∈ S := by
    simp [S] at *
    obtain h|h|h|h|h|h|h|h := m.prop
    all_goals {
      rw [h]
      simp
    }

lemma inv_helper' (m : Q₈) : m.1⁻¹ ∈ S := by
    simp [S] at *
    rcases m.prop with h|h|h|h|h|h|h|h
    all_goals {
      rw [h]
      simp
    }

instance : Inv Q₈ where
  inv m := ⟨m.1⁻¹, by apply inv_helper⟩

lemma Q₈.inv_eq (m : Q₈) : m⁻¹ = ⟨m.1⁻¹, by apply inv_helper⟩ := by rfl

instance : One Q₈ where
  one := ⟨1, by simp⟩

lemma Q₈.one_eq : (1 : Q₈) = ⟨1, by simp⟩ := rfl

@[simp]
lemma Q₈.one_mul : ∀ x : Q₈, 1 * x = x := by
  intro ⟨x, hx⟩
  simp [Q₈.one_eq, Q₈.mul_eq]

@[simp]
lemma Q₈.mul_one : ∀ x : Q₈, x * 1 = x := by
  intro x
  simp [Q₈.one_eq, Q₈.mul_eq, Id]
  rfl

@[simp]
theorem Q₈.inv_mul_cancel (m : Q₈) : m⁻¹ * m = 1 := by
  simp [Q₈.inv_eq, Q₈.mul_eq]
  ext <;> simp
  all_goals {
    rcases m.prop with h|h|h|h|h|h|h|h
    all_goals {
      rw [h]
      simp
      rfl
    }
  }

instance : U.Group Q₈ where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  --

  one_mul := Q₈.one_mul
  mul_one := Q₈.mul_one
  inv_mul_cancel := Q₈.inv_mul_cancel

  mul_assoc := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    repeat rw [Q₈.mul_eq]
    ring_nf
    ext
    all_goals simp; ring

end
end QuaternionGroupExample2
