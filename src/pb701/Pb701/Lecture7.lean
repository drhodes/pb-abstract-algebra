import Mathlib


α → α → α

namespace Closure

-- instance : Add (ℕ × ℝ) where
--   add (m, x) (n, y) = (m + n, x + y)

#check Add ℕ



end Closure


namespace MIL

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

protected theorem add_assoc (a b c : Point) : add (add a b) c = add a (add b c) := by
  ext <;> dsimp
  all_goals {
    rw [add]
    apply add_assoc
  }


def smul (r : ℝ) (p : Point) : Point := ⟨r * p.x, r * p.y, r * p.z⟩

theorem smul_distrib (r : ℝ) (a b : Point) :
    add (smul r a) (smul r b) = smul r (add a b) := by
  ext <;> dsimp
  all_goals {
    simp [add, smul]
    ring
  }

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]
end

def weightedAverage (β : Real) (β_nonneg : 0 ≤ β) (β_le : β ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := β * a.x + (1 - β) * b.x
  y := β * a.y + (1 - β) * b.y
  z := β * a.z + (1 - β) * b.z
  x_nonneg := by
    have p₁ : 0 ≤ (1 - β) := by simp_all only [sub_nonneg]
    have p₂ : 0 ≤ (1 - β) * b.x := mul_nonneg p₁ b.x_nonneg
    have p₃ : 0 ≤ β * a.x := mul_nonneg β_nonneg a.x_nonneg
    positivity
  y_nonneg := by
    have p₁ : 0 ≤ (1 - β) := by simp_all only [sub_nonneg]
    have p₂ : 0 ≤ (1 - β) * b.y := mul_nonneg p₁ b.y_nonneg
    have p₃ : 0 ≤ β * a.y := mul_nonneg β_nonneg a.y_nonneg
    positivity
  z_nonneg := by
    have p₁ : 0 ≤ (1 - β) := by simp_all only [sub_nonneg]
    have p₂ : 0 ≤ (1 - β) * b.z := mul_nonneg p₁ b.z_nonneg
    have p₃ : 0 ≤ β * a.z := mul_nonneg β_nonneg a.z_nonneg
    positivity
  sum_eq := by nlinarith [a.sum_eq, b.sum_eq]


open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex
noncomputable section

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp
end

def weightedAverage (n : ℕ) (β : Real) (β_nonneg : 0 ≤ β) (β_le : β ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n where
  x := β * a.x + (1 - β) * b.x
  y := β * a.y + (1 - β) * b.y
  z := β * a.z + (1 - β) * b.z
  x_nonneg := by
    have p₁ : 0 ≤ (1 - β) := by simp_all only [sub_nonneg]
    have p₂ : 0 ≤ (1 - β) * b.x := mul_nonneg p₁ b.x_nonneg
    have p₃ : 0 ≤ β * a.x := mul_nonneg β_nonneg a.x_nonneg
    positivity
  y_nonneg := by
    have p₁ : 0 ≤ (1 - β) := by simp_all only [sub_nonneg]
    have p₂ : 0 ≤ (1 - β) * b.y := mul_nonneg p₁ b.y_nonneg
    have p₃ : 0 ≤ β * a.y := mul_nonneg β_nonneg a.y_nonneg
    positivity
  z_nonneg := by
    have p₁ : 0 ≤ (1 - β) := by simp_all only [sub_nonneg]
    have p₂ : 0 ≤ (1 - β) * b.z := mul_nonneg p₁ b.z_nonneg
    have p₃ : 0 ≤ β * a.z := mul_nonneg β_nonneg a.z_nonneg
    positivity
  sum_eq := by nlinarith [a.sum_eq, b.sum_eq]



end StandardSimplex

end MIL


namespace SolvingEq

-- this is lame! need to
example : ∃ x, 2 * x + 1 ≡ 5 [ZMOD 7] := by exists 2;

end SolvingEq


namespace DigitSubtype

def Digits := { x : ℤ // 1 ≤ x ∧ x ≤ 9 }

instance : Add Digits where
  add x y :=
    let ⟨a, ha⟩ := x -- destructuring
    let ⟨b, hb⟩ := y
    ⟨a + b, by sorry⟩
  --          -┴---┴- this can't be proven.

end DigitSubtype

namespace AddNotClosed

def Digits := { x : ℤ // 1 ≤ x ∧ x ≤ 9 }

theorem not_closed_under_add : ∃ a b : ℤ, (1 ≤ a ∧ a ≤ 9) ∧
    (1 ≤ b ∧ b ≤ 9) ∧ ¬ (1 ≤ a + b ∧ a + b ≤ 9) := by
  use 9, 9 -- 9 + 9 ≤ 9 ?
  norm_num

end AddNotClosed



namespace CompositionGroup
-- needs work.

class UGroup (G : Type) [Mul G] [One G] [Inv G] where
  mul : G → G → G
  one : G
  inv : G → G
  --
  one_mul : ∀ x : G, 1 * x = x
  mul_one : ∀ x : G, x * 1 = x
  inv_mul_cancel : ∀ x : G, x⁻¹ * x = 1
  mul_assoc : ∀ x y z : G, x * y * z = x * (y * z)

def F (a : Type) := { x : a → a // Function.HasLeftInverse x }

variable (α : Type)

instance : One (F α)
  where one := ⟨id, by sorry⟩

instance : Mul (F α)
  where mul a b := ⟨a.val ∘ b.val, by sorry⟩

instance : Inv (F α) where
  inv f :=
    let ⟨g, hg⟩ := f
    ⟨choose hg, by sorry⟩





instance : UGroup (F α) where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  --
  one_mul := by simp
  mul_one := by simp

  inv_mul_cancel := by simp
  mul_assoc := by simp

end -- noncomputable section.
end CompositionGroup



namespace testing1

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

@[simp]
def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

@[simp]
def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

@[simp]
theorem addAlt_x (a b : Point) : (addAlt a b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm


end testing1
