import Lean
import Mathlib
import Duper

namespace U

protected
class AddGroup (G : Type) extends Add G, Neg G, Zero G where
  zero_add : ∀ x : G, 0 + x = x
  add_zero : ∀ x : G, x + 0 = x
  neg_add_cancel : ∀ x : G, -x + x = 0
  add_assoc : ∀ x y z : G, x + y + z = x + (y + z)


class Group (G : Type) [Mul G] [One G] [Inv G] where
  mul : G → G → G
  one : G
  inv : G → G
  --
  one_mul : ∀ x : G, 1 * x = x
  mul_one : ∀ x : G, x * 1 = x
  inv_mul_cancel : ∀ x : G, x⁻¹ * x = 1
  mul_assoc : ∀ x y z : G, x * y * z = x * (y * z)





protected
class CommGroup (G : Type) [Mul G] [One G] [Inv G] where
  mul : G → G → G
  one : G
  inv : G → G
  --
  one_mul : ∀ x : G, 1 * x = x
  mul_one : ∀ x : G, x * 1 = x
  inv_mul_cancel : ∀ x : G, x⁻¹ * x = 1
  mul_assoc : ∀ x y z : G, x * y * z = x * (y * z)
  mul_comm : ∀ a b : G, a * b = b * a

-- `a ≡ b [U.ZMOD n]` when `a % n = b % n`.
-- def ModEq (n a b : ℤ) :=
--   a % n = b % n

-- @[inherit_doc]
-- notation:50 a " ≡ " b " [U.ZMOD " n "]" => ModEq n a b

end U

namespace P1

example : ∃ x, 3 * x ≡ 2 [ZMOD 7] := by sorry
example : ∃ x, 5 * x + 1 ≡ 13 [ZMOD 23] := by sorry
example : ∃ x, 5 * x + 1 ≡ 13 [ZMOD 26] := by sorry
example : ∃ x, 9 * x ≡ 3 [ZMOD 5] := by sorry
example : ∃ x, 5 * x ≡ 1 [ZMOD 6] := by sorry
example : ¬ ∃ x, 3 * x ≡ 1 [ZMOD 6] := by sorry

section solution

example : ∃ x, 3 * x ≡ 2 [ZMOD 7] := by exists 3
example : ∃ x, 5 * x + 1 ≡ 13 [ZMOD 23] := by exists 7
example : ∃ x, 5 * x + 1 ≡ 13 [ZMOD 26] := by exists -60
example : ∃ x, 9 * x ≡ 3 [ZMOD 5] := by exists 2
example : ∃ x, 5 * x ≡ 1 [ZMOD 6] := by exists -1

-- Thanks @aaron_liu for removing the boiler plate on this one.
example : ¬ ∃ x, 3 * x ≡ 1 [ZMOD 6] := by
  push_neg
  intro x hc
  mod_cases hx : x % 6 <;> try {
  · have := calc 1
      _ ≡ 3 * x [ZMOD 6] := hc.symm
      _ ≡ _ [ZMOD 6] := hx.mul_left 3
    rw [Int.modEq_iff_dvd] at this
    norm_num at this
  }
end solution
end P1

namespace P7
-- done

noncomputable section


abbrev R := {x : ℝ // x ≠ -1}

@[simp]
instance : One R where
  one := ⟨0, by norm_num⟩

@[simp]
lemma subt_one_eq_one : (1:R) = ⟨0, by norm_num⟩ := by rfl

@[simp]
lemma mul_ne_neg_one (x y : ℝ) (hx : x ≠ -1) (hy : y ≠ -1) : x + y + x * y ≠ -1 := by
  intro hc
  have hltx := lt_trichotomy (-1) x
  have hlty := lt_trichotomy (-1) y
  cases hltx with
  | inl h₁ =>
    obtain (h|h|h) := hlty
    · nlinarith
    · aesop
    · nlinarith
  | inr h₁ =>
    obtain (h|h|h) := hlty
    obtain (h₂|h₂) := h₁
    · aesop
    · nlinarith
    · aesop
    · --
      obtain (h₂|h₂) := h₁
      · aesop
      · nlinarith

@[simp]
instance : Mul R where
  mul a b :=
    let ⟨x, hx⟩ := a
    let ⟨y, hy⟩ := b
    ⟨x + y + x * y, mul_ne_neg_one x y hx hy⟩

@[simp]
lemma subt_mul (x y : R) : x * y =
  ⟨x.val + y.val + x.val * y.val, mul_ne_neg_one x y x.prop y.prop ⟩ := rfl

lemma helper₂ (a : ℝ) (ha : -1 < a) : a * (1 + a)⁻¹ < 1 := by
  have : (1 + a) ≠ 0 := by linarith
  rw [ne_iff_lt_or_gt] at this
  obtain (h|h) := this
  · nlinarith
  · rw [mul_inv_lt_iff₀' h]
    simp

lemma helper₁ (a : ℝ) (ha : a ≠ -1) : -a / (1 + a) ≠ -1 := by
  rw [ne_iff_lt_or_gt] at *
  obtain (h|h) := ha
  · left
    rw [← neg_lt_neg_iff]
    ring_nf
    conv => rhs; rw [mul_comm]
    have : 1 + a < 0 := by linarith
    rw [inv_mul_eq_div]
    rw [lt_div_iff_of_neg' this]
    linarith
  · right
    norm_num at *
    rw [← neg_lt_neg_iff]
    ring_nf
    apply (helper₂ a h)


instance : Inv R where
  inv x :=
    let ⟨a, ha⟩ := x
    ⟨- a / (1 + a), helper₁ a ha⟩


@[simp]
lemma subt_inv (x : R): x⁻¹ = ⟨- x.val / (1 + x.val), helper₁ x.val x.prop⟩ := rfl

-- todo refactor this hello lemma, or rename it
lemma hello {a : ℝ} (b : ℝ) (hb : b ≠ 0) : 0 = a ↔ 0 * b = a * b := by
  exact Iff.symm (mul_left_inj' hb)

@[simp]
theorem subt_inv_mul_cancel (x : R) : x⁻¹ * x = 1 := by
  obtain ⟨a, ha⟩ := x
  rw [subt_inv, subt_mul]
  simp
  symm

  rw [hello (1 + a) ?_]
  · --
    conv => lhs; simp

    -- introduce b to make the following algebra nicer.
    set b := 1 + a
    have h0 : b ≠ 0 := by
      simp [b]
      push_neg
      by_contra
      apply ha
      linarith

    have hb : b / b = 1 := (div_eq_one_iff_eq h0).mpr rfl

    calc (0:ℝ)
      _ = 0 + 0 := by ring
      _ = -a + a + 0 := by ring
      _ = -a + a + (a ^ 2 - a ^ 2) := by ring
      _ = (-a + a + a ^ 2 + -a * a) := by ring
      _ = (-a + a * (1 + a) + -a * a) := by ring
      _ = (-a + a * b + -a * a) := by ring
      _ = (-a + a * b + -a * (1) * a) := by ring
      _ = (-a + a * b + -a * (b / b) * a) := by rw [hb]
      _ = (-a + a * b + (-a * b) / b * a) := by ring
      _ = (-a + a * b + (b * -a) / b * a) := by ring
      _ = (-a + a * b + b * -a / b * a) := by ring
      _ = (-a * 1 + a * b + b * -a / b * a) := by ring
      _ = (-a * (b / b) + a * b + b * -a / b * a) := by rw [hb]
      _ = (-a * (b / b) + a * b + -a / b * a * b) := by ring
      _ = ((-a * b) / b) + a * b + -a / b * a * b := by ring
      _ = ((b * -a) / b) + a * b + -a / b * a * b := by ring
      _ = b * (-a / b) + a * b + -a / b * a * b := by ring
      _ = -a / b * b + a * b + -a / b * a * b := by ring
      _ = (-a / b + a + -a / b * a) * b := by ring

  · revert ha
    contrapose
    push_neg
    intro ha
    linarith

--
instance : U.CommGroup R where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  --
  mul_comm a b := by simp; ring
  one_mul := by simp
  mul_one := by simp

  inv_mul_cancel := subt_inv_mul_cancel
  mul_assoc := by intro x y z; simp; ring

end -- noncomputable section.
end P7



namespace P13
noncomputable section



--

@[simp]
abbrev ℝ₀ := {x : ℝ // x ≠ 0}

@[simp]
instance : Mul ℝ₀ where
  mul a b := ⟨a.val * b.val, mul_ne_zero a.prop b.prop⟩

@[simp]
lemma subt_mul (x y : ℝ₀) :
    x * y = ⟨x.val * y.val, mul_ne_zero x.prop y.prop⟩ :=
  rfl

@[simp]
instance : One ℝ₀ where
  one := ⟨1, by norm_num⟩

@[simp]
lemma subt_one_eq_one : (1:ℝ₀) = ⟨1, by norm_num⟩ := by rfl

@[simp]
instance : Inv ℝ₀ where
  inv x := ⟨(x.val)⁻¹, by aesop⟩

@[simp]
lemma subt_inv (x : ℝ₀): x⁻¹ = ⟨(x.val)⁻¹, by aesop⟩ := rfl

@[simp]
theorem subt_inv_mul_cancel (x : ℝ₀) : x⁻¹ * x = 1 := by
  obtain ⟨a, ha⟩ := x
  simp
  exact inv_mul_cancel₀ ha

instance : U.Group ℝ₀ where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  --
  one_mul := by simp
  mul_one := by simp
  inv_mul_cancel := subt_inv_mul_cancel
  mul_assoc := by intro x y z; simp; ring

end -- noncomputable section.
end P13

/-
namespace ExSubtype
noncomputable section

abbrev ℝ₀ := {x : ℝ // x ≠ 0}

instance : Mul ℝ₀ where
  mul a b := ⟨a.val * b.val, mul_ne_zero a.property b.property⟩

instance : Inv ℝ₀ where
  inv n := ⟨(n.val)⁻¹, by aesop⟩

instance : One ℝ₀ where
  one := ⟨1, by simp⟩

-- example (m : ℝ₀) : 1 * m = m := by
--   have ⟨v, hv⟩ := m



instance : U.Group ℝ₀ where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv

  one_mul (m : ℝ₀) : 1 * m = m := by sorry
  mul_one (a : ℝ₀) : a * 1 = a := by sorry
  mul_assoc (a b c : ℝ₀) : a * b * c = a * (b * c) := by sorry
  inv_mul_cancel (a : ℝ₀) : a⁻¹ * a = ⟨1, _⟩ := by sorry

end ExSubtype
-/

/-
namespace P100
noncomputable section
-- needs work.
-- The type for a 1×1 Matrix.

abbrev M := Matrix (Fin 1) (Fin 1) {x : ℝ // x ≠ 0}

@[simp] def mk (a : ℝ) (h : a ≠ 0) : M := !![⟨a, h⟩]

instance : Mul M where
  mul m₁ m₂ :=
    let a := m₁ 0 0
    let b := m₂ 0 0
    let c := a.val * b.val
    let h : c ≠ 0 := mul_ne_zero a.property b.property
    mk c h

instance : One M where
  one := mk 1 (by simp)

instance : Inv M where
  inv m :=
    let a := m 0 0
    let b := a.val⁻¹
    let h : b ≠ 0 := inv_ne_zero a.property
    mk b h

-- a constructor for the 1x1 matrix
instance : Group M where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv

  one_mul (m : M) : 1 * m = m := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp
      sorry
    }

  mul_one (a : M) : a * 1 = a := by sorry
  mul_assoc (a b c : M) : a * b * c = a * (b * c) := by sorry
  inv_mul_cancel (a : M) : a⁻¹ * a = (1 : M) := by sorry

end
end P100
-/




namespace P10
-- needs work.

-- The type for a 3×3 Matrix.
@[reducible, simp]
def M := Matrix (Fin 3) (Fin 3) ℝ

-- a constructor for the Heisenberg group matrices.
@[simp]
def mk (a b c : ℝ) := !![1, a, b;
                         0, 1, c;
                         0, 0, 1]

-- to extract relevent value from the upper right
@[simp]
def extract (m : M) := (m 0 1, m 0 2, m 1 2)

instance : Mul M where
  --mul m₁ m₂ := m₁ * m₂
  mul m₁ m₂ :=
    let (t, u, v) := extract m₁
    let (x, y, z) := extract m₂
    mk (t + x) (u + y) (v + z)

instance : One M where
  -- the identity matrix.
  one := mk 0 0 0

instance : Inv M where
  inv m₁ :=
    let (a, b, c) := extract m₁
    mk (-a) (a * c - b) (-c)

-- example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
--   have : Invertible !![(1 : ℝ), 2; 3, 4] := by
--     apply Matrix.invertibleOfIsUnitDet
--     norm_num
--   simp

/-
instance : Group M where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv

  one_mul (m : M) : 1 * m = m := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      rw [Matrix.mul_apply]
      simp
      norm_num
      sorry

    }

  mul_one (a : M) : a * 1 = a := by sorry
  mul_assoc (a b c : M) : a * b * c = a * (b * c) := by sorry
  inv_mul_cancel (a : M) : a⁻¹ * a = (1 : M) := by sorry
  -/
end P10


namespace WarmupFinGroup

abbrev T (n : ℕ) := (Fin n → ℤ)

variable (m : ℕ) -- (hm : 0 < m)

/-- no matter which index is passed into this zero function the result is always 0. -/
instance : Zero (T m) where
  zero := fun _ => (0 : ℤ)

@[simp]
lemma T.zero {n : ℕ} : (0 : T n) = fun _ => (0 : ℤ) := by rfl

instance : Add (T m) where
  add v w := fun i => ((v i) + (w i))

@[simp]
lemma T.add {n : ℕ} (v w : T n) : v + w = fun i => ((v i) + (w i)) := rfl

instance : Neg (T m) where
    neg v := fun i => - (v i)

@[simp]
lemma T.neg {n : ℕ} (v : T n) : -v = fun i => - (v i) := rfl

instance : U.AddGroup (T m) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel

end WarmupFinGroup

namespace WarmupZMod2

-- possibly redefine ZMod n in the U name space?
abbrev T := ZMod 2

instance : U.AddGroup T where
  zero_add := sorry
  add_zero := sorry
  neg_add_cancel := sorry
  add_assoc := sorry

section solution

instance : U.AddGroup T where
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  add_assoc := add_assoc

end solution


end WarmupZMod2


namespace P12

abbrev T (m : ℕ) := (Fin m → ZMod 2)

variable (n : ℕ)
instance : U.AddGroup (T n) where
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  add_assoc := add_assoc

end P12


namespace P14
open P13
#check ℝ₀

noncomputable section
abbrev G := ℝ₀ × ℤ

instance : Mul G where
  mul x y :=
    let ⟨a, m⟩ := x
    let ⟨b, n⟩ := y
    ⟨a * b, m + n⟩

@[simp]
lemma G.mul_eq_mul (x y : G) : x * y = ⟨x.1 * y.1, x.2 + y.2⟩ := by rfl

instance : One G where
  one := ⟨1, 0⟩

@[simp] protected
lemma G.one_eq_one : (1 : G) = ⟨1, 0⟩ := by rfl

instance : Inv G where
  inv x :=
    let ⟨a, m⟩ := x
    let result : G := ⟨a⁻¹, -m⟩
    result

@[simp] protected
lemma G.inv (x : G) : x⁻¹ = ⟨(x.1)⁻¹, -(x.2)⟩ := by rfl

instance : U.Group G where
  one := One.one
  mul := Mul.mul
  inv := Inv.inv
  --
  one_mul x := by simp

  mul_one x := by simp
  inv_mul_cancel := by
    intro ⟨⟨_, ha1⟩, _⟩
    simp
    exact inv_mul_cancel₀ ha1

  mul_assoc a b c := by
    simp
    simp [mul_assoc, add_assoc]

end
end P14


namespace P19 -- this one is too easy.

variable (n : ℤ)

example (a : ℤ) : 0 + a ≡ a + 0 [ZMOD n] := by
  simp

end P19


namespace P23 -- these are too easy.

variable (n : ℤ)

def U.ZMod.add_assoc (a b c : ℤ) : a + b + c ≡ a + (b + c) [ZMOD n] := by
  calc a + b + c
    _= a + (b + c) := by ring
    _≡ a + (b + c) [ZMOD n] := by exact rfl

def U.ZMod.add_comm (a b : ℤ) : a + b ≡ b + a [ZMOD n] := by
  calc a + b
    _= b + a := by ring
    _≡ b + a [ZMOD n] := by exact rfl

end P23



namespace P24 -- this one feels empty too.

variable (n : ℤ)

def U.ZMod.distrib (a b c : ℤ) : a * (b + c) ≡ a * b + a * c [ZMOD n] := by
  calc a * (b + c)
    _= a * b + a * c := by ring
    _≡ a * b + a * c [ZMOD n] := by exact rfl

end P24
