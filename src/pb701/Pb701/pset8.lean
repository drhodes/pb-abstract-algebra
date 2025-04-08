import Mathlib
import Pb701.Lecture8

namespace P2

inductive L where | A | B | C | D deriving DecidableEq, Fintype
open L

namespace PartA
-- there is no row that matches the column indicators and there is no column
-- that matches the row indicators, hence there is no identity and no group.
end PartA

-- the rest of the tables have that 'A' is the identity element. So the
-- following instance can be factored out into the P2 namespace.

@[simp]
instance : One L where
  one := A

@[simp] lemma L.one_eq_one : (1 : L) = A := rfl

namespace PartB
-- PartB shows a commutative group, which can be inferred by inspection since
-- the table is symmetric, i.e. tableᵀ = table

@[simp]
instance : Mul L where
  mul a b :=
    let M := !![A, B, C, D;
                B, A, D, C;
                C, D, A, B;
                D, C, B, A]
    M a.toCtorIdx b.toCtorIdx

@[simp]
instance : Inv L where
  inv x := x

instance : U.Group L where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl
  inv_mul_cancel x := by cases x <;> rfl
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl

end PartB

---------------------------------------------------------------------------
namespace PartC

@[simp]
instance : Mul L where
  mul a b :=
    let M := !![A, B, C, D;
                B, C, D, A;
                C, D, A, B;
                D, A, B, C]
    M a.toCtorIdx b.toCtorIdx

@[simp]
instance : Inv L where
  inv x :=
    match x with
    | A => A
    | B => D
    | C => C
    | D => B

instance : U.Group L where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl
  inv_mul_cancel x := by cases x <;> rfl
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl

end PartC


namespace PartD
  -- In Part d, the table does not indicate an inverse for the D element,
  -- therefore this is not a group.
end PartD
end P2


namespace P3
  -- Rectangles have fewer symmetries than squares. Rectangle has no diagonal
  -- flips and only one rotation.

  inductive Rect where
  | I -- identity
  | V -- vertical flip
  | H -- horizontal flip
  | R -- 180 degree rotation.

  open Rect

  -- With Rect, every element is its own inverse.
  def caley_rect :=
    !![ I, V, H, R ;
        V, I, R, H ;
        H, R, I, V ;
        R, H, V, I ]

  -- Z₄ has a more complicated inverse function.
  def caley_Z₄ :=
    !![ 0, 1, 2, 3 ;
        1, 2, 3, 0 ;
        2, 3, 0, 1 ;
        3, 0, 1, 2 ]

  -- Although these are both groups, they have different inverse functions and
  -- are therefore different.
end P3


namespace P4
inductive Rhombus where
  | I
  | J -- Flip over Major Axis
  | N -- Flip over Minor Axis
  | R -- Rotate 180
  deriving DecidableEq
open Rhombus

@[simp]
instance : One Rhombus where
  one := I

@[simp] lemma Rhombus.one_eq_one : (1 : Rhombus) = I := rfl

@[simp]
instance : Mul Rhombus where
  mul a b :=
    let M := !![I, J, N, R;
                J, I, R, N;
                N, R, I, J;
                R, N, J, I]
    M a.toCtorIdx b.toCtorIdx

@[simp]
instance : Inv Rhombus where
  inv x := x

instance : U.Group Rhombus where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl
  inv_mul_cancel x := by cases x <;> rfl
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl

-- Is this group the same as a rectangle? Yes.

-- let cayley_rhombus :=
--   !![ I, J, N, R ;
--       J, I, R, N ;
--       N, R, I, J ;
--       R, N, J, I ]

-- def caley_rect :=
--   !![ I, V, H, R ;
--       V, I, R, H ;
--       H, R, I, V ;
--       R, H, V, I ]
end P4


namespace try1_P6

-- get a list from 0 to 11.
#eval List.range 12

-- determine which of those items, i, have gcd i 12 = 1
#eval List.filter (gcd · 12 = 1) (List.range 12)

-- build the set Z12.
@[simp] def Z12 : Set ℤ := {1, 5, 7, 11}

-- build the subtype U(12)
def U12 := {n : ℤ // n ∈ Z12}

instance : Mul U12 where
  mul x y :=
    let ⟨a, ha⟩ := x
    let ⟨b, hb⟩ := y
    ⟨(a * b) % 12, by cases ha <;> cases hb <;> aesop⟩

@[simp]
lemma U12.mul_eq_mul (x y : U12) :
  x * y = ⟨x.val * y.val % 12, by cases x.prop <;> cases y.prop <;> aesop⟩ := rfl

instance : One U12 where
  one := ⟨1, by simp⟩

@[simp]
lemma U12.one_eq_one : (1 : U12) = ⟨1, by simp⟩ := rfl

instance : Inv U12 where
  inv m := ⟨m.val, by cases m.prop <;> simp⟩

@[simp]
lemma U12.inv_eq_inv (m : U12) : m⁻¹ = ⟨m.val, by cases m.prop <;> simp⟩ := by rfl

-- todo: this is really clunky!
@[simp]
theorem U12.one_mul (x : U12) : 1 * x = x := by
  let ⟨a, ha⟩ := x
  rw [U12.one_eq_one]
  conv => lhs; rw [U12.mul_eq_mul]
  simp
  rcases ha with h|h|h|h
  all_goals {
    try simp at h
    simp_rw [h]
    ring_nf
  }

-- todo: this is really clunky!
@[simp]
theorem U12.mul_one (x : U12) : x * 1 = x := by
  let ⟨a, ha⟩ := x
  rw [U12.one_eq_one]
  conv => lhs; rw [U12.mul_eq_mul]
  dsimp [Z12, U12.mul_one]
  rcases ha with h|h|h|h
  all_goals {
    try simp at h
    simp_rw [h]
    ring_nf
  }

@[simp]
theorem U12.inv_mul_cancel (x : U12) : x⁻¹ * x = 1 := by
  let ⟨a, ha⟩ := x
  rcases ha with h|h|h|h
  all_goals {
    try simp at h
    simp_rw [h]
    simp
  }


instance : U.Group U12 where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  one_mul := U12.one_mul
  mul_one := U12.mul_one
  inv_mul_cancel := U12.inv_mul_cancel
  mul_assoc x y z := by
    simp only [U12.mul_eq_mul, Z12]
    let ⟨a, ha⟩ := x
    let ⟨b, hb⟩ := y
    let ⟨c, hc⟩ := z

    -- obtain h₁|h₁|h₁|h₁ := ha
    -- all_goals {
    --   try rw [Set.mem_singleton_iff] at h₁
    --   simp_rw [h₁]

    --   obtain h₁|h₁|h₁|h₁ := hb
    --   all_goals {
    --     try rw [Set.mem_singleton_iff] at h₁
    --     simp_rw [h₁]

    --     obtain h₁|h₁|h₁|h₁ := hc
    --     all_goals {
    --       try rw [Set.mem_singleton_iff] at h₁
    --       simp_rw [h₁]
    --       rfl
    --     }
    --   }
end try1_P6


namespace P6

-- get a list from 0 to 11.
#eval List.range 12

-- determine which of those items, i, have gcd i 12 = 1
#eval List.filter (gcd · 12 = 1) (List.range 12)

-- build the subtype U(12), Uni
def U12 := { a : ℕ // a < 12 ∧ a % 12 = 1 }

set_option profiler true

@[simp]
theorem U12.mul_helper
    (a : ℕ) (ha₁ : a < 12) (ha₂ : a % 12 = 1)
    (b : ℕ) (hb₁ : b < 12) (hb₂ : b % 12 = 1) :
    a * b % 12 < 12 ∧ a * b % 12 % 12 = 1 := by
  interval_cases a <;>
    interval_cases b <;>
      simp at *

@[simps]
instance : Mul U12 where
  mul x y := ⟨x.val * y.val % 12, by
    let ⟨a, ⟨ha₁, ha₂⟩⟩ := x
    let ⟨b, ⟨hb₁, hb₂⟩⟩ := y
    exact U12.mul_helper a ha₁ ha₂ b hb₁ hb₂
  ⟩

@[simp]
lemma U12.mul_eq_mul (x y : U12) :
  x * y = ⟨x.val * y.val % 12, by
    let ⟨a, ⟨ha₁, ha₂⟩⟩ := x
    let ⟨b, ⟨hb₁, hb₂⟩⟩ := y
    exact U12.mul_helper a ha₁ ha₂ b hb₁ hb₂
  ⟩ := rfl

instance : One U12 where
  one := ⟨1, by simp⟩

@[simp]
lemma U12.one_eq_one : (1 : U12) = ⟨1, by simp⟩ := rfl

@[simps]
instance : Inv U12 where
  inv m := ⟨m.val, by
    let ⟨a, ⟨ha₁, ha₂⟩⟩ := m
    simp_all only [and_self]
  ⟩

@[simp]
lemma U12.inv_eq_inv (m : U12) : m⁻¹ = ⟨m.val, m.prop⟩ := rfl

@[simp]
theorem U12.one_mul (x : U12) : 1 * x = x := by
  let ⟨a, ⟨ha₁, ha₂⟩⟩ := x
  interval_cases a <;> simp

@[simp]
theorem U12.mul_one (x : U12) : x * 1 = x := by
  let ⟨a, ⟨ha₁, ha₂⟩⟩ := x
  interval_cases a <;> simp

@[simp]
theorem U12.inv_mul_cancel (x : U12) : x⁻¹ * x = 1 := by
  let ⟨a, ⟨ha₁, ha₂⟩⟩ := x
  interval_cases a <;> {
    norm_num at ha₂
    try simp
  }

instance : U.Group U12 where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  one_mul := U12.one_mul
  mul_one := U12.mul_one
  inv_mul_cancel := U12.inv_mul_cancel

  mul_assoc x y z := by
    let ⟨a, ⟨ha₁, ha₂⟩⟩ := x
    let ⟨b, ⟨hb₁, hb₂⟩⟩ := y
    let ⟨c, ⟨hc₁, hc₂⟩⟩ := z
    interval_cases a <;> {
      norm_num at ha₂
      try simp
    }

end P6

namespace P15
-- Prove or disprove that every group containing six elements is abelian.

-- start with sequence (a, b, c)
inductive Sixers where
  | S0 -- shift elements by 0 right, (a, b, c)
  | S1 -- shift elements by 1 right, (c, a, b)
  | S2 -- shift elements by 2 right, (b, c, a)
  | R1 -- rotate elements 2 and 3 => (a, c, b)
  | R2 -- rotate elements 1 and 3 => (c, b, a)
  | R3 -- rotate elements 1 and 2 => (b, a, c)
  deriving DecidableEq
open Sixers

abbrev Trip := ℕ × ℕ × ℕ

def f : Trip → Sixers → Trip
  | (a, b, c), R1 => (a, c, b)
  | (a, b, c), R2 => (c, b, a)
  | (a, b, c), R3 => (b, a, c)
  | (a, b, c), S0 => (a, b, c)
  | (a, b, c), S1 => (c, a, b)
  | (a, b, c), S2 => (b, c, a)

#eval f (f (1,2,3) R3) S1

instance : One Sixers where
  one := S0

@[simp]
lemma Sixers.one_eq_one : (1 : Sixers) = S0 := rfl

@[simp]
instance : Mul Sixers where
  mul a b :=
    let M := !![S0, S1, S2, R1, R2, R3;
                S1, S2, S0, R2, R3, R1;
                S2, S0, S1, R3, R1, R2;
                R1, R3, R2, S0, S2, S1;
                R2, R1, R3, S1, S0, S2;
                R3, R2, R1, S2, S1, S0]
    M a.toCtorIdx b.toCtorIdx

instance : Inv Sixers where
  inv x :=
    match x with
    | R1 => R1
    | R2 => R2
    | R3 => R3
    | S0 => S0
    | S1 => S2
    | S2 => S1

example (x : Sixers) : x⁻¹ * x = 1 := by
  cases x <;> rfl

instance : U.Group Sixers where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl
  inv_mul_cancel x := by cases x <;> rfl
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl

#eval R1 * R2
#eval R2 * R1

-- show that sixers is not commutative.
example : ¬ ∀ a b : Sixers, a * b = b * a := by
  push_neg
  use R1, R2
  tauto

end P15


namespace P17

-- todo


end P17

-- namespace woot

-- structure Telescope (α : Type) [LinearOrderedField α] where
--   f : ℕ → α × α
--   h : ∀ n : ℕ, (f n).2 + (f (n + 1)).1 = 0

-- def g (n : ℕ ) : ℝ × ℝ := (n, -(n+1))

-- def tg : Telescope ℝ where
--   f := g
--   h n := by
--     induction' n with k hk
--     · simp [g]
--     · simp [g] at *
--       ring

-- --
-- example (i n : ℕ ) : n = ∑ i ∈ Set.Icc 0 n,
--     (g i).1 + (g i).2 + (g $ i + 1).1 + (g $ (i + 1)).2 := by
--   have := tg.h n
--   induction' n with k hk
--   · simp at *
--     simp [g] at *
--     norm_num

--   · done



-- end woot

-- namespace Telescopic
-- -- telescopic sequences are ones that collapse

-- abbrev α := ℤ -- α would be Type or more generic.

-- def myseq (n : ℕ) := 1 + n + (n - 1)

-- -- `dissect` prepares sequences for term cancelling.

-- def dissect (S : ℕ → α) : ℕ → (ℕ → α) := sorry



-- -- after a sequence is dissected

-- -- `mask` identifies the dissected terms that cancel
-- end Telescopic


namespace object



end object
