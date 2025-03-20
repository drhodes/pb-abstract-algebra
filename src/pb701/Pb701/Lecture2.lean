import Lean
import Mathlib

namespace Lecture2




-----------------------------------------------------------------
namespace Definition_1_2_12

variable
  (A : Set (Set ℕ))
  (B C : Set ℕ)
  (h : A = {{1}, {2}})

example : Π i : ℕ, A = {} := by
  sorry

end Definition_1_2_12


-----------------------------------------------------------------
namespace Example_1_2_13
open Set


variable
  (x y : ℝ)
  (A B C : Set ℝ)
  (ha : A = {x, y})
  (hb : B = {1, 2, 3})
  (hc : C = ∅)

example : A ×ˢ B = {(x, 1), (x,2), (x, 3), (y, 1), (y, 2), (y, 3)} := by sorry
example : A ×ˢ C = ∅ := by sorry

section solution

example : A ×ˢ B = {(x,1),(x,2),(x,3),(y,1),(y,2),(y,3)} := by
  ext a
  aesop -- todo.

example : A ×ˢ C = ∅ := by
  subst ha hb hc
  ext a
  refine ⟨mem_of_mem_inter_right, False.elim⟩
end solution

end Example_1_2_13

-----------------------------------------------------------------
namespace Example_1_2_20
open Function

-- this first example depends heavily on real analysis
noncomputable def f' (x : ℝ) := x ^ 3

-- so instead let's do one that still address the concept but is not so analysis
-- intensive.

noncomputable def f (x : ℝ) := 2 * x
noncomputable def g (x : ℝ) := Real.exp x
noncomputable def h (x : ℝ) := x ^ 2


example: f.Bijective = Bijective f := rfl

example : f.Bijective := by sorry
example : g.Injective ∧ ¬ g.Surjective := by sorry
example : ¬ h.Injective ∧ ¬ h.Surjective := by sorry

section solution

example : f.Bijective := by
  constructor
  · intro a b
    simp [f]
  · intro b
    use ((1/2) * b)
    simp [f]

example : g.Injective ∧ ¬ g.Surjective := by
  constructor
  · intro a b h
    dsimp [g] at h
    rwa [← Real.exp_eq_exp]
  · --
    simp [Surjective, g]
    push_neg
    use (0)
    intro x
    simp

example : ¬ Injective h ∧ ¬ Surjective h := by
  constructor
  · dsimp [Injective, h]
    push_neg
    use -1, 1
    norm_num
  · dsimp [Surjective, h]
    push_neg
    use -1
    intro a ha
    nlinarith

end solution

end Example_1_2_20

namespace try1
-- refer to https://math.stackexchange.com/questions/3217507
-- noncomputable def f (x : ℝ) := x ^ 3


lemma bij1 (a b : ℝ) (h : a ^ 3 - b ^ 3 = 0) :
  (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by linarith

lemma bij2 (a b : ℝ) :
  a ^ 2 + a * b + b ^ 2 = (1 / 2) * ((a + b) ^ 2 + a ^ 2 + b ^ 2) := by linarith

-- should be doable with odd denominators?
example (a b : ℝ) (c : ℚ) (hc : Odd c.den) : (a * b).rpow c = a.rpow c * b.rpow c := by
  let v := c.num
  let w := c.den
  have : c = v / w := by exact Eq.symm (Rat.num_div_den c)
  rw [this]
  sorry

example (b : ℝ) : ∃ a, a ^ 3 = b := by
  use (b ^ (3⁻¹:ℝ))
  obtain h|h|h := lt_trichotomy b 0
  · --
    let c := (3⁻¹ : ℝ)
    have h₁ : b = -1 * |b| := by sorry
    rw [h₁]
    have h₂ :=
    calc ((-1 * |b|) ^ c) ^ 3
      _= (((-1) ^ c) * (|b| ^ c)) ^ 3 := by sorry

  · rw [h]; simp
  · sorry


example : Function.Bijective (fun (x : ℝ) => x ^ 3) := by
  constructor
  · --
    intro a b hf
    simp at *
    have h₀ := bij1 a b
    have h₁ := bij2 a b
    have h₂ : (a ^ 2 + a * b + b ^ 2) = 0 ↔ a = 0 ∧ b = 0 := by
      constructor
      · --
        intro ht
        by_contra hc
        push_neg at hc
        obtain h|h|h := lt_trichotomy a 0
        · nlinarith
        · apply (hc h)
          rw [h] at hf
          nlinarith
        · nlinarith
      · --
        intro ⟨ha, hb⟩
        rw [ha, hb]
        norm_num
    aesop? -- todo
    linarith
  · --
    sorry
end try1

-- ------------------------------------------------------------------------------

namespace Example_ASDFASDF

def Relation (α β : Type) := Set (α × β)

-- MoP uses lean4 functions as functions.
def square (n : ℕ) : ℕ := n ^ 2


#check Function.Bijective



end Example_ASDFASDF

end Lecture2








namespace Lecture1.CoinExample

inductive Op where | Flip | Ident deriving Repr
open Op

instance : Mul Op where
  mul
  | Flip, Flip => Ident
  | Ident, Ident => Ident
  | Ident, Flip => Flip
  | Flip, Ident => Flip

instance : One Op where one := Ident
instance : Inv Op where inv f := f

instance : Group Op where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv

  one_mul (a : Op) : 1 * a = a := by
    cases a <;> rfl

  mul_one (a : Op) : a * 1 = a := by
    cases a <;> rfl

  mul_assoc (a b c : Op) : a * b * c = a * (b * c) := by
    cases a <;> cases b <;> cases c <;> rfl

  inv_mul_cancel (a : Op) : a⁻¹ * a = (1 : Op) := by
    cases a <;> rfl

end Lecture1.CoinExample


namespace Lecture1.SquareExample

inductive Op where | R0 | R90 | R180 | R270 | H | V | D1 | D2
  deriving Repr, BEq

open Op

def cayley_table : Matrix (Fin 8) (Fin 8) Op :=
  ![![R0  , R90 , R180, R270, H   , V   , D1  , D2  ],
    ![R90 , R180, R270, R0  , D2  , D1  , H   , V   ],
    ![R180, R270, R0  , R90 , V   , H   , D2  , D1  ],
    ![R270, R0  , R90 , R180, D1  , D2  , V   , H   ],
    ![H   , D1  , V   , D2  , R0  , R180, R90 , R270],
    ![V   , D2  , H   , D1  , R180, R0  , R270, R90 ],
    ![D1  , V   , D2  , H   , R270, R90 , R0  , R180],
    ![D2  , H   , D1  , V   , R90 , R270, R180, R0  ]]

instance : Mul Op where
  mul a b :=
    let idx1 := a.toCtorIdx
    let idx2 := b.toCtorIdx
    cayley_table idx1 idx2

instance : One Op where one := R0

instance : Inv Op where inv
  | R0 => R0
  | R90 => R270
  | R180 => R180
  | R270 => R90
  | x => x

instance : Group Op where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv

  one_mul (a : Op) : 1 * a = a := by
    cases a <;> rfl

  mul_one (a : Op) : a * 1 = a := by
    cases a <;> rfl

  mul_assoc (a b c : Op) : a * b * c = a * (b * c) := by
    cases a <;> cases b <;> cases c <;> rfl

  inv_mul_cancel (a : Op) : a⁻¹ * a = (1 : Op) := by
    cases a <;> rfl

end Lecture1.SquareExample


namespace Lecture1.Dihedral
-- this is from mathlib.

variable (α : ℕ)

inductive Op α where
  | r : (ZMod α) → Op α
  | sr : (ZMod α) → Op α
  deriving Repr, DecidableEq

open Op

instance : Mul (Op α) where
  mul
  | r i, r j   =>  r $ i + j -- TODO, draw a table out for this.
  | r i, sr j  => sr $ j - i
  | sr i, r j  => sr $ i + j
  | sr i, sr j =>  r $ j - i

instance : One (Op α) where one := r 0

instance : Inv (Op α) where inv
  | r i => r (-i)
  | sr i => sr i

instance : Group (Op α) where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv

  one_mul := by
    rintro (a | a)
    · calc 1 * r a
        _= r 0 * r a := rfl
        _= r (0 + a) := rfl
        _= r a := by simp
    · calc 1 * sr a
        _= r 0 * sr a := rfl
        _= sr (a - 0) := rfl
        _= sr a := by simp

  mul_one := by
    rintro (a | a)
    · calc r a * 1
        _= r a * r 0 := rfl
        _= r (a + 0) := rfl
        _= r a := by simp
    · calc sr a * 1
        _= sr a * r 0 := rfl
        _= sr (a + 0) := rfl
        _= sr a := by simp

  -- this is from mathlib.
  mul_assoc := by
    rintro (a | x) (b | y) (c | z) <;> simp [· * ·, Mul.mul] <;> sorry

  inv_mul_cancel := by
    rintro (a | a) <;> simp [· * ·, Mul.mul] <;> rfl

end Lecture1.Dihedral


namespace Lecture1.Trihedral

variable (α : ℕ)

inductive Op α where
  | r : (ZMod α) → Op α
  | sr : (ZMod α) → Op α
  deriving Repr, DecidableEq

open Op

instance : Mul (Op α) where
  mul
  | r i, r j   =>  r $ i + j -- TODO, draw a table out for this.
  | r i, sr j  => sr $ j - i
  | sr i, r j  => sr $ i + j
  | sr i, sr j =>  r $ j - i

instance : One (Op α) where one := r 0

instance : Inv (Op α) where inv
  | r i => r (-i)
  | sr i => sr i

instance : Group (Op α) where
  mul := Mul.mul
  one := One.one
  inv := Inv.inv

  one_mul := by
    rintro (a | a)
    · calc 1 * r a
        _= r 0 * r a := rfl
        _= r (0 + a) := rfl
        _= r a := by simp
    · calc 1 * sr a
        _= r 0 * sr a := rfl
        _= sr (a - 0) := rfl
        _= sr a := by simp

  mul_one := by
    rintro (a | a)
    · calc r a * 1
        _= r a * r 0 := rfl
        _= r (a + 0) := rfl
        _= r a := by simp
    · calc sr a * 1
        _= sr a * r 0 := rfl
        _= sr (a + 0) := rfl
        _= sr a := by simp

  -- this is from mathlib.
  mul_assoc := by
    rintro (a | x) (b | y) (c | z) <;> simp [· * ·, Mul.mul] <;> sorry

  inv_mul_cancel := by
    rintro (a | a) <;> simp [· * ·, Mul.mul] <;> rfl

end Lecture1.Dihedral
