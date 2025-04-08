import Mathlib
import Pb701.Lecture8
import Pb701.pset7

-- Homework: Judson 3.5: Pick 3 (27-30, 49), Pick 2 (31-33, 51)

namespace restitution
-- here are proven the items of simp, beholden to honesty.

variable {M : Type*} [Mul M] [One M]
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}


#check mul_inv_rev
#check List.map_cons
#check List.map_nil

#check List.prod_append

example (l₁ l₂ : List M) : (l₁ ++ l₂).prod = l₁.prod * l₂.prod := by
  sorry

#check List.prod_cons
example {a : M} {l : List M} : (a :: l).prod = a * l.prod := by
  dsimp [List.prod]


#check List.prod_nil
example : [].prod = 1 := rfl

#check List.reverse_cons
example (a : α) (as : List α) : List.reverse (a :: as) = List.reverse as ++ [a] := by
  dsimp [List.reverse]
  repeat rw [List.reverseAux_eq]
  rw [List.append_nil]

#check List.reverse_nil

end restitution

namespace P27
open List
-- Exercise 27 @ http://abstract.ups.edu/aata/groups-exercises.html#pEz
variable {G : Type} [Group G]

#check List.prod_inv_reverse


-- this the mathlib solution without simps, expanded line by line so it's easy
-- to browse.

theorem unsimp_prod_inv_reverse (gs : List G) : (gs.prod)⁻¹ = (gs.map Inv.inv).reverse.prod := by
  match gs with
  | [] =>
    · rw [map_nil]
      rw [reverse_nil]
      rw [prod_nil] at *
      rw [inv_one]
  | x :: xs =>
    · -- lhs
      rw [prod_cons]
      rw [mul_inv_rev]
      -- rhs
      rw [map_cons]
      rw [reverse_cons]
      rw [prod_append]
      rw [prod_cons]
      rw [prod_nil]
      rw [mul_one]
      --
      rw [unsimp_prod_inv_reverse]

theorem prod_inv_reverse' : ∀ gs : List G, (gs.prod)⁻¹ = (gs.map Inv.inv).reverse.prod
  | [] => by simp
  | x :: xs => by simp [prod_inv_reverse' xs]

theorem prod_inv_reverse'mathlib : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod
  | [] => by simp
  | x :: xs => by simp [prod_inv_reverse xs]

end P27


namespace P30
variable {G : Type} [Group G]

variable (a b c : G)


theorem T301 : b * a = c * a → b = c := by
  rw [mul_right_cancel_iff]
  rw [imp_self]
  trivial


theorem T302 : a * b = a * c → b = c := by
  rw [mul_left_cancel_iff]
  rw [imp_self]
  trivial

end P30

namespace P31

variable (G : Type) [Group G]

-- this example formalization is from
-- https://github.com/ImperialCollegeLondon/formalising-mathematics-2024/blob/main/FormalisingMathematics2024/Section05groups/Sheet1.lean


theorem T31 (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  intro a b
  have :=
  calc              a * b = b * a
    _ ↔ (a * b) * (a * b) = (b * a) * (a * b) := by simp [mul_left_inj]
    _ ↔ (a * b) * (a * b) = b * (a * a) * b := by group
    _ ↔                 1 = b * (a * a) * b := by rw [h $ a * b]
    _ ↔                 1 = b * 1 * b := by rw [h a]
    _ ↔                 1 = b * b := by rw [mul_one]
    _ ↔                 1 = (1 : G) := by rw [h b]
  rw [this]

variable (a b : G)

example (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) : (a * b) ^ 2 = 1 → a * b = b * a := by
  intro h
  have :=
  calc              a * b = b * a
    _ ↔ (a * b) * (a * b) = (b * a) * (a * b) := by simp [mul_left_inj]
    _ ↔ (a * b) * (a * b) = b * (a * a) * b := by group
    _ ↔       (a * b) ^ 2 = b * (a * a) * b := by rw [pow_two $ a * b]
    _ ↔                 1 = b * (a * a) * b := by rw [h]
    _ ↔                 1 = b * (a ^ 2) * b := by rw [pow_two a]
    _ ↔                 1 = b * 1 * b := by rw [ha]
    _ ↔                 1 = b * b := by rw [mul_one]
    _ ↔                 1 = b ^ 2 := by rw [pow_two b]
    _ ↔                 1 = (1 : G) := by rw [hb]
  rw [this]

end P31


namespace P32Warmup
variable (G : Type) [Group G] [Fintype G]

theorem T32 (hg : Fintype.card G = 2) : ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1 := by

end P32Warmup


namespace P32
variable (G : Type) [Group G] [Fintype G]

-- a group must have at least one element for identity.

theorem T32 (h : Even $ Fintype.card G) (h₂ : 1 < Fintype.card G) : ∃ a : G, a ≠ 1 → a ^ 2 = 1 := by
  obtain ⟨b, hb⟩ := h


end P32



namespace P32'

variable (G : Type) [Group G] [Fintype G]

theorem T32 (hg : Even $ Fintype.card G) : ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1 := by
  sorry



end P32'




namespace P33
variable (G : Type) [Group G]


theorem T33 : ∀ a b : G, (a * b) ^ 2 = a ^ 2 * b ^ 2 → a * b = b * a := by
  intro a b h
  rw [← mul_left_inj b, ← mul_right_inj a]

  calc a * (a * b * b)
    _ = (a * a) * (b * b) := by group
    _ = a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]
    _ = (a * b) ^ 2 := by rw [h]
    _ = (a * b) * (a * b) := by rw [pow_two]
    _ = a * (b * a * b) := by group

end P33

namespace P49
variable (G : Type) [Group G]


theorem T49 (a b : G) (h₁ : a ^ 4 * b = b * a) (h₂ : a ^ 3 = 1) : a * b = b * a := by
  symm
  calc b * a
    _ = a ^ 4 * b := h₁.symm
    _ = a ^ 3 * a * b := by rw [pow_succ]
    _ = 1 * a * b := by rw [h₂]
    _ = a * b := by rw [one_mul]

end P49




namespace P51
variable {G : Type} [Group G]

lemma law1 (x y : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : x ^ 2 * y ^ 2 = 1 := by
  simp only [pow_two]
  calc x * x * (y * y)
    _ = x * (x * y) * y := by group
    _ = 1 := by simp [h x y]

lemma law2 (x y : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : ((x * y)⁻¹ ^ (2)) = (y * x) ^ 2 := by
  simp only [sq]
  calc (x * y)⁻¹ * (x * y)⁻¹
    _ = (y⁻¹ * x⁻¹) * (y⁻¹ * x⁻¹) := by group
    _ = (y⁻¹ * x⁻¹) ^ 2 := by rw [sq]
    _ = (y * x) ^ 2 := by rw [h y x]
  simp only [sq]

lemma law3 (x y : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : (x * y)⁻¹ = y * x := by
  rw [h]
  simp only [mul_inv_rev, inv_inv]

lemma law4 (x y : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : (x * y) * (y * x) = 1 := by
  rw [← law3 x y h, mul_inv_cancel]

lemma law5 (x : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : x ^ 4 = 1 := by
  have h₁ := h x x
  rw [← mul_left_inj x, ← mul_left_inj x] at h₁
  simp at h₁
  symm
  calc 1
    _ = x * x * x * x := h₁.symm
    _ = (x * x) * (x * x) := by rw [mul_assoc]
    _ = (x ^ 2) * (x ^ 2) := by rw [sq]
    _ = x ^ (2 + 2) := Eq.symm (pow_add x 2 2)
    _ = (x ^ 4) := rfl

example (x : G) : x * x^3 = x^4 := by exact Eq.symm (pow_succ' x 3)

lemma law6 (x y : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : (x * y)⁻¹ = (x * y) ^ 3 := by
  symm
  rw [← mul_right_inj $ x * y, mul_inv_cancel]
  rw [← pow_succ' (x * y) 3]
  rw [law5 (x * y) h]

lemma law7 (x : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : (x⁻¹) ^ 2 = x ^ 2 := by
  rw [sq, sq]
  rw [h x x]

lemma law8 (x y : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : (y * x) ^ 2 = 1 := by
  set xy := x * y
  set yx := y * x

  have :=
  calc True
    _ ↔                             xy^2 = xy^2                        := by group
    _ ↔                          xy * xy = xy^2                        := by rw [sq]
    _ ↔                        xy * yx⁻¹ = xy^2                        := by rw [law3 _ _ h]
    _ ↔                 xy * yx⁻¹ * yx⁻¹ = xy^2 * yx⁻¹                 := by rw [← mul_left_inj yx⁻¹]
    _ ↔                 xy * yx⁻¹ * yx⁻¹ = xy^2 * xy                   := by rw [law3 _ _ h]
    _ ↔                    xy * (yx⁻¹)^2 = xy^2 * xy                   := by rw [mul_assoc, ← sq]
    _ ↔  (xy * (yx⁻¹)^2) * (xy^2 * xy)⁻¹ = (xy^2 * xy) * (xy^2 * xy)⁻¹ := by rw [mul_left_inj]
    _ ↔  (xy * (yx⁻¹)^2) * (xy^2 * xy)⁻¹ = 1                           := by rw [mul_inv_cancel]
    _ ↔    (xy * (yx)^2) * (xy^2 * xy)⁻¹ = 1                           := by rw [law7 _ h]
    _ ↔      (xy * (yx)^2) * (xy * xy^2) = 1                           := by rw [law3 _ _ h]
    _ ↔           (xy * (yx)^2) * (xy^3) = 1                           := by group
    _ ↔           (xy * (yx)^2) * (xy⁻¹) = 1                           := by rw [law6 _ _ h]
    _ ↔      (xy * (yx)^2) * (xy⁻¹) * xy = 1 * xy                      := by rw [mul_left_inj]
    _ ↔        xy * (yx)^2 * (xy⁻¹ * xy) = 1 * xy                      := by group
    _ ↔                      xy * (yx)^2 = xy                          := by rw [one_mul, inv_mul_cancel, mul_one]
    _ ↔             xy⁻¹ * (xy * (yx)^2) = xy⁻¹ * xy                   := by rw [mul_right_inj ]
    _ ↔             (xy⁻¹ * xy) * (yx)^2 = 1                           := by rw [←mul_assoc, inv_mul_cancel]
    _ ↔                           (yx)^2 = 1                           := by rw [inv_mul_cancel, one_mul]
  rwa [true_iff] at this

theorem T51 (x y : G) (h : ∀ a b : G, a * b = a⁻¹ * b⁻¹) : y * x = x * y := by
  set xy := x * y
  set yx := y * x

  have := calc True
    _ ↔            yx ^ 2 = 1         := by simp only [law8 _ _ h]
    _ ↔           yx * yx = 1         := by rw [sq]
    _ ↔  yx⁻¹ * (yx * yx) = yx⁻¹ * 1  := by rw [mul_right_inj]
    _ ↔  (yx⁻¹ * yx) * yx = yx⁻¹      := by rw [←mul_assoc, mul_one]
    _ ↔                yx = xy        := by rw [inv_mul_cancel, one_mul, law3 _ _ h]

  rwa [true_iff] at this

end P51


-- scrap.
namespace P51'
variable {G : Type} [Group G]

lemma pow_mul_pow_one (x y : G) (h : x * y = x⁻¹ * y⁻¹) : x ^ 2 * y ^ 2 = 1 := by
  have :=
  calc x * y = x⁻¹ * y⁻¹
    _ ↔ x * y * y = x⁻¹ * y⁻¹ * y := by rw [← mul_left_inj]
    _ ↔ x * (x * y * y) = x * (x⁻¹ * y⁻¹ * y) := by rw [← mul_right_inj]
    _ ↔ (x * x) * (y * y) = 1 := by group
    _ ↔ (x ^ 2) * (y ^ 2) = 1 := by simp only [pow_two]
  rwa [this] at h


lemma squares_commute (x y : G) (h : x * y = x⁻¹ * y⁻¹) : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
  symm
  have h₁ :=
  calc x ^ 2 * y ^ 2 = 1
    _ ↔ (x ^ 2 * y ^ 2) * y⁻¹ = 1 * y⁻¹ := by rw [mul_left_inj]
    _ ↔ x ^ 2 * y = y⁻¹ := by group
    _ ↔ x ^ 2 * y * y⁻¹ = y⁻¹ * y⁻¹ := by rw [mul_left_inj]
    _ ↔ x ^ 2 = y⁻¹ * y⁻¹ := by group
    _ ↔ y * x ^ 2 = y * (y⁻¹ * y⁻¹) := by rw [mul_right_inj]
    _ ↔ y * x ^ 2 = (y * y⁻¹) * y⁻¹ := by group
    _ ↔ y * x ^ 2 = y⁻¹ := by group
    _ ↔ y * (y * x ^ 2) = y * y⁻¹ := by rw [mul_right_inj]
    _ ↔ (y * y) * x ^ 2 = 1 := by group
    _ ↔ y ^ 2 * x ^ 2 = 1 := by simp [pow_two]

  rw [pow_mul_pow_one (h:=h)] at *
  simp_all only [true_iff]


lemma mul_inv_eq_inv_mul (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  have :=
  calc (1 : G)
    _ = y⁻¹ * y := by group
    _ = y⁻¹ * 1 * y := by group
    _ = y⁻¹ * (x⁻¹ * x) * y := by group
    _ = (y⁻¹ * x⁻¹) * (x * y) := by group
  rw [← mul_left_inj $ (x * y)⁻¹] at this
  conv at this => lhs; rw [one_mul]
  conv at this => rhs; rw [mul_assoc]; rhs;

  have h₁ :=
    calc x * y * (x * y)⁻¹
      _= (x * y) * (x * y)⁻¹ := rfl
      _= (x * y) * (x * y)⁻¹ := by simp
      _= 1 := by exact mul_inv_cancel (x * y)
  rw [h₁] at this

  calc (x * y)⁻¹
    _ = y⁻¹ * x⁻¹ * 1 := this
    _ = y⁻¹ * x⁻¹ := by group
end P51'
