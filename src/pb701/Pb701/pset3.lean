import Mathlib
import Duper

namespace PSet3
-- page 15: ../media/book/aata-20220728.pdf

-- https://hrmacbeth.github.io/math2001/08_Functions.html#id24

-- A  B
-- ----
-- A  B
-- B  A

-- this instance is used in the `example` below
-- deriving instance Fintype for AlphaBet

-- example : ∀ f : AlphaBet → AlphaBet, Injective f → HasLeftInverse f := by
--   intro f hf
--   exact?

-- open Function


namespace alpha

namespace try1

inductive Alpha | A | B deriving DecidableEq
open Function Alpha

example : ∀ f : Alpha → Alpha, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  . -- show that `f` is surjective
    match ha : f A, hb : f B with
    | A, A =>
      have : A = B := by
        apply hf; rw [ha, hb]
      contradiction
    | B, B =>
      have : A = B := by
        apply hf; rw [ha, hb]
      contradiction
    | A, B =>
      intro y
      cases y
      · use A
      · use B
    | B, A =>
      intro b
      cases b
      · use B
      · use A
end try1


namespace try7

inductive Alpha | A | B deriving DecidableEq
open Function Alpha

example : ∀ f : Alpha → Alpha, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  . -- show that `f` is surjective
    intro c
    cases ha : f A <;> cases hb : f B

    · have : A = B := by
        apply hf
        rw [ha, hb]
      contradiction

    · cases c with
      | A => use A
      | B => use B

    · cases c with
      | A => use B
      | B => use A

    · have : A = B := by
        apply hf
        rw [hb, ha]
      simpa

end try7


namespace try8

inductive Alpha | A | B deriving DecidableEq
open Function Alpha

example : ∀ f : Alpha → Alpha, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  . -- show that `f` is surjective
    intro c
    cases ha : f A <;> cases hb : f B

    all_goals
      try cases c <;> tauto

    all_goals
      try
        have : A = B := by
          apply hf
          rw [ha, hb]
        contradiction

end try8


namespace try9

inductive Alpha | A | B deriving DecidableEq
open Function Alpha

example : ∀ f : Alpha → Alpha, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  . -- show that `f` is surjective
    intro c
    cases ha : f A <;> cases hb : f B

    all_goals try cases c <;> tauto

    all_goals try
      have : A = B := by
        apply hf
        rw [ha, hb]
      contradiction

end try9



namespace try2

example : ∀ f : AlphaBet → AlphaBet, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  · -- show that `f` is surjective
    obtain h | h := eq_or_ne (f A) (f B)
    · --
      have : A = B := by
        apply hf;
        exact h
      contradiction
    · --
      have : A ≠ B := by
        by_contra hc
        apply h
        aesop -- todo
      dsimp [Surjective]
      intro c
      unfold Injective at hf
      use c
      cases c with
      | A =>
        by_contra hc
        apply this



      | B => sorry

  -- match ha : f A, hb : f B with
  -- | A, A =>
  --   have : A = B
  --   apply hf; rw [ha, hb]
  --   contradiction
  -- | B, B =>
  --   have : A = B
  --   apply hf; rw [ha, hb]
  --   contradiction

  -- | A, B =>
  --   intro y
  --   cases y
  --   · use A
  --   · use B
  -- | B, A =>
  --   intro b
  --   cases b
  --   · use B
  --   · use A

end try2

end alpha




def Inverse {X Y : Type} (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id


namespace P19
open Function
-- Let f : A → B and g : B → C be invertible mappings; that is, mappings such
-- that f⁻¹ and g⁻¹ exist. Show that (g ∘ f )⁻¹ = f⁻¹ ∘ g⁻¹.

--variable
  -- (A B C : Type)
  -- (f : A → B)
  -- (g : B → C)
  -- (hf : HasLeftInverse f)
  -- (hg : HasRightInverse g)

variable
  {A B C : Type}
  {f : A → B}
  {g : B → C}
  {f_inv : B → A}
  {g_inv : C → B}
  (hf : LeftInverse f_inv f)
  (hg : RightInverse g_inv g)


example : (g ∘ f) = (g ∘ f) :=
  by intro x; simp [hf, hg]

end P19


namespace P23
-- Define a function on the real numbers by f(x) = (x + 1)/(x − 1).

-- What are the domain and range of f ? What is the inverse of f ?
-- Compute f ∘ f⁻¹ and f⁻¹ ∘ f .



end P23


namespace P25
-- Determine whether or not the following relations are equivalence relations on
-- the given set. If the relation is an equivalence relation, describe the
-- partition given by it. If the relation is not an equivalence relation, state
-- why it fails to be one.

-- (a) x ∼ y in R if x ≥ y
-- (b) m ∼ n in Z if mn > 0
-- (c) x ∼ y in R if |x − y| ≤ 4
-- (d) m ∼ n in Z if m ≡ n (mod 6)

end P25

end PSet3
