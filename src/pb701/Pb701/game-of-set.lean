import Mathlib



-- a valid family of matches. This construction does not specify a single
-- particular Match.




-- experiment with the game of set

inductive Count where | On | Tu | Sn
  deriving Repr, DecidableEq, BEq, Fintype

inductive Color where | Re | Gr | Pr
  deriving Repr, DecidableEq, BEq, Fintype

inductive Shade where | Cl | Ha | Fi
  deriving Repr, DecidableEq, BEq, Fintype

inductive Shape where | Sq | Pi | Di
  deriving Repr, DecidableEq, BEq, Fintype

@[ext]
structure Card where
  count : Count
  color : Color
  shade : Shade
  shape : Shape
  deriving Repr, DecidableEq, BEq, Fintype

open Count Color Shade Shape

@[simp]
def same {α : Type} (a b : Card) (sel : Card → α) : Prop :=
  (sel a) = (sel b)

@[simp]
lemma same_iff {α : Type} (a b : Card) (sel : Card → α) :
  same a b sel ↔ (sel a) = (sel b) := by rfl

@[simp]
def diff {α : Type} (a b : Card) (sel : Card → α) : Prop :=
  (sel a) ≠ (sel b)

@[simp]
lemma diff_iff {α : Type} (a b : Card) (sel : Card → α) :
  diff a b sel ↔ (sel a) ≠ (sel b) := by rfl

@[simp]
def all_same {α : Type} (a b c : Card) (s : Card → α) : Prop :=
  (same a b s) ∧ (same b c s) ∧ (same a c s)

@[simp]
lemma all_same_iff {α : Type} (a b c : Card) (s : Card → α) :
  all_same a b c s ↔ (same a b s) ∧ (same b c s) ∧ (same a c s) := by rfl

@[simp]
def all_diff {α : Type} (a b c : Card) (s : Card → α) : Prop :=
  (diff a b s) ∧ (diff b c s) ∧ (diff a c s)

@[simp]
lemma all_diff_iff {α : Type} (a b c : Card) (s : Card → α) :
  all_diff a b c s ↔ (diff a b s) ∧ (diff b c s) ∧ (diff a c s) := by rfl

@[simp]
def valid_select {α : Type} (a b c : Card) (s : Card → α) : Prop :=
  all_same a b c s ∨ all_diff a b c s

@[simp]
lemma valid_select_iff {α : Type} (a b c : Card) (s : Card → α) :
  valid_select a b c s ↔ all_same a b c s ∨ all_diff a b c s := by rfl

@[simp]
def valid_set (a b c : Card) :=
  valid_select a b c (Card.count) ∧ valid_select a b c (Card.color) ∧
  valid_select a b c (Card.shade) ∧ valid_select a b c (Card.shape)

@[simp]
lemma valid_set_iff (a b c : Card) : valid_set a b c ↔
  valid_select a b c (Card.count) ∧ valid_select a b c (Card.color) ∧
  valid_select a b c (Card.shade) ∧  valid_select a b c (Card.shape) := by rfl

@[simp] lemma same_count_of_eq (a b : Card) : a = b → a.count = b.count := congrArg Card.count
@[simp] lemma same_shape_of_eq (a b : Card) : a = b → a.shape = b.shape := congrArg Card.shape
@[simp] lemma same_shade_of_eq (a b : Card) : a = b → a.shade = b.shade := congrArg Card.shade
@[simp] lemma same_color_of_eq (a b : Card) : a = b → a.color = b.color := congrArg Card.color

@[simp]
lemma ne_iff_some_diff (a b : Card) : a ≠ b ↔
    a.count ≠ b.count ∨ a.color ≠ b.color ∨ a.shade ≠ b.shade ∨ a.shape ≠ b.shape := by
  constructor
  · contrapose; aesop
  · aesop

def exists_other_count (a b : Count) : ∃ c, c ≠ a ∧ c ≠ b := by decide +revert
def exists_other_color (a b : Color) : ∃ c, c ≠ a ∧ c ≠ b := by decide +revert
def exists_other_shade (a b : Shade) : ∃ s, s ≠ a ∧ s ≠ b := by decide +revert
def exists_other_shape (a b : Shape) : ∃ s, s ≠ a ∧ s ≠ b := by decide +revert

set_option maxRecDepth 2048
lemma other_card (a b : Card) : ∃ c, c ≠ a ∧ c ≠ b := by decide +revert

lemma exists_valid_count (a b : Count) : ∃ c, (a = b ↔ c = a ∧ c = b) ∧ (a ≠ b ↔ c ≠ a ∧ c ≠ b) := by decide +revert
lemma exists_valid_color (a b : Color) : ∃ c, (a = b ↔ c = a ∧ c = b) ∧ (a ≠ b ↔ c ≠ a ∧ c ≠ b) := by decide +revert
lemma exists_valid_shade (a b : Shade) : ∃ c, (a = b ↔ c = a ∧ c = b) ∧ (a ≠ b ↔ c ≠ a ∧ c ≠ b) := by decide +revert
lemma exists_valid_shape (a b : Shape) : ∃ c, (a = b ↔ c = a ∧ c = b) ∧ (a ≠ b ↔ c ≠ a ∧ c ≠ b) := by decide +revert

-- Highlander Principle,
theorem there_can_be_only_one : True := sorry

-- Weak Highlander Principle,
theorem there_exists_at_least_one (a b : Card) (h : a ≠ b) : ∃ c, c ≠ a → c ≠ b → valid_set a b c := by
  obtain ⟨count, ⟨hcount₁, hcount₂⟩⟩ := exists_valid_count a.count b.count
  obtain ⟨color, ⟨hcolor₁, hcolor₂⟩⟩ := exists_valid_color a.color b.color
  obtain ⟨shade, ⟨hshade₁, hshade₂⟩⟩ := exists_valid_shade a.shade b.shade
  obtain ⟨shape, ⟨hshape₁, hshape₂⟩⟩ := exists_valid_shape a.shape b.shape

  use (Card.mk count color shade shape)
  simp
  reduce
  intro h₁ h₂
  refine ⟨?_,?_,?_,?_⟩
  · --
    cases h₁ <;> cases h₂
    · right
      refine ⟨?_,?_,?_⟩
      · aesop
      repeat {
        · intro h
          symm at h
          contradiction
      }
    · --
      reduce at *
      right
      constructor
      · exact hcount₂.left
      · done

    · done
    · done
    --
  · done
  · done
  · done



-- In the game of Set, players try to find Sets. However the word "Set" is
-- overloaded so instead of the term "Set" this document will use the term
-- "Match" to mean three cards that satisify the properties of the game.

@[match_pattern]
inductive Col where
  | L -- left column
  | C -- center column
  | R -- right column
  deriving Repr, DecidableEq, BEq, Fintype
open Col

@[match_pattern]
inductive Layer where
  | pipe : (src tgt : Col) → Layer
  | spray : (src : Col) → Layer
  | join : (tgt : Col) → Layer
  | swap : (tgt : Col) → Layer
  deriving Repr, DecidableEq, BEq, Fintype
open Layer

@[simp]
def valid_layer_pair (l₁ l₂ : Layer) :=
  match (l₁, l₂) with
  | (pipe _ x, pipe y _) => x = y
  | (pipe _ x, spray y) => x = y
  | (pipe _ _, _) => False
  --
  | (spray _, pipe _ _) => False
  | (spray _, spray _) => False
  | (spray _, _) => True
  --
  | (join x, pipe y _) => x = y
  | (join x, spray y) => x = y
  | (join _, _) => False
  --
  | (swap _, pipe _ _) => False
  | (swap _, join _) => False
  | (swap _, _) => True

example : valid_layer_pair (pipe L L) (pipe L L) := rfl
example : valid_layer_pair (pipe R L) (pipe L R) := rfl
example : valid_layer_pair (pipe R L) (spray L) := rfl
example : valid_layer_pair (pipe C C) (spray C) := rfl
example : valid_layer_pair (spray C) (join C) := by simp

@[simp]
def not_all_pipes : Layer → Layer → Layer → Prop
  | pipe _ _, pipe _ _, pipe _ _ => False
  | _, _, _ => True

@[simp]
def valid_family (l₁ l₂ l₃ : Layer) : Prop :=
  valid_layer_pair l₁ l₂ ∧ valid_layer_pair l₂ l₃ ∧ not_all_pipes l₁ l₂ l₃

example : valid_family (pipe C L) (pipe L R) (spray R) := by simp


structure MatchFamily where
  l₁ : Layer
  l₂ : Layer
  l₃ : Layer
  h : valid_family l₁ l₂ l₃

-- def enumerate_family (fam : MatchFamily) : List Card :=
--   -- holy crap.
--   match l₁ with
--   | pipe num _ => [Card.mk num]
--   | spray num => [Card.mk num]
--   | join col => [
--       Card.mk On,
--       Card.mk Tu,
--       Card.mk San,
--       ]
--   | swap : (tgt : Col) → Layer






--example (a b : Card) :


-- type uniqCount

-- @[simp]
-- def build_count (a b : Count) : Count :=
--   match hm : (a, b) with
--     | (On, Tu) => Sn | (Tu, On) => Sn
--     | (On, Sn) => Tu | (Sn, On) => Tu
--     | (Tu, Sn) => On | (Sn, Tu) => On
--     | _ => a

-- -- example (a b : Count) (h : a ≠ b) : build_count ≠ a




-- @[simp]
-- def build_color (a b : Color) : Color :=
--   match (a, b) with
--   | (Re, Pr) => Gr | (Pr, Re) => Gr
--   | (Re, Gr) => Pr | (Gr, Re) => Pr
--   | (Pr, Gr) => Re | (Gr, Pr) => Re
--   | _ => a

-- @[simp]
-- def build_shade (a b : Shade) : Shade :=
--   match (a, b) with
--   | (Cl, Ha) => Fi | (Ha, Cl) => Fi
--   | (Cl, Fi) => Ha | (Fi, Cl) => Ha
--   | (Ha, Fi) => Cl | (Fi, Ha) => Cl
--   | _ => a

-- @[simp]
-- def build_shape (a b : Shape) : Shape :=
--   match (a, b) with
--   | (Sq, Pi) => Di | (Pi, Sq) => Di
--   | (Sq, Di) => Pi | (Di, Sq) => Pi
--   | (Pi, Di) => Sq | (Di, Pi) => Sq
--   | _ => a


-- @[simp]
-- def build_card (a b : Card) :=
--   Card.mk (build_count a.count b.count) (build_color a.color b.color)
--           (build_shade a.shade b.shade) (build_shape a.shape b.shape)


-- -- Weak Highlander Principle,
-- example (a b : Card) (h : a ≠ b) : ∃ c, c ≠ a → c ≠ b → valid_set a b c := by
--   exists (build_card a b)
--   intro h₁ h₂
--   refine ⟨?_,?_,?_,?_⟩
--   · --
--     rw [all_same_or_diff_iff]
--     revert h₁
--     contrapose
--     simp only [all_same, all_diff] at *
--     push_neg
--     rintro ⟨h₁, h₂⟩






--   · done
--   · done
--   · done

-- -- Highlander Principle,
-- theorem there_can_be_only_one : ∀ a b, a ≠ b → ∃! c, valid_set a b c := by
--   intro a b hab
--   constructor
--   · constructor
--     · sorry
--     · done
--   · done
