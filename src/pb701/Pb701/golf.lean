import Mathlib

universe u

variable (α : Type u)

class Thing (T : Type u) where
  protected thing_axiom_1 : ∀ a : T, sorry
  protected thing_axiom_2 : ∀ a : T, sorry

#check @Magma.AssocRel _ _ _ _ _


example (p : Prop) : p → p := by exact fun a ↦ a





-- A core theorem has terms that depend on one definition and can be proven
-- using only the axioms of the definition.

def core_theorem (t : Theorem) : t.Terms ∈ t.Definitions.axioms

-- A core theorem has terms that depend on one definition and can be proven
-- using only the axioms of the definition.

def outer_theorem (t : Theorem) :
