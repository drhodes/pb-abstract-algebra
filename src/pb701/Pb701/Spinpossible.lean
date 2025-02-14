import Mathlib

namespace Spinpossible

inductive Num | N1 | N2 | N3 | N4 | N5 | N6 | N7 | N8 | N9

inductive Piece
  | Up : Num → Piece
  | Dn : Num → Piece

def Board := Matrix ℕ ℕ Piece

variable {G : Type}

example [Group G] (a b : G) : a * b = a * b := by exact rfl


end Spinpossible
