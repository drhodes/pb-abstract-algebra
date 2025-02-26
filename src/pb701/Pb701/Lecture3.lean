import Lean
import Mathlib

namespace Lecture3
open Function


-----------------------------------------------------------------
namespace Definition_1_2_23
open Function

variable {X Y : Type}

def Inverse (f : X → Y) (g : Y → X) : Prop :=
  LeftInverse f g ∧ RightInverse f g

end Definition_1_2_23
open Definition_1_2_23

-----------------------------------------------------------------
namespace Example_1_24_1
open Function

def f (x : ℝ) := x

example : Inverse f f := by
  constructor
  all_goals intro x; dsimp [f]

noncomputable def g (x : ℝ) := 2 * x
noncomputable def g' (x : ℝ) := (1 / 2) * x

example : Inverse g g' := by
  constructor
  all_goals intro x; simp [g, g']

end Example_1_24_1


namespace Example_1_24_1_4
open Function

noncomputable def f (x : ℝ) := x.rpow 3
noncomputable def f' (x : ℝ) := x.rpow (1/3)


end Example_1_24_1_4


variable (F : Prop → Prop → Prop)

example : (∀ p, (p → ∀ q, F p q)) ↔ (∀ p, (∀ q, p → F p q)) := by
  constructor
  · tauto
  · tauto

variable (G : Prop → Prop)
variable (t : Prop)

-- def CondLeftInverse (cond : α → Prop) (g : β → α) (f : α → β) : Prop :=
--   ∀ y, (cond y) → ∀ x, g (f y) = y

noncomputable def g (x : ℝ) := 2 * x
noncomputable def g' (x : ℝ) := (1 / 2) * x

namespace Example_1_24_1_3

open Set

theorem exp.mapsTo_pos : MapsTo Real.exp univ (Ioi 0) := by
  simp_all only [mapsTo_univ_iff, mem_Ioi]
  apply Real.exp_pos

theorem log.mapsTo_pos : MapsTo Real.log (Ioi 0) univ := by
  intro x
  norm_num

lemma lft_inv : LeftInverse (log.mapsTo_pos.restrict) (exp.mapsTo_pos.restrict)  := by
  intro x
  ext
  simp_all only [MapsTo.val_restrict_apply, Real.log_exp]

lemma rht_inv : RightInverse (log.mapsTo_pos.restrict) (exp.mapsTo_pos.restrict) := by
  intro x
  ext
  simp_all only [Set.MapsTo.val_restrict_apply]
  obtain ⟨_, hx⟩ := x
  simp_all only [Set.mem_Ioi]
  refine Real.exp_log hx

example : Inverse (log.mapsTo_pos.restrict) (exp.mapsTo_pos.restrict) := by
  refine ⟨lft_inv, rht_inv⟩

end Example_1_24_1_3

-----------------------------------------------------------------------------
-- The easier way.

-- Mathlib.Data.Set.Operations

namespace Example_1_24_1_3_easier
open Set Real

lemma lft_inv : LeftInvOn Real.log Real.exp (Ioi 0) := by
  simp [LeftInvOn]

lemma rht_inv : RightInvOn Real.log Real.exp (Ioi 0) := by
  apply Real.exp_log

example : InvOn log exp (Ioi 0) (Ioi 0) := by
  refine ⟨lft_inv, rht_inv⟩


end Example_1_24_1_3_easier
end Lecture3
