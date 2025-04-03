import Lean.Meta.Diagnostics
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Refl
import Lean.Elab.Binders
import Lean.Elab.Open
import Lean.Elab.Eval
import Lean.Elab.SetOption
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Do

namespace Lean.Elab.Tactic
open Meta
open Parser.Tactic


@[builtin_tactic «fail»] def evalHW : Tactic := fun _ => do
  let goals ← getGoals
  let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
  throwError "tactic 'fail' failed\n{goalsMsg}"


example : True := by
  fail "hello world"
