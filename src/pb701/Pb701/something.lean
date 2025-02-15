



/-- Basic version of `norm_num` that does not call `simp`. -/
elab (name := normNum1) "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode mkNullNode loc (simpOnly := true) (useSimp := false)
