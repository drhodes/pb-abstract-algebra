


Yaël Dillies: def F (α : Type u) : Type u := Prod α α

creates an "equational lemma"
theorem F (α : Type u) : F α = Prod α α := rfl
Yaël Dillies: def h : Type u → Type u := fun α => Prod α α

instead creates the equational lemma
theorem h : h = fun α => Prod α α := rfl
