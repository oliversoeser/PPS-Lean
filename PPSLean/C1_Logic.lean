import Mathlib.Data.Set.Basic

section

variable (α : Type)
variable (a b : Prop)

#check Set α

#check a ↔ b

theorem theorem_1_1 : (a → b) ↔ (¬a ∨ b) :=
  Iff.intro
    (fun (f : a → b) => sorry)
    (fun (h : ¬a ∨ b) => sorry)

theorem theorem_1_2 : (a → b) ↔ (¬b → ¬a) :=
  sorry



end
