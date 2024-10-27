-- Week 1: Chapter 1, Logic

import Mathlib.Data.Set.Basic

variable (a b : Prop)

-- Theorem 1.1
theorem imp_iff_or : (a → b) ↔ (¬a ∨ b) :=
  Iff.intro
    (fun (f : a → b) => sorry)
    (fun (h : ¬a ∨ b) => sorry)

-- Theorem 1.2
theorem contrapos : (a → b) ↔ (¬b → ¬a) :=
  sorry

-- Theorem 1.3
theorem not_or_iff : ¬(a ∨ b) ↔ ¬a ∨ ¬b :=
  sorry
