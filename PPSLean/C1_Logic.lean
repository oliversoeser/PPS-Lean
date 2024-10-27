-- Week 1: Chapter 1, Logic

variable (a b : Prop)

#check Or.intro_left
#check Or.intro_right
#check Classical.byCases
#check Or.elim

-- Theorem 1.1
theorem imp_iff_or : (a → b) ↔ (¬a ∨ b) :=
  Iff.intro
    (fun (h₀ : a → b) => Classical.byCases
      (fun (h₁ : a) => Or.inr (h₀ h₁))
      (fun (h₂ : ¬a) => Or.inl h₂))
    (fun (h₀ : ¬a ∨ b) => Or.elim h₀
      (fun (h₁ : ¬a) => fun (h₂ : a) => absurd h₂ h₁)
      (fun b => fun _ => b))

-- Theorem 1.2
theorem contrapos : (a → b) ↔ (¬b → ¬a) :=
  Iff.intro
    (fun (h₀ : a → b) => Classical.byCases
      (fun (h₁ : a) => fun (h₂ : ¬b) => absurd (h₀ h₁) h₂)
      (fun (h₁ : ¬a) => fun _ => h₁))
    (fun (h₀ : ¬b → ¬a) => Classical.byCases
      (fun (h₁ : b) => fun _ => h₁)
      (fun (h₁ : ¬b) => fun (h₂ : a) => absurd h₂ (h₀ h₁)))

-- Theorem 1.3
theorem not_or_iff : ¬(a ∨ b) ↔ ¬a ∧ ¬b :=
  Iff.intro
    sorry
    sorry
