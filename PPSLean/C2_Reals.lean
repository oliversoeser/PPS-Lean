-- Week 1: Chapter 2, The Reals

import Mathlib.Algebra.Field.Basic

-- Definition 2.1: Field
#check add_comm
#check add_assoc
#check zero_add
#check add_neg_cancel

#check mul_comm
#check mul_assoc
#check one_mul
#check Field.mul_inv_cancel
#check mul_add

variable (F : Type*) [Field F]
variable (x y z : F)

-- Proposition 2.1
theorem add_cancel_left : x + y = x + z ↔ y = z :=
  Iff.intro
    (fun h : x + y = x + z => calc
    y = y + 0 := by rw [add_comm, zero_add]
    _ = y + (x + -x) := by rw [add_neg_cancel]
    _ = (y + x) + -x := by rw [add_assoc]
    _ = (x + y) + -x := by rw [add_comm x]
    _ = (x + z) + -x := by rw [h]
    _ = (z + x) + -x := by rw [add_comm z]
    _ = z + (x + -x) := by rw [add_assoc]
    _ = z + 0 := by rw [add_neg_cancel]
    _ = z := by rw [add_zero])
    (fun h => by rw [h])

theorem add_id_unique : x + y = x → y = 0 :=
  fun h₀ : x + y = x =>
    have h₁ : x + y = x + 0 := by rw [h₀, add_zero]
    (add_cancel_left F x y 0).mp h₁

theorem add_id_inv : x + y = 0 → x = -y :=
  fun h₀ : x + y = 0 =>
    have h₁ : y + x = y + -y := by rw [add_neg_cancel, add_comm]; exact h₀
    (add_cancel_left F y x (-y)).mp h₁

theorem neg_neg_eq : -(-x) = x :=
  have h₀ : -x + -(-x) = -x + x := by rw [add_comm (-x) x, add_neg_cancel, add_neg_cancel]
  (add_cancel_left F (-x) (-(-x)) x).mp h₀

-- Proposition 2.2
theorem mul_cancel_left : x ≠ 0 → (x * y = x * z ↔ y = z) :=
  fun h₀ =>
    Iff.intro
      (fun h₁ => calc
        y = y * 1 := by rw [mul_comm, one_mul]
        _ = y * (x * x⁻¹) := by rw [Field.mul_inv_cancel x h₀]
        _ = (y * x) * x⁻¹ := by rw [mul_assoc]
        _ = (x * y) * x⁻¹ := by rw [mul_comm x]
        _ = (x * z) * x⁻¹ := by rw [h₁]
        _ = z * (x * x⁻¹) := by rw [mul_comm x, mul_assoc]
        _ = z * 1 := by rw [Field.mul_inv_cancel x h₀]
        _ = z := by rw [mul_one])
      (fun h₁ => by rw [h₁])

theorem mul_id_unique : x ≠ 0 → x * y = x → y = 1 :=
  fun h₀ =>
    fun h₁ : x * y = x =>
      have h₂ : x * y = x * 1 := by rw [mul_comm x 1, one_mul, h₁]
      (mul_cancel_left F x y 1 h₀).mp h₂

theorem mul_id_inv : x ≠ 0 → x * y = 1 → y = x⁻¹ :=
  fun h₀ =>
    fun h₁ : x * y = 1 =>
      have h₂ : x * y = x * x⁻¹ := by rw [h₁, ← Field.mul_inv_cancel x h₀]
      (mul_cancel_left F x y x⁻¹ h₀).mp h₂

theorem inv_inv_eq : x ≠ 0 → (x⁻¹)⁻¹ = x :=
  sorry

-- Proposition 2.3
theorem zero_mul_eq_zero : 0 * x = 0 :=
  sorry
theorem nonzero_mul : x ≠ 0 ∧ y ≠ 0 → x * y ≠ 0 :=
  sorry
theorem neg_mul_eqs : -x * y = -(x * y) ∧ -(x * y) = x * -y :=
  sorry
theorem neg_mul_neg_eq_pos : -x * -y = x * y :=
  sorry

section

-- Archimedian property (assumed in this section)
end
