-- Week 1: Chapter 2, The Reals

import Mathlib.Algebra.Field.Basic

-- Definition 2.1: Field
#check Field

#check add_comm
#check add_assoc
#check zero_add
#check add_neg_cancel

#check mul_comm
#check mul_assoc
#check one_mul
#check mul_inv_cancel
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
  sorry
theorem add_id_inv : x + y = 0 → x = -y :=
  sorry
theorem neg_neg_eq : -(-x) = x :=
  sorry

-- Proposition 2.2
theorem mul_cancel_left : x ≠ 0 → (x * y = x * z ↔ y = z) :=
  sorry
theorem mul_id_unique : x ≠ 0 → x * y = x → y = 1 :=
  sorry
theorem mul_id_inv : x ≠ 0 → x * y = 1 → y = x⁻¹ :=
  sorry
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
