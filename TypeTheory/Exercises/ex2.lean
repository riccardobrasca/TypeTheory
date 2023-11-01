import TypeTheory.L5.ex

namespace N

section multiplication

def mul : N → N → N
| 0, a => 0
| succ n, a => mul n a + a

/- This activates the notation `a * b` for `mul a b`. -/
instance : Mul N := ⟨mul⟩

theorem zero_mul (a : N) : 0 * a = 0 := rfl

theorem succ_mul (a b : N) : succ a * b = a * b + b := rfl

theorem mul_zero (a : N) : a * 0 = 0 := by
  induction a with
  | zero => exact zero_mul _
  | _ d hd => rw [succ_mul, hd, add_zero]

theorem mul_succ (a b : N) : a * (succ b) = a * b + a := by
  induction a with
  | zero =>
    rw [zero_def, zero_mul, zero_mul, zero_add]
  | _ d hd =>
    rw [succ_mul, hd, succ_mul, add_succ, add_succ,
      add_assoc, add_comm d b, ← add_assoc]

theorem one_mul (a : N) : 1 * a = a := by
  rw [one_eq_succ_zero, succ_mul, zero_mul, zero_add]

theorem mul_one (a : N) : a * 1 = a := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

end multiplication

end N
