import algebra.group algebra.group_power

variables A: Type*

theorem Q_02 (a b: A) [comm_group A]:
  ∀ n: ℕ, (a * b) ^ n = a ^ n * b ^ n
| 0 :=
  calc (a * b) ^ 0
      = 1 : by rw pow_zero
  ... = 1 * 1                 : (mul_one 1).symm
  ... = (a ^ 0) * (b ^ 0)     : by rw [pow_zero, pow_zero]
| (k + 1) :=
  calc (a * b) ^ (k + 1)
      = a * b * (a * b) ^ k       : pow_succ (a * b) k
  ... = b * a * (a * b) ^ k       : by rw mul_comm a b
  ... = b * a * (a ^ k * b ^ k)   : by rw (Q_02 k)
  ... = b * (a * a ^ k) * b ^ k   : by rw [← mul_assoc, mul_assoc b a (a ^ k)]
  ... = b * a ^ (k + 1) * b ^ k   : by rw pow_succ
  ... = a ^ (k + 1) * (b * b ^ k) : by rw [mul_comm b (a ^ (k + 1)), mul_assoc]
  ... = a ^ (k + 1) * b ^ (k + 1) : by rw [←pow_succ]
