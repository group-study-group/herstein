import algebra.group algebra.group_power

variables {G: Type*}

theorem Q_03 [hG: group G]:
  (∀ a b: G, (a * b) ^ 2 = a ^ 2 * b ^ 2) → comm_group G :=
λ h, begin

  have lem: ∀ a b: G, a * (a * b) * b = a * (b * a) * b,
    from λ a b, calc a * (a * b) * b
    = a * a * (b * b)         : by rw [←mul_assoc, mul_assoc]
... = a * a ^ 1 * (b * b ^ 1) : by rw [pow_one, pow_one]
... = a ^ 2 * b ^ 2           : by rw [←pow_succ, ←pow_succ]
... = (a * b) ^ 2             : (h a b).symm
... = a * b * (a * b)         : by rw [pow_succ, pow_one]
... = a * (b * a) * b         : by rw [←mul_assoc, ←mul_assoc],

  have comm: ∀ a b: G, a * b = b * a,
  from λ a b, mul_left_cancel (mul_right_cancel (lem a b)),

  -- G is a group, together with comm, show that
  -- G is an abelian group:
  exact { mul_comm := comm, .. hG },
end
