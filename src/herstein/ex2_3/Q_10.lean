import algebra.group

variable {G: Type*}

theorem Q_10 [group G]:
  (∀ a: G, a⁻¹ = a) →
  (∀ a b: G, a * b = b * a) :=
λ h a b, mul_left_cancel (mul_right_cancel $
calc a * (a * b) * b
    = a * (a⁻¹ * b⁻¹) * b : by rw [h, h]
... = a * (b * a)⁻¹ * b   : by rw [←mul_inv_rev]
... = a * (b * a) * b     : by rw h )
