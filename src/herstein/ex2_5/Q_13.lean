import algebra.group group_theory.subgroup

variables {G: Type*}

def normaliser (a: G) [group G]: set G :=
  { x: G | a * x = x * a }

theorem Q_13 (a: G) [group G]:
  is_subgroup (normaliser a) := {
  one_mem := calc
    a * 1 = 1 * a: by rw [mul_one, one_mul],

  mul_mem := λ g h hg hh, calc
    a * (g * h) = (a * g) * h  : (mul_assoc _ _ _).symm
    ...         = (g * a) * h  : hg ▸ rfl
    ...         =  g * (a * h) : mul_assoc _ _ _
    ...         =  g * (h * a) : hh ▸ rfl
    ...         = (g * h) * a  : (mul_assoc _ _ _).symm,

  inv_mem := λ g hg, calc
    a * g⁻¹ = (g⁻¹ * g) * (a * g⁻¹)  : (mul_left_inv g).symm ▸ (one_mul _).symm
    ...     =  g⁻¹ * (g * a) * g⁻¹   : by rw [ ←mul_assoc, mul_assoc g⁻¹ ]
    ...     =  g⁻¹ * (a * g) * g⁻¹   : hg ▸ rfl
    ...     = (g⁻¹ * a) * g  * g⁻¹   : mul_assoc g⁻¹ a g ▸ rfl
    ...     =  g⁻¹ * a               : mul_inv_cancel_right (g⁻¹ * a) g
}
