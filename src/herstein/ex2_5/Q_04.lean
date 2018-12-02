import algebra.group
import group_theory.subgroup

variables {G: Type*} {H: set G} {a: G}

theorem Q_04a [hG: group G] [hH: is_subgroup H]:
  is_subgroup ((λ h, a * h * a⁻¹) '' H) := {

  inv_mem := λ g ⟨h, ⟨hH, ha⟩⟩, begin

    -- inverse of aha⁻¹ is ah⁻¹a⁻¹ ...
    have inv_g: g⁻¹ = a * h⁻¹ * a⁻¹,
    from ha ▸ calc (a * h * a⁻¹)⁻¹
    = (a⁻¹)⁻¹ * h⁻¹ * a⁻¹ : by rw [mul_inv_rev, mul_inv_rev, ←mul_assoc]
... = a * h⁻¹ * a⁻¹       : by rw inv_inv,

    -- ... and ah⁻¹a⁻¹ is in aHa⁻¹.
    have t: a * h⁻¹ * a⁻¹ ∈ ((λ h, a * h * a⁻¹) '' H),
    from ⟨h⁻¹, ⟨is_subgroup.inv_mem hH, rfl⟩⟩,

    exact inv_g.symm ▸ t,
  end,

  -- the identity is in aHa⁻¹: 1 = a1a⁻¹.
  one_mem := ⟨1, ⟨
    hH.one_mem,
    calc a * 1 * a⁻¹ = 1: by rw [mul_one, mul_right_inv a] ⟩⟩,

  -- multiplication in aHa⁻¹ is closed because ah₁a⁻¹ * ah₂a⁻¹ = ah₁h₂a⁻¹.
  mul_mem := λ g₁ g₂ ⟨h₁, ⟨hh₁, hg₁⟩⟩ ⟨h₂, ⟨hh₂, hg₂⟩⟩, ⟨h₁ * h₂, ⟨

  is_submonoid.mul_mem hh₁ hh₂,

  hg₁ ▸ hg₂ ▸ calc a * (h₁ * h₂) * a⁻¹
    = a * h₁ * 1 * (h₂ * a⁻¹)         : by rw [←mul_assoc, mul_assoc, mul_one]
... = a * h₁ * (a⁻¹ * a) * (h₂ * a⁻¹) : by rw mul_left_inv
... = (a * h₁ * a⁻¹) * a * (h₂ * a⁻¹) : by rw ←(mul_assoc (a * h₁) a⁻¹ a)
... = (a * h₁ * a⁻¹) * (a * h₂ * a⁻¹) : by rw [mul_assoc, mul_assoc a h₂ a⁻¹],
  ⟩⟩,
}
