import algebra.group
import group_theory.subgroup

variables {G: Type*} {H K: set G}

theorem Q_01 [hG: group G] [hH: is_subgroup H] [hK: is_subgroup K]:
  is_subgroup (H ∩ K) := {

  inv_mem := λ a ha, ⟨
  is_subgroup.inv_mem ha.1,
  is_subgroup.inv_mem ha.2
  ⟩,

  one_mem := ⟨hH.one_mem, hK.one_mem⟩,

  mul_mem := λ a b ha hb, ⟨
  is_submonoid.mul_mem ha.1 hb.1,
  is_submonoid.mul_mem ha.2 hb.2,
  ⟩
}
