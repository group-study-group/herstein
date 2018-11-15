import algebra.group algebra.group_power

variables {G: Type*}

-- if (a * b) ^ n = a ^ n * b ^ n for three consecutive integers, G is abelian.
-- (the `rw`s  should really be re-written in calc so that it's human-readable.)
def Q_04h (G: Type*) [group G] (k: ℕ): Prop :=
  ∀ a b: G, (a * b) ^ k = a ^ k * b ^ k

lemma Q_04a [group G]: ∀ n: ℕ, ∀ a b: G,
  (a * b) ^ (n + 1) = a * (b * a) ^ n * b
| 0 :=
  λ a b, by rw [ zero_add, pow_one, pow_zero, mul_one ]
| (nat.succ r) :=
  λ a b, by rw [ pow_succ, Q_04a, pow_succ,
                 ←mul_assoc, ←mul_assoc,
                 ←mul_assoc, ←mul_assoc ]

lemma Q_04b [group G]: ∀ n: ℕ,
  (Q_04h G n) ∧ (Q_04h G (n + 1))
  → (∀ a b: G, (a * b) ^ n = (b * a) ^ n)
| 0 :=
  λ ⟨h1, h2⟩ a b, by rw [ pow_zero, pow_zero ]
| (nat.succ r) :=
  λ ⟨h1, h2⟩ a b,
  let h1' := h1 a b in
  let h2' := h2 a b in
  begin
    rw [
      Q_04a,
      pow_succ a (nat.succ r),
      pow_succ' b (nat.succ r),
      ←mul_assoc, mul_assoc a _ (b ^ nat.succ r),
      ←h1
    ] at h2',

    exact mul_left_cancel (mul_right_cancel h2'.symm)
  end

theorem Q_04 [hG: group G] (n: ℕ):
  (Q_04h G n) ∧ (Q_04h G (n + 1)) ∧ (Q_04h G (n + 2))
  → comm_group G :=
λ ⟨h1, ⟨h2, h3⟩⟩, {
  mul_comm := λ a b, begin
    have t0, from Q_04b n ⟨h1, h2⟩,
    have t1, from Q_04b (n + 1) ⟨h2, h3⟩ a b,
    rw [ pow_succ, pow_succ, Q_04b n ⟨h1, h2⟩ ] at t1,
    exact mul_right_cancel t1,
  end,
  .. hG
}



