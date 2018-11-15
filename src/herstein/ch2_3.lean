import algebra.group algebra.group_power

universe u
variables {A G: Type u}

-- Lemma 2.3.1: If G is a group, then
-- a. The identity element of G is unique.
-- b. Every a ∈ G has a unique inverse in G.
-- c. For every a ∈ G, (a⁻¹)⁻¹ = a.
-- d. For all a, b ∈ G, (a * b)⁻¹ = b⁻¹ * a ⁻¹

lemma L2_3_1a (e f: G) [group G]:
  (∀ a: G, a = a * e) ∧
  (∀ a: G, a = e * a) ∧
  (∀ a: G, a = a * f) ∧
  (∀ a: G, a = f * a) → e = f :=
λ ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩, eq.trans (h3 e) (h2 f).symm

-- now justified: use of group.one G to extract unique identity of G,
-- and the notation 1 for group.one G.

lemma L2_3_1b (a g h: G) [group G]:
  a * g = 1 ∧ g * a = 1 ∧
  a * h = 1 ∧ h * a = 1 → g = h :=
λ ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩, calc
  g = g * 1       : (mul_one g).symm
... = g * (a * h) : h3 ▸ ⟨g * (a * h)⟩
... = (g * a) * h : (mul_assoc g a h).symm
... = 1 * h       : h2 ▸ ⟨(g * a) * h⟩
... = h           : (one_mul h)

-- now justified: use of group.inv and notation a⁻¹ for the inverse of a.

lemma L2_3_1b₁ (a b c: G) [group G]:
  a * b = a * c → b = c := λ h, calc
  b   = 1 * b       : (one_mul b).symm
  ... = a⁻¹ * a * b : by rw inv_mul_self
  ... = a⁻¹ * a * c : by rw [mul_assoc, h, ←mul_assoc]
  ... = 1 * c       : by rw inv_mul_self
  ... = c           : one_mul c



lemma L2_3_1c (a: G) [group G]: (a⁻¹)⁻¹ = a :=
eq.symm $ calc a
    = 1 * a               : (one_mul _).symm
... = (a⁻¹)⁻¹ * a⁻¹ * a   : by rw ←inv_mul_self
... = (a⁻¹)⁻¹ * (a⁻¹ * a) : by rw mul_assoc
... = (a⁻¹)⁻¹ * 1         : by rw inv_mul_self
... = (a⁻¹)⁻¹             : mul_one _



-- a group is abelian if its multiplication is commutative
def abelian (G: Type u) [group G]: Prop := ∀ a b: G, a * b = b * a



theorem Q2_3_2 (a b: A) [comm_group A]:
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
  ... = b * a * (a ^ k * b ^ k)   : by rw (Q2_3_2 k)
  ... = b * (a * a ^ k) * b ^ k   : by rw [← mul_assoc, mul_assoc b a (a ^ k)]
  ... = b * a ^ (k + 1) * b ^ k   : by rw pow_succ
  ... = a ^ (k + 1) * (b * b ^ k) : by rw [mul_comm b (a ^ (k + 1)), mul_assoc]
  ... = a ^ (k + 1) * b ^ (k + 1) : by rw [←pow_succ]



theorem Q2_3_3 [group G]:
  (∀ a b: G, (a * b) ^ 2 = a ^ 2 * b ^ 2)
  → (abelian G) := λ h a b, begin
  have t, from calc a * (a * b) * b
    = a * a * (b * b)         : by rw [←mul_assoc, mul_assoc]
... = a * a ^ 1 * (b * b ^ 1) : by rw [pow_one, pow_one]
... = a ^ 2 * b ^ 2           : by rw [←pow_succ, ←pow_succ]
... = (a * b) ^ 2             : (h a b).symm
... = a * b * (a * b)         : by rw [pow_succ, pow_one]
... = a * (b * a) * b         : by rw [←mul_assoc, ←mul_assoc],

  exact mul_left_cancel (mul_right_cancel t),
end


-- if (a * b) ^ n = a ^ n * b ^ n for three consecutive integers, G is abelian.
-- the `rw`s  should really be re-written in calc so that it's human-readable.
def Q2_3_4_h (G: Type u) [group G] (k: ℕ): Prop :=
  ∀ a b: G, (a * b) ^ k = a ^ k * b ^ k

lemma Q2_3_4a [group G]: ∀ n: ℕ, ∀ a b: G,
  (a * b) ^ (n + 1) = a * (b * a) ^ n * b
| 0 :=
  λ a b, by rw [ zero_add, pow_one, pow_zero, mul_one ]
| (nat.succ r) :=
  λ a b, by rw [ pow_succ, Q2_3_4a, pow_succ,
                 ←mul_assoc, ←mul_assoc,
                 ←mul_assoc, ←mul_assoc ]

lemma Q2_3_4b [group G]: ∀ n: ℕ,
  (Q2_3_4_h G n) ∧ (Q2_3_4_h G (n + 1))
  → (∀ a b: G, (a * b) ^ n = (b * a) ^ n)
| 0 :=
  λ ⟨h1, h2⟩ a b, by rw [ pow_zero, pow_zero ]
| (nat.succ r) :=
  λ ⟨h1, h2⟩ a b,
  let h1' := h1 a b in
  let h2' := h2 a b in
  begin
    rw [
      Q2_3_4a,
      pow_succ a (nat.succ r),
      pow_succ' b (nat.succ r),
      ←mul_assoc, mul_assoc a _ (b ^ nat.succ r),
      ←h1
    ] at h2',

    exact mul_left_cancel (mul_right_cancel h2'.symm)
  end

theorem Q2_3_4 [group G] (n: ℕ):
  (Q2_3_4_h G n) ∧ (Q2_3_4_h G (n + 1)) ∧ (Q2_3_4_h G (n + 2))
  → abelian G :=
λ ⟨h1, ⟨h2, h3⟩⟩ a b, begin
  have t0, from Q2_3_4b n ⟨h1, h2⟩,
  have t1, from Q2_3_4b (n + 1) ⟨h2, h3⟩ a b,
  rw [ pow_succ, pow_succ, Q2_3_4b n ⟨h1, h2⟩ ] at t1,
  exact mul_right_cancel t1,
end



theorem Q2_3_10 [group G]:
  (∀ a: G, a⁻¹ = a) →
  (∀ a b: G, a * b = b * a) :=
λ h a b, mul_left_cancel (mul_right_cancel
(calc a * (a * b) * b
    = a * (a⁻¹ * b⁻¹) * b : by rw [h, h]
... = a * (b * a)⁻¹ * b   : by rw [←mul_inv_rev]
... = a * (b * a) * b     : by rw h ))



-- mathlib's constructor for `group` asks only for a (two-sided) identity
-- alongside a left inverse. This exercise shows it is possible to produce
-- both of those things if given a right identity and a right inverse.
theorem Q2_3_12 (G: Type u) (mul: G → G → G) (e: G) (rinv: G → G):
  (∀ a b c: G, (mul (mul a b) c) = (mul a (mul b c))) ∧
  (∀ a: G, mul a e = a) ∧
  (∀ a: G, mul a (rinv a) = e)
  → group G :=
λ ⟨h1, ⟨h2, h3⟩⟩, begin

  -- the right inverse is also a left inverse
  have h4: ∀ a: G, mul (rinv a) a = e, from λ a, calc
  mul (rinv a) a
    = mul (mul (rinv a) a) e                              : (h2 _).symm
... = mul (mul (rinv a) a) (mul (rinv a) (rinv (rinv a))) : by rw ←h3
... = mul (rinv a) (mul a (mul (rinv a) (rinv (rinv a)))) : h1 _ _ _
... = mul (rinv a) (mul (mul a (rinv a)) (rinv (rinv a))) : by rw h1
... = mul (rinv a) (mul e (rinv (rinv a)))                : by rw h3
... = mul (mul (rinv a) e) (rinv (rinv a))                : by rw ←h1
... = mul (rinv a) (rinv (rinv a))                        : by rw h2
... = e                                                   : h3 _,

  -- the right identity is also the left identity
  have h5: ∀ a: G, mul e a = a, from λ a, calc
  mul e a
    = mul (mul a (rinv a)) a : by rw h3
... = mul a (mul (rinv a) a) : h1 _ _ _
... = mul a e : sorry
... = a : sorry,

  exact group.mk mul h1 e h5 h2 rinv h4,
end


