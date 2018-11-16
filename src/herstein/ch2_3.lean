import algebra.group algebra.group_power

universe u
variables {A G: Type u}

-- Theorems & lemmas from the body text of chapter 2.3

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

-- left cancellation
lemma L2_3_2₁ (a u w: G) [group G]:
  a * u = a * w → u = w :=
λ h, calc u
    = 1 * u         : (one_mul _).symm
... = a⁻¹ * a * u   : by rw ←inv_mul_self
... = a⁻¹ * (a * u) : mul_assoc _ _ _
... = a⁻¹ * (a * w) : by rw h
... = a⁻¹ * a * w   : (mul_assoc _ _ _).symm
... = 1 * w         : by rw inv_mul_self
... = w             : by rw one_mul



-- right cancellation: similarly
lemma L2_3_2₂ (a u w: G) [group G]:
  u * a = w * a → u = w :=
λ h, calc u
    = u * (a * a⁻¹) : (mul_right_inv a).symm ▸ (mul_one u).symm
... = w * (a * a⁻¹) : by rw [ ←mul_assoc, h, mul_assoc ]
... = w             : by rw [ mul_right_inv, mul_one ]
