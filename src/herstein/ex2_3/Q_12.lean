import algebra.group

variable {G: Type*}

-- mathlib's constructor for `group` asks only for a (two-sided) identity
-- alongside a left inverse. This exercise shows it is possible to produce
-- both of those things if given a right identity and a right inverse.
theorem Q_12 (G: Type*) (mul: G → G → G) (e: G) (y: G → G):
  (∀ a b c: G, (mul (mul a b) c) = (mul a (mul b c))) ∧
  (∀ a: G, mul a e = a) ∧
  (∀ a: G, mul a (y a) = e)
  → group G :=
λ ⟨h1, ⟨h2, h3⟩⟩, begin

  -- the right inverse is also a left inverse
  have h4: ∀ a: G, mul (y a) a = e, from λ a, calc
  mul (y a) a
    = mul (mul (y a) a) e                              : (h2 _).symm
... = mul (mul (y a) a) (mul (y a) (y (y a))) : by rw ←h3
... = mul (y a) (mul a (mul (y a) (y (y a)))) : h1 _ _ _
... = mul (y a) (mul (mul a (y a)) (y (y a))) : by rw h1
... = mul (y a) (mul e (y (y a)))                : by rw h3
... = mul (mul (y a) e) (y (y a))                : by rw ←h1
... = mul (y a) (y (y a))                        : by rw h2
... = e                                                   : h3 _,

  -- the right identity is also the left identity
  have h5: ∀ a: G, mul e a = a, from λ a, calc
  mul e a
    = mul (mul a (y a)) a : by rw h3
... = mul a (mul (y a) a) : h1 _ _ _
... = mul a e                : by rw h4
... = a                      : h2 _,

  -- we have now shown everything we need to
  -- synthesise an instance of group G:
  exact {
    mul := mul,
    mul_assoc := h1,
    one := e,
    one_mul := h5,
    mul_one := h2,
    inv := y,
    mul_left_inv := h4
  },
end


