import algebra.group algebra.group_power

variables {G: Type*} (a b : G)

@[symm] theorem gpow_add' {G : Type*} [group G] (a : G) (i : ℤ): a^(i + 1) = a * a^i :=
by rw [add_comm, gpow_add]; simp

@[symm] theorem gpow_add'' {G : Type*} [group G] (a : G) (i : ℤ): a^(i + 1) = a^i * a :=
by rw [gpow_add]; simp

def Q04H {G : Type*} [group G] (a b : G) (i : ℤ): Prop := 
(a * b)^i = a^i * b^i

theorem Q04Alt [group G] 
(H : ∀ a b : G, 
∃ i : ℤ, (Q04H a b i) ∧ (Q04H a b (i + 1)) ∧ (Q04H a b (i + 1 + 1)) ) :
∀ a b : G, a * b = b * a := λ a b : G, 
exists.elim (H a b)
(λ i Hi, 
have H1 : b * a^i = a^i * b, from 
    have H10 : (a * b)^(i + 1) = a^(i + 1) * b^(i + 1), from Hi.2.1,
    have H11 : (a*b) * (a*b)^i = (a * a^i) * (b * b^i), 
        by {rw [(gpow_add' (a*b) i).symm, (gpow_add' a i).symm, (gpow_add' b i).symm], exact H10}, 
    have H12 : a * ( b * (a*b)^i) = a * (a^i * (b * b^i)), 
        by {rw [mul_assoc, mul_assoc] at H11, exact H11}, 
    have H13 : b * (a*b)^i = a^i * (b * b^i), from mul_left_cancel H12, 
    have H14 : b * (a^i * b^i) = a^i * (b * b^i), from Hi.1 ▸ H13, 
    have H15 : b * a^i * b^i = a^i * b * b^i, from by {rw [mul_assoc, mul_assoc], exact H14}, 
(mul_right_inj (b^i)).mp H15, 

show a * b = b * a, from 
    have H20 : a * b * (a * b)^(i+1) =  a * a^(i+1) * (b * b^(i+1)), 
        by {rw [(gpow_add' (a*b) (i+1)).symm, (gpow_add' a (i+1)).symm, (gpow_add' b (i+1)).symm], exact Hi.2.2}, 
    have H21 : a * b * (a^(i+1)*b^(i+1)) = a * a^(i+1) * (b * b^(i+1)), from Hi.2.1 ▸ H20, 
    have H22 : a * b * a^(i+1) * b^(i+1) = a * a^(i+1) * b * b^(i+1), 
        by {conv {to_lhs, rw [mul_assoc]}, conv {to_rhs, rw [mul_assoc]}, exact H21},  
    have H23 : a * b * a^(i+1) = a * a^(i+1) * b, from mul_right_cancel H22, 
    have H24 : a * (b * a^(i+1)) = a * (a^(i+1) * b), by {rw [mul_assoc, mul_assoc] at H23; exact H23}, 
    have H25 : b * a^(i+1) = a^(i+1) * b, from mul_left_cancel H24, 
    have H26 : b * (a^i * a) = (a^i * a) * b, from (gpow_add'' a i) ▸ H25, 
    have H27 : b * a^i * a = a^i * a * b, by {rw [mul_assoc], exact H26}, 
    have H28 : a^i * b * a = a^i * a * b, from H1 ▸ H27, 
    have H29 : a^i * (b * a) = a^i * (a * b), by {rw [mul_assoc, mul_assoc] at H28, exact H28}, 
    have H30 : b * a = a * b, from mul_left_cancel H29, 
H30.symm )















/- 
theorem Q04AltAlt [group G] : 
(∀ a b : G, 
(∃ i : ℤ, (Q04H a b i) ∧ (Q04H a b (i + 1)) ∧ (Q04H a b (i + 2)))) 
→ ∀ a b : G, a * b = b * a := 
begin
    intro H0, 
    intros a b, 
    apply exists.elim (H0 a b), 
    intros i Hi, 
    unfold Q04H at Hi,
    have H1 : a^i * b = b * a^i,   
        apply (mul_right_inj (b^i)).1, 
        apply eq.symm, 
        rw mul_assoc,  
        rw ←(Hi.1), 
        apply (mul_left_inj (a)).1, 
        rw [←mul_assoc, ←mul_assoc, ←mul_assoc],
        rw [←gpow_add', ←gpow_add', mul_assoc, ←gpow_add'], 
    from Hi.2.1, 
    
    let H3  : _ ^ ( i + ( 1 + 1)) = _ := Hi.2.2, 
    rw ←add_assoc at H3, 
    rw gpow_add' at H3, 
    rw (show i + 2 = (i + 1) + 1, by rw [add_assoc];refl) at H3,
    conv at H3 begin
      to_rhs,
      rw gpow_add',
    end,
    rw gpow_add' at H3,
    rw [mul_assoc, mul_assoc a (a^(i + 1))] at H3, 
    rw mul_left_inj at H3, 
    rw Hi.1 at H3, 
    rw (gpow_add' b ) at H3, 
    rw (gpow_add' b ) at H3,
    repeat {rw [←mul_assoc] at H3}, 
    rw mul_right_inj at H3, 
    rw (gpow_add' a) at H3, 
    rw mul_assoc (a) at H3, 
    rw (H1) at H3, 
    rw [mul_assoc a] at H3,
    rw mul_assoc b (a^i) b at H3, 
    rw H1 at H3, 
    repeat {rw [←mul_assoc] at H3}, 
    rw mul_right_inj at H3, 
    rw mul_right_inj at H3,
    rw H3, 
end -/