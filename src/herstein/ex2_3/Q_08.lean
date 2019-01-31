import data.fintype

universe u

example {G : Type u} [group G] [fintype G] [decidable_eq G] (x : G) : ∃ n : ℕ, x ^ (n + 1) = 1 :=
begin
    -- The above means 
    -- G is a type in some universe, is a group, has finite terms, equality of terms is "doable"...
     
    let f : fin (fintype.card G) → G := λ n , x ^ (n.1 + 1), 
    -- fintype.card G takes fintype G and returns its cardinality
    -- x : fin n means x is a pair (k, Hk) where k : ℕ, Hk : k < n 
    
    by_cases H : function.injective f , 
    cases nonempty_of_trunc (fintype.equiv_fin G), -- ???

    have H1 : function.surjective f, from 
    (fintype.injective_iff_surjective_of_equiv val.symm ).1 H, 
    -- fintype.blah : α, β same cardinality, f : α → β, then f inj ↔ f surj,
    have H2 : ∃ n : fin (fintype.card G), f n = 1, from H1 1, 
    cases H2 with n Hn, -- Extracts n and pf that f n = 1 from H2
    use [n.1, Hn], -- 'use' only accepts term mode pfs 
    
    unfold function.injective at H, -- Unfolds definition of 'injective' in H
    simp [not_forall] at H, -- Tells Lean '¬ ∀ → ∃' at H 
    rcases H with ⟨m, n, H1, H2⟩, -- Extracts m, n, pf of f m = f n, m ≠ n from H
    cases lt_or_gt_of_ne H2, 
      -- Breaks m ≠ n into m < n ∨ m > n becuz we don't have WLOG m < n working
      
      -- Pf of result when m < n
      -- Gist: x^((n - m - 1) + 1) = 1 , n - m - 1 is the number we looking for. 
      have H01 : x^(n.1-m.1) * x^(m.1+1) = 1 * x^(m.1+1), from 
      -- H01 is preparation for H02 to cancel x^(m.1 + 1) on both sides. 
      -- Reminder: it'm n.1, m.1 becuz n, m : (number, pf) 
      calc x^(n.1-m.1) * x^(m.1+1)
            = x^(n.1 - m.1 + (m.1+1))   : (pow_add x _ _).symm 
        ... = x^(n.1+1)               : by rw [←add_assoc, nat.sub_add_cancel (le_of_lt h)]
        ... = x^(m.1+1)               : H1.symm 
        ... = 1 * x^(m.1+1)           : (one_mul _).symm , 
      have H02 : x^(n.1 - m.1) = 1, from mul_right_cancel H01,
      have H03 : x^(n.1 - m.1 - 1 + 1) = 1, by rwa [nat.sub_add_cancel (nat.sub_pos_of_lt h)], 
      -- 'rwa' rewrites then matches goal with an existing hypothesis, in this case H02. 
      use [n.1 - m.1 - 1, H03], /- Tells Lean H03 is a pf that n.1 - m.1 - 1 satisfies 
      the ∃ statement we are after. -/ 

      -- Repeated pf with m > n
      have H01 : x^(m.1-n.1) * x^(n.1+1) = 1 * x^(n.1+1), from 
      calc x^(m.1-n.1) * x^(n.1+1)
            = x^(m.1 - n.1 + (n.1+1))   : (pow_add x _ _).symm
        ... = x^(m.1+1)               : by rw [← add_assoc, nat.sub_add_cancel (le_of_lt h)]
        ... = x^(n.1+1)               : H1 
        ... = 1 * x^(n.1+1)           : (one_mul _).symm , 
      have H02 : x^(m.1 - n.1) = 1, from mul_right_cancel H01,
      have H03 : x^(m.1 - n.1 - 1 + 1) = 1, by rwa [nat.sub_add_cancel (nat.sub_pos_of_lt h)], 
      use [m.1 - n.1 - 1, H03], 
      /- Note - How to swap n'm & m'm (For Mac OS / ):
      0. Press Option-Command-F. This opens the Replace window. 
      1. Highlight section. In this case lines 47 to 55. 
      2. Press button to the right of ->. This restrict changes to the highlighted section. 
      3. Type \bn\n into top box. This locates all 'isolated' n's. 
      4. Type t into bottom box, then Command-Enter. This replaces all n's with t's. 
      5. Now repeat step 3,4 to replace all m with n's.
      6. Repeat step 3,4 to replace all t's with m's. -/
end

-- Lemmas used
#check @fintype.injective_iff_surjective_of_equiv 
#check @fintype.equiv_fin 
#print function.surjective 
#check @eq.subst 
#check @lt_or_gt_of_ne
#check sub_add_cancel 
#check @sub_pos_of_lt 