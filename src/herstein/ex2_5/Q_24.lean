import algebra.group algebra.group_power


variables {G: Type*} (a b : G)

theorem Q_24 [group G] (H1 : ∀ a b : G, (a * b)^3 = a^3 * b^3) (H2 : ∀ x : G, x^3 = 1 → x = 1) : 
∀ a b : G, a * b = b * a :=
λ a b : G,

have Lem1 : ∀ x y : G, (y * x)^2 = x^2 * y^2, from 
    λ x y : G, 
    have H10 : (a * b) * (a * b) * (a * b) = (a * a^2) * b^3, from sorry, 
    have H11 : a * (b * (a * b) * (a * b)) = a * (a^2 * b^3), from sorry, 
    have H12 : b * (a * b) * (a * b) = a^2 * (b^2 * b), from sorry,
    have H13 : (b * (a * b) * a) * b = (a^2 * b^2) * b, from sorry, 
    have H14 : b * (a * b) * a = a^2 * b^2, from sorry, 
sorry, 

have Lem2 : b^2 * a^3 = a^3 * b^2, from 
    have H20 : a * ((b * a) * (b * a)) = a * (a^2 * b^2), from sorry, 
    have H21 : (a * b) * (a * b) * a = (a * a^2) * b^2, from sorry, 
    have H22 : (a * b)^2 * a = a^3 * b^2, from sorry,
    have H23 : b^2 * a^2 * a = a^3 * b^2, from sorry, 
sorry, 
 
let h : G := a * b * a^(-1 : ℤ) * b^(-1 : ℤ) in
have Lem3 : (h^2)^3 = 1, from 
calc (h^2)^3
    = ((a * b * a^(-1 : ℤ) * b^(-1 : ℤ))^2)^3 : sorry
... = (b^(-2 : ℤ) * ((a * b * a^(-1 : ℤ))^2))^3 : sorry
... = (b^(-2 : ℤ) * (a^(-2 : ℤ)) * (a * b)^2)^3 : sorry
... = (b^(-2 : ℤ) * ((a^(-2 : ℤ)) * (a^2 * b^2)))^3 : sorry
... = ( b^(-2 : ℤ) * (a^(-2 : ℤ) * (b^2 * a^2)) )^3 : sorry
... = (b^(-2 : ℤ))^3 * (a^(-2 : ℤ))^3 * b^6 * a^6 : sorry
... = (b^(-3 : ℤ))^2 * (a^(-2 : ℤ))^3 * b^6 * a^6 : sorry
... = (a^(-2 : ℤ))^3 * (b^(-3 : ℤ))^2 * b^6 * a^6 : sorry
... = a^(-6 : ℤ) * b^(-6 : ℤ) * b^6 * a^6 : sorry
... = a^(-6 : ℤ) * b^(-6 : ℤ) * b^6 * a^6 : sorry
... = 1 : sorry, 

have Lem4 : h^2 = 1, from sorry, 

show a * b = b * a, from sorry

