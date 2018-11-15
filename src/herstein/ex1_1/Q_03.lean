import data.set.basic

variable α: Type*
variables A B C: set α

open set

theorem Q_03: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
ext $ λ x,
  ⟨λ h,
    ⟨or.elim h or.inl (λ hbc, or.inr hbc.1),
     or.elim h or.inl (λ hbc, or.inr hbc.2)⟩,
   λ ⟨hab, hac⟩, or.elim hab or.inl
    (λ hb, or.elim hac or.inl
    (λ hc, or.inr ⟨hb, hc⟩))⟩
