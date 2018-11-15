import data.set.basic

variable α: Type*
variables A B: set α

open set

-- requires classical logic
theorem Q4a: compl (A ∩ B) = (compl A) ∪ (compl B) :=
ext $ λ x,
  ⟨λ hi, classical.by_cases
    (λ ha, or.inr (λ hb, hi ⟨ha, hb⟩))
    (λ hn, or.inl hn),
   λ hu, or.elim hu
    (λ hac ⟨ha, hb⟩, hac ha)
    (λ hbc ⟨ha, hb⟩, hbc hb)⟩

theorem Q4b: compl (A ∪ B) = (compl A) ∩ (compl B) :=
ext $ λ x,
  ⟨λ hu,
    ⟨λ ha, hu (or.inl ha),
     λ hb, hu (or.inr hb)⟩,
   λ ⟨hac, hbc⟩ hu, or.elim hu
    (λ ha, hac ha)
    (λ hb, hbc hb)⟩
