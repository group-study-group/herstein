import data.set.basic data.finset

variable α: Type*
variables A B C: set α

open set

-- requires classical logic?
theorem Q8: (A - B) ∪ (B - A) = (A ∪ B) - (A ∩ B) :=
ext $ λ x,
  ⟨λ hl,
    ⟨or.elim hl
      (λ hab, or.inl hab.1)
      (λ hba, or.inr hba.1),
     λ ⟨ha, hb⟩, or.elim hl
      (λ hab, hab.2 hb)
      (λ hba, hba.2 ha)⟩,
   λ hr, classical.by_cases
    (λ ha, or.inl ⟨ha, λ hb, hr.2 ⟨ha, hb⟩⟩)
    (λ hn, or.inr
      ⟨or.elim hr.1
        (λ ha, false.elim (hn ha))
        (λ hb, hb),
       hn⟩)⟩

