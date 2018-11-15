import data.set.basic
import data.finset

universe u
variable α: Type

variable a: α
variables A B C: set α

variables S T: finset ℕ

open set finset

theorem Q1a: A ⊆ B ∧ B ⊆ C → A ⊆ C :=
λ ⟨hl, hr⟩ a ha, hr (hl ha)

theorem Q1b₁: B ⊆ A → A ∪ B = A :=
λ h, ext $ λ x,
  ⟨λ hab, or.elim hab (λ ha, ha) (λ hb, h hb),
   or.inl⟩

theorem Q1c₁: B ⊆ A → B ∪ C ⊆ A ∪ C :=
λ h x hbc, or.elim hbc
  (λ hb, or.inl (h hb))
  (λ hc, or.inr hc)

theorem Q1c₂: B ⊆ A → B ∩ C ⊆ A ∩ C :=
λ h x ⟨hb, hc⟩, ⟨h hb , hc⟩



theorem Q2a: A ∩ B = B ∩ A :=
ext $ λ x,
  ⟨λ ⟨ha, hb⟩, ⟨hb, ha⟩,
   λ ⟨hb, ha⟩, ⟨ha, hb⟩⟩

theorem Q2b: (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
ext $ λ x,
  ⟨λ ⟨⟨ha, hb⟩, hc⟩, ⟨ha, ⟨hb, hc⟩⟩,
   λ ⟨ha, ⟨hb, hc⟩⟩, ⟨⟨ha, hb⟩, hc⟩⟩



theorem Q3: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
ext $ λ x,
  ⟨λ h,
    ⟨or.elim h or.inl (λ hbc, or.inr hbc.1),
     or.elim h or.inl (λ hbc, or.inr hbc.2)⟩,
   λ ⟨hab, hac⟩, or.elim hab or.inl
    (λ hb, or.elim hac or.inl
    (λ hc, or.inr ⟨hb, hc⟩))⟩



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



theorem Q5: card (S ∪ T) = card S + card T - card (S ∩ T) := sorry



-- theorem Q6: ?


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



#check set.powerset


