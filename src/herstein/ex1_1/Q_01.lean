import data.set.basic

variable α: Type*
variables A B C: set α

open set

theorem Q_01a: A ⊆ B ∧ B ⊆ C → A ⊆ C :=
λ ⟨hl, hr⟩ a ha, hr (hl ha)

theorem Q_01b₁: B ⊆ A → A ∪ B = A :=
λ h, ext $ λ x,
  ⟨λ hab, or.elim hab (λ ha, ha) (λ hb, h hb),
   or.inl⟩

theorem Q_01c₁: B ⊆ A → B ∪ C ⊆ A ∪ C :=
λ h x hbc, or.elim hbc
  (λ hb, or.inl (h hb))
  (λ hc, or.inr hc)

theorem Q_01c₂: B ⊆ A → B ∩ C ⊆ A ∩ C :=
λ h x ⟨hb, hc⟩, ⟨h hb , hc⟩
