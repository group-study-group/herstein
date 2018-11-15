import data.set.basic

variable α: Type*
variables A B C: set α

open set

theorem Q2a: A ∩ B = B ∩ A :=
ext $ λ x,
  ⟨λ ⟨ha, hb⟩, ⟨hb, ha⟩,
   λ ⟨hb, ha⟩, ⟨ha, hb⟩⟩

theorem Q2b: (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
ext $ λ x,
  ⟨λ ⟨⟨ha, hb⟩, hc⟩, ⟨ha, ⟨hb, hc⟩⟩,
   λ ⟨ha, ⟨hb, hc⟩⟩, ⟨⟨ha, hb⟩, hc⟩⟩
