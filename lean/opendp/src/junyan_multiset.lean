/- 
taken from a comment by Junyan Xu on 
https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Generalization.20of.20map_diff.html
-/
import data.multiset.basic
open multiset
variables {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)

lemma multiset.map_diff_subset (s₁ : multiset α) (s₂ : multiset α) :
  s₁.map f - s₂.map f ≤ (s₁ - s₂).map f :=
begin
  rw [tsub_le_iff_right, le_iff_count],
  intro, simp only [count_add, count_map, ← card_add, ← filter_add],
  exact card_le_of_le (filter_le_filter _ $ tsub_le_iff_right.1 le_rfl),
end

lemma list.map_diff_subset (l₁ : list α) (l₂ : list α) :
  (l₁.map f).diff (l₂.map f) ⊆ (l₁.diff l₂).map f :=
begin
  simp only [← coe_subset, ← coe_sub, ← coe_map],
  exact subset_of_le (multiset.map_diff_subset f _ _),
end