/- 
modified from an old version of a comment by Junyan Xu on 
https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Generalization.20of.20map_diff.html
-/
import data.multiset.basic
open multiset
variables {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)

lemma multiset.map_diff_subset (s₁ : multiset α) (s₂ : multiset α) :
  s₁.map f - s₂.map f ≤ (s₁ - s₂).map f :=
begin
  rw tsub_le_iff_right,
  rw le_iff_count,
  intro b,
  rw count_add,
  iterate 3 { rw count_map },
  rw ← card_add,
  apply card_le_of_le,
  rw ← filter_add,
  apply filter_le_filter,
  rw ← tsub_le_iff_right,
end


lemma list.map_diff_subset (l₁ : list α) (l₂ : list α) :
  (l₁.map f).diff (l₂.map f) ⊆ (l₁.diff l₂).map f :=
begin
  rw ← coe_subset,
  rw ← coe_sub,
  iterate 3 { rw ← coe_map },
  rw ← coe_sub,
  apply subset_of_le, apply multiset.map_diff_subset,
end