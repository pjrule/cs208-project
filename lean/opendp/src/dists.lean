import data.vector
import data.vector.zip
import data.multiset.basic

variables {n m : ℕ} {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)

@[simp] def multiset.sym_diff (x y : multiset α) : multiset α
  := (x - y) + (y - x)
infix ` Δ `:51 := multiset.sym_diff

@[simp] def multiset.sym_dist (x y : multiset α) : ℕ := (x Δ y).card
infix ` |Δ| `:51 := multiset.sym_dist

@[simp] def list.sym_dist (x y : list α) : ℕ
  := (x : multiset α) |Δ| (y : multiset α)
infix ` |ΔL| `:52 := list.sym_dist

@[simp] def vector.sym_dist (x y : vector α n)
  := (x.to_list : multiset α) |Δ| (y.to_list : multiset α)
infix ` |ΔV| `:52 := vector.sym_dist

@[simp] def vec_neighbors (x y : vector α n) : bool := (x |ΔV| y) ≤ 1
infix ` ~ `:53 := vec_neighbors

lemma neighbor_diff_equiv :
∀ (v₁ : vector α n) (v₂ : vector α n), v₁ ~ v₂ ↔ v₁ |ΔV| v₂ ≤ 1 := by simp

/- 
The proofs for the two lemmas below (map_diff_subset) are taken from a comment by Junyan Xu on 
https://leanprover-community.github.io/archive/stream/113489-new-members/topic/
Generalization.20of.20map_diff.html
-/
theorem multiset.map_diff_subset (s₁ s₂ : multiset α) :
  s₁.map f - s₂.map f ≤ (s₁ - s₂).map f :=
begin
  rw [tsub_le_iff_right, multiset.le_iff_count],
  intro, simp only [multiset.count_add, multiset.count_map,
                    ← multiset.card_add, ← multiset.filter_add],
  exact multiset.card_le_of_le (multiset.filter_le_filter _ $ tsub_le_iff_right.1 le_rfl),
end

theorem list.map_diff_subset (l₁ l₂ : list α) :
  (l₁.map f).diff (l₂.map f) ⊆ (l₁.diff l₂).map f :=
begin
  simp only [← multiset.coe_subset, ← multiset.coe_sub, ← multiset.coe_map],
  exact multiset.subset_of_le (multiset.map_diff_subset f _ _),
end
/- end community contribution -/

theorem multiset.map_sym_diff_subset (s₁ s₂ : multiset α) :
  (s₁.map f) Δ (s₂.map f) ≤ (s₁ Δ s₂).map f :=
begin
  simp only [multiset.sym_diff],
  have h₁ : s₁.map f - s₂.map f ≤ (s₁ - s₂).map f
    := by { exact multiset.map_diff_subset _ _ _ },
  have h₂ : s₂.map f - s₁.map f ≤ (s₂ - s₁).map f
    := by { exact multiset.map_diff_subset _ _ _ },
  have h₃ : (s₁.map f - s₂.map f) + (s₂.map f - s₁.map f) 
    ≤ (s₁ - s₂).map f + (s₂ - s₁).map f
    := by { exact add_le_add h₁ h₂ },
  have h₄ : (s₁ - s₂).map f + (s₂ - s₁).map f
    ≤ ((s₁ - s₂) + (s₂ - s₁)).map f
    := by { simp },
  exact le_trans h₃ h₄
end

lemma multiset.map_sym_dist_le_map_sym_dist (s₁ s₂ : multiset α) :
  (s₁.map f) |Δ| (s₂.map f) ≤ ((s₁ Δ s₂).map f).card :=
begin
    have h : (s₁.map f) Δ (s₂.map f) ≤ (s₁ Δ s₂).map f
      := by { exact multiset.map_sym_diff_subset _ _ _ },
    exact multiset.card_le_of_le h
end

/-- Row transform stability. --/
theorem multiset.map_sym_dist_le_sym_dist (s₁ s₂ : multiset α) :
  (s₁.map f) |Δ| (s₂.map f) ≤ s₁ |Δ| s₂ :=
begin
  have h₁ : (s₁.map f) |Δ| (s₂.map f) ≤ ((s₁ Δ s₂).map f).card
    := by { exact multiset.map_sym_dist_le_map_sym_dist _ _ _ },
  have h₂ : ((s₁ Δ s₂).map f).card ≤ (s₁ Δ s₂).card
    := by { simp },
  exact le_trans h₁ h₂
end

@[simp] def nat_of_fin (v : fin (n + 1)) : ℕ := v