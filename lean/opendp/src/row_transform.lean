import data.fin.basic
import data.nat.basic
import data.real.basic
import data.multiset.basic
import algebra.group.basic
import .dists

variables {n m : ℕ} {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)

def clamp (ub : ℕ) (v : ℕ) : fin (ub + 1) := fin.clamp v ub

@[simp] def clamp_vec (s : multiset ℕ) (ub : ℕ) : multiset (fin (ub + 1))
  := s.map (clamp ub)

theorem clamp_stability (s₁ s₂ : multiset ℕ) (ub : ℕ) :
  (clamp_vec s₁ ub) |Δ| (clamp_vec s₂ ub) ≤ s₁ |Δ| s₂
:= multiset.map_sym_dist_le_sym_dist  _ _ _

theorem is_equal_stability (s₁ s₂ : multiset α) (v : α) :
  (s₁.map (eq v)) |Δ| (s₂.map (eq v)) ≤ s₁ |Δ| s₂
:= multiset.map_sym_dist_le_sym_dist _ _ _