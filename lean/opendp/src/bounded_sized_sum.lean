import data.fin.basic
import data.nat.basic
import data.nat.dist
import data.real.basic
import data.vector.basic
import data.multiset.basic
import algebra.group.basic
import algebra.big_operators.multiset
import data.complex.basic
import order.basic
import .dists

/-- Bounded sum, known N. --/

variables {n m : ℕ} {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)

@[reducible] def vector.fin_sum (v : vector (fin (n + 1)) m) : ℕ
  := multiset.sum ((v.to_list : multiset (fin (n + 1))).map nat_of_fin)

@[reducible] def vector.fin_bounded_sum (v : vector (fin (n + 1)) m) : fin ((n * m) + 1)
  := fin.of_nat' (vector.fin_sum v)

@[simp] lemma vector.cons_to_list (a : α) (v : vector α n) :
  (a ::ᵥ v).to_list = a :: v.to_list := by simp

lemma vector.cons_succ (v : vector α n.succ) : 
  v = v.head ::ᵥ v.tail := by simp

lemma vector.cons_succ_to_list (v : vector α n.succ) : 
  v.to_list = v.head :: v.tail.to_list := begin
    have h₁ : v.to_list = (v.head ::ᵥ v.tail).to_list := begin
      have : v = v.head ::ᵥ v.tail := vector.cons_succ _,
      simp
    end,
    rw h₁, simp only [vector.cons_to_list], simp
end

/- TODO: rewrite to follow from list.fin_sum_le and multiset.fin_sum_le. -/
@[simp] theorem vector.fin_sum_le (v : vector (fin (n + 1)) m) :
  vector.fin_sum v ≤ n * m :=
begin
  simp only [vector.fin_sum, multiset.sum],
  induction m with _ hd,
  have h₁ : v = vector.nil := by simp,
  rw h₁, simp,
  have h₂ : v.to_list = v.head :: v.tail.to_list
    := vector.cons_succ_to_list _,
  have h₃ : nat_of_fin v.head ≤ n := fin.is_le _,
  specialize hd v.tail, simp at *, 
  have h₄ : n * m_n + n = n + n * m_n := nat.add_comm _ _,
  rw [nat.mul_succ, h₂, h₄], exact add_le_add h₃ hd
end

theorem list.fin_sum_le (l : list (fin (n + 1))) :
  (l.map nat_of_fin).sum ≤ n * l.length :=
begin
  induction l with d ih,
  simp,
  have h₁ : (list.map nat_of_fin (d :: ih)).sum
  = nat_of_fin d + (list.map nat_of_fin ih).sum := by simp,
  rw h₁,
  have h₃ : nat_of_fin d ≤ n := fin.is_le _,
  have h₄ : n * (d :: ih).length = n + ih.length * n
    := by { simp, rw [left_distrib, mul_one, add_comm, mul_comm] },
  rw [h₄, mul_comm], exact add_le_add h₃ l_ih
end
  
theorem multiset.fin_sum_le (m : multiset (fin (n + 1))) :
  (m.map nat_of_fin).sum ≤ n * m.card
:= by { induction m, simp [-nat_of_fin], exact list.fin_sum_le _, simp }

lemma nat.lt_succ_le (h : m ≤ n) : m < n.succ := nat.lt_succ_iff.mpr h

@[simp] lemma vector.fin_sum_le_mod (v : vector (fin (n + 1)) m) :
  (vector.fin_sum v) % ((n * m) + 1) = vector.fin_sum v := 
begin
  have   : vector.fin_sum v ≤ n * m       := vector.fin_sum_le _,
  have h : vector.fin_sum v < (n * m) + 1 := nat.lt_succ_le _,
  exact nat.mod_eq_of_lt h, simp
end

lemma multiset.nat_sum_map_sub_add_inter (s t : multiset α) (f : α → ℕ):
  (multiset.map f s).sum = (multiset.map f (s - t)).sum + (multiset.map f (s ∩ t)).sum :=
begin
  have h₁ : (multiset.map f s) = (multiset.map f ((s - t) + (s ∩ t)))
    := by { rw multiset.sub_add_inter },
  rw h₁,
  simp
end

lemma list.diff_length_multiset_sub_card (l₁ l₂ : list α) :
(l₁.diff l₂).length = ((l₁ : multiset α) - (l₂ : multiset α)).card := by simp

lemma nat.dist.triangle_inequality_zero (m n : ℕ) : m.dist n ≤ m + n := begin
  have h₁ : m.dist n ≤ m.dist 0 + nat.zero.dist n
    := nat.dist.triangle_inequality m 0 n,
  have h₂ : m.dist 0 = m := nat.dist_zero_right _,
  have h₃ : nat.zero.dist n = n := nat.dist_zero_left _,
  rw [h₂, h₃] at h₁, exact h₁
end

@[simp] def vector.fin_bounded_sum_dist (v₁ v₂ : vector (fin (n + 1)) m) : ℕ
  := nat.dist (vector.fin_bounded_sum v₁) (vector.fin_bounded_sum v₂)

theorem vector.bounded_sized_sum_stability (v₁ v₂ : vector (fin (n + 1)) m) : 
vector.fin_bounded_sum_dist v₁ v₂ ≤ n * (v₁ |ΔV| v₂) := begin
  simp, 
  simp only [vector.fin_sum],
  let l₁ := v₁.to_list,
  let l₂ := v₂.to_list,
  let m₁ := (l₁ : multiset (fin (n + 1))),
  let m₂ := (l₂ : multiset (fin (n + 1))),
  let fmap := multiset.map nat_of_fin,
  let mml := fmap (m₁ - m₂),
  let mmr := fmap (m₂ - m₁),
  have h₁ : (fmap m₁).sum = mml.sum + (fmap (m₁ ∩ m₂)).sum
    := multiset.nat_sum_map_sub_add_inter _ _ _,
  have h₂ : (fmap m₂).sum = mmr.sum + (fmap (m₂ ∩ m₁)).sum
    := multiset.nat_sum_map_sub_add_inter _ _ _,
  have h₃ : (l₁.diff l₂).length = (m₁ - m₂).card := list.diff_length_multiset_sub_card _ _,
  have h₄ : (l₂.diff l₁).length = (m₂ - m₁).card := list.diff_length_multiset_sub_card _ _,
  rw [left_distrib, h₁, h₂, h₃, h₄],
  simp only [nat.dist_add_add_right, multiset.inter_comm],
  have h₅ : mml.sum ≤ n * (m₁ - m₂).card := multiset.fin_sum_le _,
  have h₆ : mmr.sum ≤ n * (m₂ - m₁).card := multiset.fin_sum_le _,
  have h_tri : mml.sum.dist mmr.sum ≤ mml.sum + mmr.sum 
    := nat.dist.triangle_inequality_zero _ _,
  have h_sym : mml.sum + mmr.sum ≤ n * (m₁ - m₂).card + n * (m₂ - m₁).card
    := add_le_add _ _,
  exact le_trans h_tri h_sym, exact h₅, exact h₆
end

theorem vector.bounded_sized_sum_neighbor_stability (v₁ v₂ : vector (fin (n + 1)) m) (hn : v₁ ~ v₂) :
  vector.fin_bounded_sum_dist v₁ v₂ ≤ n :=
begin
  simp [-vector.sym_dist] at hn,
  have h₁ : vector.fin_bounded_sum_dist v₁ v₂ ≤ n * (v₁ |ΔV| v₂)
    := vector.bounded_sized_sum_stability _ _,
  have h₂ : n * (v₁ |ΔV| v₂) ≤ n * 1 := nat.mul_le_mul_of_nonneg_left hn,
  rw mul_one at h₂,
  exact le_trans h₁ h₂
end


