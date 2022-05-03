import data.fin.basic
import data.nat.basic
import data.nat.dist
import data.multiset.basic
import .dists

/-- Bounded sum, unknown N. --/
variables {n m ub : ℕ} {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)

def nf (a : fin (n + 1)) := nat_of_fin a

@[simp] def multiset.sat_add (a : fin (n + 1)) (b : fin (n + 1)) : (fin (n + 1))
  := fin.clamp ((nf a) + (nf b)) n


lemma multiset.sat_add_comm (a : fin (n + 1)) (b : fin (n + 1)) :
  multiset.sat_add a b = multiset.sat_add b a :=
begin
  simp only [multiset.sat_add],
  have h : nf a + nf b = nf b + nf a
    := by { rw add_comm },
  rw h
end

/-
lemma fin.clamp_le (v n : ℕ) (h : v ≤ n) : fin.clamp v n = v :=
begin

end
-/


lemma multiset.sat_add_left_comm (a b c: fin (n + 1)) :
  multiset.sat_add a (multiset.sat_add b c) = multiset.sat_add b (multiset.sat_add a c) :=
begin
  simp only [multiset.sat_add],
  cases classical.em (nf a + nf b + nf c ≤ nf n),
  have ha : nf a + nf b ≤ nf n := nat.le_of_add_le_left _,
  have hc : nf c ≤ nf n := nat.le_of_add_le_right _,

  /-
  have hb : nf b ≤ nf n := nat.le_of_add_le_left _ _ ,
  -/
end
  

@[reducible] def multiset.sat_sum (m : multiset (fin (n + 1))) (ub : ℕ) (h : n ≤ ub): (fin (ub + 1))
  := multiset.foldr 
