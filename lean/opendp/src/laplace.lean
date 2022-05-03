import data.fin.basic
import data.nat.basic
import data.nat.dist
import data.real.basic
import data.vector.basic
import data.multiset.basic
import algebra.group.basic
import algebra.big_operators.multiset
import order.basic
import .dists
import .sum

variables {n m : ℕ} {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)

/-
theorem vector.bounded_sized_sum_neighbor_stability (v₁ v₂ : vector (fin (n + 1)) m) (hn : v₁ ~ v₂) :
  nat.dist (vector.fin_bounded_sum v₁) (vector.fin_bounded_sum v₂) ≤ n :=
begin
end
-/

noncomputable def laplace_scale (sensitivity ε : ℝ) := sensitivity / ε

noncomputable def laplace_pdf (x μ scale : ℝ) := real.exp 

noncomputable def bounded_sum_pdf (v : vector (fin (n + 1)) m) (ε q : ℝ) (hε : ε > 0) : ℝ := 

noncomputable theorem vector.bounded_sum_dp
(v₁ v₂ : vector (fin (n + 1)) m) (ε q : ℝ) (hn : v₁ ~ v₂) (hε : ε > 0) :
  bounded_sum_pdf v₁ ε q hε ≤ bounded_sum_pdf v₂ ε q hε :=
begin
end
