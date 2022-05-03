
import data.vector
import data.real.basic
import init.data.list

universes u 
variables {α : Type u} {n : ℕ} 

@[simp] def resize_constant (m : ℕ) (zero : α) : vector α n → vector α m
| ⟨l, p⟩ := ⟨ list.take m (l ++ list.repeat zero m), by simp ⟩

theorem resize_preserves_elements (zero : α) :
∀ (n : ℕ) (v : vector α n), 
v = resize_constant n zero v
| n ⟨l, p⟩ := begin
  simp,
  suffices len : n = l.length,
  rw len,
  simp,
  symmetry,
  rw p
end

/-
theorem resize_sensitivity (n : ℕ) (zero : α) [decidable_eq α] :
∀ (v₁ : vector α n) (v₂ : vector α n) (m : ℕ),
v₁ ~ v₂ → (resize_constant m zero v₁) ~ (resize_constant m zero v₂)
| v₁ v₂ m := begin
  intros neighbors,
  simp,
  suffices v₁_take : (resize_constant m zero v₁).to_list
    = list.take m (v₁.to_list ++ list.repeat zero m),
  suffices v₂_take : (resize_constant m zero v₂).to_list
    = list.take m (v₂.to_list ++ list.repeat zero m),
  rw [v₁_take, v₂_take],
  suffices distrib : list.zip_with element_dist
               (list.take m (v₁.to_list ++ list.repeat zero m))
               (list.take m (v₂.to_list ++ list.repeat zero m))
             = list.take m 
                 (list.zip_with element_dist
                                (v₁.to_list ++ list.repeat zero m)
                                (v₂.to_list ++ list.repeat zero m)),
  rw distrib,
  cases m,
  simp
end
-/