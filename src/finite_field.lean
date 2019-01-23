import algebra.char_p

import integer
import field
import vector_space

universes u v

section integral_domain

variables {α : Type u} [integral_domain α]

lemma ring_char_prime_or_zero : nat.prime (ring_char α) ∨ ring_char α = 0 :=
sorry

lemma ring_char_prime [fintype α] : nat.prime (ring_char α) :=
sorry

instance zmodp_module_pos_char {hp : nat.prime (ring_char α)} : module (zmodp (ring_char α) hp) α :=
sorry

end integral_domain

namespace finite_field

open fintype

variables {α : Type u} {β : Type v}
variables [discrete_field α] [fintype α]
variables [field β] [fintype β]

theorem fin_field_card (α : Type*) [discrete_field α] [fintype α] :
∃ p n : ℕ, nat.prime p ∧ card α = p^n :=
let F := zmodp (ring_char α) ring_char_prime in
have hp : nat.prime (card F) := by simp; exact ring_char_prime,
have V : vector_space F α, from @vector_space.mk F α _ _ zmodp_module_pos_char,
let ⟨n, h⟩ := @vector_space.card_fin_vector_space F α _ _ _ _ V _ in
⟨card F, n, hp, h⟩

theorem exists_fin_field : ∀ p n : ℕ, prime p → ∃ α : Type*, ∃ [hf : field α], ∃ [hfin : fintype α], @card α hfin = p^n :=
sorry

theorem unique_fin_field [field α] [field β] : card α = card β → (α ≃r β) :=
sorry

end finite_field
