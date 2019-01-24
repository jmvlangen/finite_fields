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

lemma dvd_self {α : Type u} [has_dvd α] {a : α} : a ∣ a := sorry

instance zmod_ring_hom {h : ring_char α > 0} :
is_ring_hom (nat.cast ∘ fin.val : zmod ⟨ring_char α, h⟩ → α) :=
{ map_one := have h1 : (1 : ℕ) < (⟨ring_char α, h⟩ : ℕ+),
    from or.elim (@ring_char_prime_or_zero α _)
      (assume hp, nat.prime.gt_one hp)
      (assume h0, absurd h0 (ne_of_gt h)),
    begin
      unfold function.comp,
      rw[←nat.cast_one, zmod.val_cast_of_lt h1],
      exact nat.cast_one
    end,
  map_mul := λ {x y}, show (↑(x * y).val : α) = ↑x.val * ↑y.val, from
    begin
      rw[←nat.cast_mul],
      rw[←nat.mod_add_div(x.val * y.val) (ring_char α)],
      rw[zmod.mul_val],
      simp,
      rw[(ring_char.spec α (ring_char α)).mpr dvd_self],
      rw[zero_mul, add_zero]
    end,
  map_add := λ x y, show (↑(x + y).val : α) = ↑x.val + ↑y.val, from
    begin
      rw[←nat.cast_add],
      rw[←nat.mod_add_div(x.val + y.val) (ring_char α)],
      rw[zmod.add_val],
      simp,
      rw[(ring_char.spec α (ring_char α)).mpr dvd_self],
      rw[zero_mul, add_zero]
    end }

open is_ring_hom

noncomputable instance zmod_module_pos_char {h : ring_char α > 0} :
module (zmod ⟨ring_char α, h⟩) α :=
module.of_core
{ smul := λ r x, (nat.cast ∘ fin.val) r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw[mul_add]; refl,
  add_smul := λ r s x, by unfold has_scalar.smul; rw[@map_add _ _ _ _ (nat.cast ∘ fin.val) zmod_ring_hom _ _, add_mul],
  mul_smul := λ r s x, by unfold has_scalar.smul; rw[@map_mul _ _ _ _ (nat.cast ∘ fin.val) zmod_ring_hom _ _, mul_assoc], 
  one_smul := λ x, show (nat.cast ∘ fin.val) 1 * x = _,
    by rw[@map_one _ _ _ _ (nat.cast ∘ fin.val) zmod_ring_hom, one_mul] }

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
have V : vector_space F α, from @vector_space.mk F α _ _ zmod_module_pos_char,
let ⟨n, h⟩ := @vector_space.card_fin_vector_space F α _ _ _ _ V _ in
⟨card F, n, hp, h⟩

theorem exists_fin_field : ∀ p n : ℕ, prime p → ∃ α : Type*, ∃ [hf : field α], ∃ [hfin : fintype α], @card α hfin = p^n :=
sorry

theorem unique_fin_field [field α] [field β] : card α = card β → (α ≃r β) :=
sorry

end finite_field
