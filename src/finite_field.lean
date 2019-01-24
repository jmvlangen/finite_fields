import algebra.char_p
import data.zmod.basic

import field
import vector_space

universes u v

section integral_domain

variables {α : Type u} [integral_domain α]

lemma char_p_prime_or_zero {p : ℕ} [char_p α p] : nat.prime p ∨ p = 0 :=
sorry

lemma char_p_prime [fintype α] {p : ℕ} [char_p α p] : nat.prime p :=
sorry

instance ring_hom_pos_char {p : ℕ} [char_p α p] {h : p > 0} :
is_ring_hom (nat.cast ∘ fin.val : zmod ⟨p, h⟩ → α) :=
{ map_one := have h1 : (1 : ℕ) < (⟨p, h⟩ : ℕ+),
    from or.elim (@char_p_prime_or_zero α _ p _)
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
      rw[←nat.mod_add_div(x.val * y.val) p],
      rw[zmod.mul_val],
      simp,
      rw[(char_p.cast_eq_zero_iff α p p).mpr $ dvd_refl _],
      rw[zero_mul, add_zero]
    end,
  map_add := λ x y, show (↑(x + y).val : α) = ↑x.val + ↑y.val, from
    begin
      rw[←nat.cast_add],
      rw[←nat.mod_add_div(x.val + y.val) p],
      rw[zmod.add_val],
      simp,
      rw[(char_p.cast_eq_zero_iff α p p).mpr $ dvd_refl _],
      rw[zero_mul, add_zero]
    end }

open is_ring_hom

instance zmod_module_pos_char {p : ℕ} [char_p α p] {h : p > 0} :
module (zmod ⟨p, h⟩) α :=
module.of_core
{ smul := λ r x, (nat.cast ∘ fin.val) r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw[mul_add]; refl,
  add_smul := λ r s x, by unfold has_scalar.smul;
    rw[@map_add _ _ _ _ (nat.cast ∘ fin.val) ring_hom_pos_char _ _, add_mul]; apply_instance,
  mul_smul := λ r s x, by unfold has_scalar.smul;
    rw[@map_mul _ _ _ _ (nat.cast ∘ fin.val) ring_hom_pos_char _ _, mul_assoc]; apply_instance,
  one_smul := λ x, show (nat.cast ∘ fin.val) 1 * x = _,
    by rw[@map_one _ _ _ _ (nat.cast ∘ fin.val) ring_hom_pos_char, one_mul]; apply_instance }

end integral_domain

namespace finite_field

open fintype

variables {α : Type u} {β : Type v}
variables [discrete_field α] [fintype α]
variables [field β] [fintype β]

theorem fin_field_card (α : Type u) [discrete_field α] [fintype α] :
∃ n : ℕ, card α = (ring_char α)^n :=
begin
  haveI := (⟨ring_char.spec α⟩ : char_p α (ring_char α)),
  let F := zmodp (ring_char α) (@char_p_prime α _ _ _ _),
  have V : vector_space F α, from @vector_space.mk F α _ _ zmod_module_pos_char,
  cases @vector_space.card_fin_vector_space F α _ _ _ _ V _ with n h,
  exact ⟨n, fintype.card_fin (ring_char α) ▸ h⟩
end

theorem fin_field_card' (α : Type u) [discrete_field α] [fintype α] :
∃ p n : ℕ, nat.prime p ∧ card α = p^n :=
let ⟨n, h⟩ := fin_field_card α in
⟨ring_char α, n, @char_p_prime α _ _ (ring_char α) ⟨ring_char.spec α⟩, h⟩

theorem exists_fin_field : ∀ p n : ℕ, prime p → ∃ α : Type*, ∃ [hf : field α], ∃ [hfin : fintype α], @card α hfin = p^n :=
sorry

theorem unique_fin_field [field α] [field β] : card α = card β → (α ≃r β) :=
sorry

end finite_field
