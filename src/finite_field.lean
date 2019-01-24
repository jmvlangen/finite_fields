import algebra.char_p
import data.zmod.basic

import field
import vector_space

universes u v

section integral_domain

variables {α : Type u} [integral_domain α]

open nat

lemma ring_char_prime_or_zero : nat.prime (ring_char α) ∨ ring_char α = 0 :=
let r := ring_char α in
or.elim (nat.eq_zero_or_eq_succ_pred r)
  (assume h₀ : r = 0,
   show nat.prime r ∨ r = 0, from or.inr h₀)
  (assume h₀ : r = succ (pred r),
   or.elim (nat.eq_zero_or_eq_succ_pred (pred r))
     (assume h₁ : pred r = 0,
      have r = 1, from (h₁ ▸ h₀ : r = succ 0),
      have r ∣ 1, from eq.symm this ▸ one_dvd 1,
      have (nat.cast 1 : α) = 0, from (ring_char.spec α 1).mpr this,
      have (1 : α) = 0, from @cast_one α _ _ ▸ this,
      absurd this one_ne_zero)
     (assume h₁ : pred r = succ (pred (pred r)),
      have r = (succ $ succ $ pred $ pred r), from h₁ ▸ h₀,
      have r ≥ 2, from eq.symm this ▸ (succ_le_succ $ succ_le_succ $ nat.zero_le (pred (pred r))),
      have ∀ d ∣ r, d = 1 ∨ d = r, from
        assume d : ℕ,
        assume hdvd : ∃ e : ℕ, r = d * e,
        let ⟨e, hmul⟩ := hdvd in
        have r > 0, from gt_of_ge_of_gt ‹r ≥ 2› (nat.zero_lt_succ 1),
        have (r : α) = 0, from (ring_char.spec α r).mpr (dvd_refl r),
        have (d : α) * e = 0, from (@cast_mul α _ d e) ▸ (hmul ▸ this),
        or.elim (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero (d : α) e this)
          (assume hd : (d : α) = 0,
           have r ∣ d, from (ring_char.spec α d).mp hd,
           have d > 0, from pos_of_dvd_of_pos hdvd ‹r > 0›, 
           have d ≥ r, from le_of_dvd ‹d > 0› ‹r ∣ d›,
           have d ≤ r, from le_of_dvd ‹r > 0› ‹d ∣ r›,
           have d = r, from eq_iff_le_not_lt.mpr ⟨‹d ≤ r›, not_lt_of_ge ‹d ≥ r›⟩,
           show d = 1 ∨ d = r, from or.inr ‹d = r›)
          (assume he : (e : α) = 0,
           have r ∣ e, from (ring_char.spec α e).mp he,
           have e ∣ r, from dvd_of_mul_left_eq d (eq.symm hmul),
           have e > 0, from pos_of_dvd_of_pos ‹e ∣ r› ‹r > 0›,
           have e ≥ r, from le_of_dvd ‹e > 0› ‹r ∣ e›,
           have e ≤ r, from le_of_dvd ‹r > 0› ‹e ∣ r›,
           have e = r, from eq_iff_le_not_lt.mpr ⟨‹e ≤ r›, not_lt_of_ge ‹e ≥ r›⟩,
           have d * r = 1 * r, from
             calc
               d * r = d * e : by rw ‹e = r›
                 ... = r     : by rw hmul
                 ... = 1 * r : by rw one_mul, 
           have d = 1, from nat.eq_of_mul_eq_mul_right ‹r > 0› this,
           show d = 1 ∨ d = r, from or.inl ‹d = 1›),
      have nat.prime r, from ⟨‹r ≥ 2›, this⟩,
      show nat.prime r ∨ r = 0, from or.inl this))

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
