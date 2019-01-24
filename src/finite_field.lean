import algebra.char_p

import integer
import field
import vector_space

universes u v

section integral_domain

variables {α : Type u} [integral_domain α]

open nat function

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

lemma ring_char_prime [fintype α] [decidable_eq α] : nat.prime (ring_char α) :=
let r := ring_char α in
have nat.prime r ∨ r = 0, from ring_char_prime_or_zero,
or.elim this
   (assume h : nat.prime r,
    show nat.prime r, from h)
   (assume h : r = 0,
    let ι : ℕ → α := nat.cast in
    have ∀ n : ℕ, (n : α) = 0 → n = 0, from
      assume n : ℕ,
      assume h₀ : (n : α) = 0,
      have 0 ∣ n, from h ▸ (ring_char.spec α n).mp h₀, 
      show n = 0, from zero_dvd_iff.mp this,
    have char_zero α, from add_group.char_zero_of_inj_zero this,
    have ht : injective ι, from @cast_injective α _ _ this,
    have hf : ¬injective ι, from set.not_injective_nat_fintype,
    absurd ht hf)
    
--set_option pp.notation false
--set_option pp.implicit true
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
  map_mul := λ {x y}, show (↑(x * y).val : α) = ↑x.val * ↑y.val,     
    begin
      rw[←nat.cast_mul],
      rw[zmod.mul_val],
      --rw[subtype.coe_mk (ring_char α) h],
      sorry
    end,
  map_add := λ x y, sorry }

instance zmod_smul_ring_hom {h : ring_char α > 0} {r : zmod ⟨ring_char α, h⟩} :
is_ring_hom (λ x : α, (nat.cast ∘ fin.val) r * x) := sorry

--noncomputable instance zmod_scalar_pos_char {h : ring_char α > 0} :
--has_scalar (zmod ⟨ring_char α, h⟩) α :=
--{ smul := λ n a, (nat.cast ∘ fin.val) n * a }

open is_ring_hom

--set_option pp.notation false

noncomputable instance zmod_module_pos_char {h : ring_char α > 0} :
module (zmod ⟨ring_char α, h⟩) α :=
module.of_core
{ smul := λ r x, (nat.cast ∘ fin.val) r * x,
  smul_add := λ r x y, map_add _,
  add_smul := λ r s x, show (nat.cast ∘ fin.val) (r + s) * x = _,
    by rw[@map_add _ _ _ _ (nat.cast ∘ fin.val) zmod_ring_hom _ _, add_mul], 
  mul_smul := λ r s x, show (nat.cast ∘ fin.val) (r * s) * x = _,
    by rw[@map_mul _ _ _ _ (nat.cast ∘ fin.val) zmod_ring_hom _ _, mul_assoc], 
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
