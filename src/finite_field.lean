import algebra.char_p
import data.zmod.basic

import field
import vector_space

universes u v

section integral_domain

variables {α : Type u} [integral_domain α]

open nat

lemma char_p_prime_or_zero {p : ℕ} [char_p α p]: nat.prime p ∨ p = 0 :=
or.elim (nat.eq_zero_or_eq_succ_pred p)
  (assume h₀ : p = 0,
   show nat.prime p ∨ p = 0, from or.inr h₀)
  (assume h₀ : p = succ (pred p),
   or.elim (nat.eq_zero_or_eq_succ_pred (pred p))
     (assume h₁ : pred p = 0,
      have p = 1, from (h₁ ▸ h₀ : p = succ 0),
      have p ∣ 1, from eq.symm this ▸ one_dvd 1,
      have (nat.cast 1 : α) = 0, from (char_p.cast_eq_zero_iff α p 1).mpr this,
      have (1 : α) = 0, from @cast_one α _ _ ▸ this,
      absurd this one_ne_zero)
     (assume h₁ : pred p = succ (pred (pred p)),
      have p = (succ $ succ $ pred $ pred p), from h₁ ▸ h₀,
      have p ≥ 2, from eq.symm this ▸ (succ_le_succ $ succ_le_succ $ nat.zero_le (pred (pred p))),
      have ∀ d ∣ p, d = 1 ∨ d = p, from
        assume d : ℕ,
        assume hdvd : ∃ e : ℕ, p = d * e,
        let ⟨e, hmul⟩ := hdvd in
        have p > 0, from gt_of_ge_of_gt ‹p ≥ 2› (nat.zero_lt_succ 1),
        have (p : α) = 0, from (char_p.cast_eq_zero_iff α p p).mpr (dvd_refl p),
        have (d : α) * e = 0, from (@cast_mul α _ d e) ▸ (hmul ▸ this),
        or.elim (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero (d : α) e this)
          (assume hd : (d : α) = 0,
           have p ∣ d, from (char_p.cast_eq_zero_iff α p d).mp hd,
           have d > 0, from pos_of_dvd_of_pos hdvd ‹p > 0›, 
           have d ≥ p, from le_of_dvd ‹d > 0› ‹p ∣ d›,
           have d ≤ p, from le_of_dvd ‹p > 0› ‹d ∣ p›,
           have d = p, from eq_iff_le_not_lt.mpr ⟨‹d ≤ p›, not_lt_of_ge ‹d ≥ p›⟩,
           show d = 1 ∨ d = p, from or.inr ‹d = p›)
          (assume he : (e : α) = 0,
           have p ∣ e, from (char_p.cast_eq_zero_iff α p e).mp he,
           have e ∣ p, from dvd_of_mul_left_eq d (eq.symm hmul),
           have e > 0, from pos_of_dvd_of_pos ‹e ∣ p› ‹p > 0›,
           have e ≥ p, from le_of_dvd ‹e > 0› ‹p ∣ e›,
           have e ≤ p, from le_of_dvd ‹p > 0› ‹e ∣ p›,
           have e = p, from eq_iff_le_not_lt.mpr ⟨‹e ≤ p›, not_lt_of_ge ‹e ≥ p›⟩,
           have d * p = 1 * p, from
             calc
               d * p = d * e : by rw ‹e = p›
                 ... = p     : by rw hmul
                 ... = 1 * p : by rw one_mul, 
           have d = 1, from nat.eq_of_mul_eq_mul_right ‹p > 0› this,
           show d = 1 ∨ d = p, from or.inl ‹d = 1›),
      have nat.prime p, from ⟨‹p ≥ 2›, this⟩,
      show nat.prime p ∨ p = 0, from or.inl this))

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
variables [discrete_field β] [fintype β]

theorem fin_field_card (α : Type u) [discrete_field α] [fintype α] :
∃ n : ℕ+, card α = (ring_char α)^(n : ℕ) :=
begin
  haveI := (⟨ring_char.spec α⟩ : char_p α (ring_char α)),
  let F := zmodp (ring_char α) (@char_p_prime α _ _ _ _),
  have V : vector_space F α, from @vector_space.mk F α _ _ zmod_module_pos_char,
  cases @vector_space.card_fin_vector_space F α _ _ _ _ V _ with n h,
  have hn : n > 0, from or.resolve_left (nat.eq_zero_or_pos n)
    (assume h0,
    have card α = 1, by rw[←nat.pow_zero (card F), ←h0]; exact h,
    have (1 : α) = 0, from (fintype.card_le_one_iff.mp (le_of_eq this)) 1 0,
    absurd this one_ne_zero),
  exact ⟨⟨n, hn⟩, fintype.card_fin (ring_char α) ▸ h⟩
end

theorem fin_field_card' (α : Type u) [discrete_field α] [fintype α] :
∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ card α = p^(n : ℕ) :=
let ⟨n, h⟩ := fin_field_card α in
⟨ring_char α, n, @char_p_prime α _ _ (ring_char α) ⟨ring_char.spec α⟩, h⟩

theorem finite_field.exists : ∀ (p : ℕ) (n : ℕ+), nat.prime p →
∃ (α : Type*) [hf : field α] [hfin : fintype α], @card α hfin = p^(n : ℕ) :=
sorry

theorem finite_field.unique : card α = card β → (α ≃r β) :=
sorry


def fin_field (p : ℕ) (n : ℕ+) {hp : nat.prime p} :=
classical.some (finite_field.exists p n hp)

notation `𝔽_[` p `;` n `]` := fin_field p n --find better notation?

variables {p : ℕ} {n : ℕ+} {hp : nat.prime p}

noncomputable instance : field 𝔽_[p;n] :=
classical.some (classical.some_spec (finite_field.exists p n hp))

noncomputable instance : fintype 𝔽_[p;n] :=
classical.some (classical.some_spec $ classical.some_spec (finite_field.exists p n hp))

end finite_field
