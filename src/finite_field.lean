import algebra.char_p
import data.zmod.basic
import data.equiv.algebra

import vector_space

universes u v

namespace char_p

variable {α : Type u}
variable [ring α]

open nat

lemma char_p_eq_mod (n : ℕ) [char_p α n] (k : ℕ) : (k : α) = (k % n : ℕ) :=
calc
  (k : α) = (k % n + n * (k / n) : ℕ)   : by rw [mod_add_div k n]
      ... = ↑(k % n) + ↑(n * (k / n)) : by rw [cast_add (k % n) (n * (k / n))]
      ... = ↑(k % n) + 0               : by rw [(cast_eq_zero_iff α n (n * (k / n))).mpr (dvd_mul_right n (k / n))]
      ... = ↑(k % n)                   : by rw [add_zero]

end char_p

namespace zmod

variable {n : ℕ+}
variable (α : Type u)
variables [ring α]

open char_p nat

def cast : zmod n → α := nat.cast ∘ fin.val

instance cast_is_ring_hom [char_p α n] : is_ring_hom (cast α) :=
{ map_one := 
    calc
      ((1 : zmod n).val : α) = ↑(1 % n : ℕ) : rfl
                         ... = ↑(1 : ℕ)     : eq.symm (char_p_eq_mod n 1)
                         ... = (1 : α)       : cast_one,
  map_mul := assume x y : zmod n,
    calc
      ↑((x * y).val) = ↑((x.val * y.val) % n) : by rw [zmod.mul_val x y]
                  ... = ↑(x.val * y.val)       : eq.symm (char_p_eq_mod n (x.val * y.val))
                  ... = ↑(x.val) * ↑(y.val)   : cast_mul x.val y.val,
  map_add := assume x y : zmod n,
    calc
      (↑((x + y).val) : α) = ↑((x.val + y.val) % n) : by rw [zmod.add_val x y]
                        ... = ↑(x.val + y.val)       : eq.symm (char_p_eq_mod n _)
                        ... = ↑(x.val) + ↑(y.val)   : cast_add x.val y.val}

open is_ring_hom

instance to_module [char_p α n] : module (zmod n) α :=
module.of_core
{ smul := λ r x, (cast α) r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw[mul_add]; refl,
  add_smul := λ r s x, by unfold has_scalar.smul;
    rw[map_add (cast α), add_mul]; apply_instance,
  mul_smul := λ r s x, by unfold has_scalar.smul;
    rw[map_mul (cast α), mul_assoc]; apply_instance,
  one_smul := λ x, show (cast α) 1 * x = _,
    by rw[map_one (cast α), one_mul]; apply_instance }

end zmod

namespace nat

lemma eq_of_dvd_of_dvd {m n : ℕ} : m ∣ n → n ∣ m → m = n :=
assume h₁ : m ∣ n,
assume h₂ : n ∣ m,
or.elim (eq_zero_or_pos m)
  (assume hm : m = 0,
   have hn : n = 0, from eq_zero_of_zero_dvd (hm ▸ h₁),
   show m = n, from eq.symm hn ▸ hm)
  (assume hm : m > 0,
   have hn : n > 0, from pos_of_dvd_of_pos h₂ hm,
   have m ≤ n, from le_of_dvd hn h₁,
   have m ≥ n, from le_of_dvd hm h₂,
   show m = n, from eq_iff_le_not_lt.mpr ⟨‹m ≤ n›, not_lt_of_ge ‹m ≥ n›⟩)

end nat

section integral_domain

variables (α : Type u) [integral_domain α]

open nat function

lemma char_p_prime_or_zero (p : ℕ) [char_p α p]: nat.prime p ∨ p = 0 :=
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
           have d = p, from eq_of_dvd_of_dvd ‹d ∣ p› ‹p ∣ d›,
           show d = 1 ∨ d = p, from or.inr ‹d = p›)
          (assume he : (e : α) = 0,
           have p ∣ e, from (char_p.cast_eq_zero_iff α p e).mp he,
           have e ∣ p, from dvd_of_mul_left_eq d (eq.symm hmul),
           have e = p, from eq_of_dvd_of_dvd ‹e ∣ p› ‹p ∣ e›,
           have d * p = 1 * p, from
             calc
               d * p = d * e : by rw ‹e = p›
                 ... = p     : by rw hmul
                 ... = 1 * p : by rw one_mul, 
           have d = 1, from nat.eq_of_mul_eq_mul_right ‹p > 0› this,
           show d = 1 ∨ d = p, from or.inl ‹d = 1›),
      have nat.prime p, from ⟨‹p ≥ 2›, this⟩,
      show nat.prime p ∨ p = 0, from or.inl this))

lemma char_p_prime [fintype α] [decidable_eq α] (p : ℕ) [char_p α p] : nat.prime p :=
have nat.prime p ∨ p = 0, from char_p_prime_or_zero α p,
or.resolve_right this
   (assume h : p = 0,
    let ι : ℕ → α := nat.cast in
    have ∀ n : ℕ, (n : α) = 0 → n = 0, from
      assume n : ℕ,
      assume h₀ : (n : α) = 0,
      have 0 ∣ n, from h ▸ (char_p.cast_eq_zero_iff α p n).mp h₀, 
      show n = 0, from zero_dvd_iff.mp this,
    have char_zero α, from add_group.char_zero_of_inj_zero this,
    have ht : injective ι, from @cast_injective α _ _ this,
    have hf : ¬injective ι, from set.not_injective_nat_fintype,
    absurd ht hf)

end integral_domain

namespace finite_field

open fintype

variables {α : Type u} {β : Type v}
variables [discrete_field α] [fintype α]
variables [discrete_field β] [fintype β]

theorem fin_field_card (α : Type u) [discrete_field α] [fintype α] :
∃ n : ℕ+, card α = (ring_char α)^(n : ℕ) :=
begin
  let r := ring_char α,
  haveI := (⟨ring_char.spec α⟩ : char_p α r),
  have hp : nat.prime r, from char_p_prime α r,
  haveI := (⟨ring_char.spec α⟩ : char_p α ↑(⟨r, hp.pos⟩ : ℕ+)),
  let F := zmodp r hp,
  haveI := @vector_space.mk F α _ _ (zmod.to_module α), 
  cases vector_space.card_fin F α with n h,
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
⟨ring_char α, n, @char_p_prime α _ _ _ (ring_char α) ⟨ring_char.spec α⟩, h⟩

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
