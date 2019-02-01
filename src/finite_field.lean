import algebra.char_p
import data.zmod.basic
import data.equiv.algebra

import vector_space

universes u v

namespace char_p

variable {α : Type u}
variable [ring α]

open nat

--char_p
lemma char_p_eq_mod (n : ℕ) [char_p α n] (k : ℕ) : (k : α) = (k % n : ℕ) :=
calc (k : α) = (k % n + n * (k / n) : ℕ) : by rw [mod_add_div]
         ... = ↑(k % n) + ↑n * ↑(k / n)  : by rw [cast_add, cast_mul]
         ... = ↑(k % n) + 0              : by rw [char_p.cast_eq_zero α n, zero_mul]
         ... = ↑(k % n)                  : by rw [add_zero]

end char_p

namespace zmod

variable {n : ℕ+}
variable (α : Type u)
variables [ring α]

open char_p nat

--zmod n or char_p
def cast : zmod n → α := nat.cast ∘ fin.val

--zmod n or char_p
instance cast_is_ring_hom [char_p α n] : is_ring_hom (cast α) :=
{ map_one := by rw ←cast_one; exact eq.symm (char_p_eq_mod n 1),
  map_mul := assume x y : zmod n, show ↑((x * y).val) = ↑(x.val) * ↑(y.val), from
    by rw [zmod.mul_val, ←char_p_eq_mod, cast_mul],
  map_add := assume x y : zmod n, show ↑((x + y).val) = ↑(x.val) + ↑(y.val), from
    by rw [zmod.add_val, ←char_p_eq_mod, cast_add] }

open is_ring_hom

--zmod n or char_p
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

instance to_module' {m : ℕ} {hm : m > 0} [hc : char_p α m] : module (zmod ⟨m, hm⟩) α :=
@zmod.to_module ⟨m, hm⟩ α _ hc

end zmod

namespace char_p

variables (α : Type u) [ring α]

open function nat 

--char_p
lemma ne_zero [fintype α] [decidable_eq α] (p : ℕ) [char_p α p] : p ≠ 0 :=
(assume h : p = 0,
have ∀ n : ℕ, (n : α) = 0 → n = 0, from
  assume (n : ℕ) (h₀ : (n : α) = 0),
  have 0 ∣ n, from h ▸ (cast_eq_zero_iff α p n).mp h₀, 
  show n = 0, from zero_dvd_iff.mp this,
have char_zero α, from add_group.char_zero_of_inj_zero this,
have ht :  injective nat.cast, from @cast_injective α _ _ this,
have hf : ¬injective nat.cast, from @set.not_injective_nat_fintype α _ _ _,
absurd ht hf)

end char_p

section integral_domain

variables (α : Type u) [integral_domain α]

open nat function char_p

--integral_domain
lemma char_p_ne_one (p : ℕ) [hc : char_p α p] : p ≠ 1 :=
assume hp : p = 1,
have (↑1 : α) = 0, from (cast_eq_zero_iff α p 1).mpr (hp ▸ (dvd_refl p)),
have ( 1 : α) = 0, from @cast_one α _ _ ▸ this,
absurd this one_ne_zero

--integral_domain
lemma char_p_prime_of_ge_two (p : ℕ) [hc : char_p α p] (hp : p ≥ 2) : nat.prime p :=
suffices ∀d ∣ p, d = 1 ∨ d = p, from ⟨hp, this⟩,
assume (d : ℕ) (hdvd : ∃ e, p = d * e),
let ⟨e, hmul⟩ := hdvd in
have (p : α) = 0, from (cast_eq_zero_iff α p p).mpr (dvd_refl p),
have (d : α) * e = 0, from (@cast_mul α _ d e) ▸ (hmul ▸ this),
or.elim (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero (d : α) e this)
  (assume hd : (d : α) = 0,
  have p ∣ d, from (cast_eq_zero_iff α p d).mp hd,
  show d = 1 ∨ d = p, from or.inr (dvd_antisymm ⟨e, hmul⟩ this))
  (assume he : (e : α) = 0,
  have p ∣ e, from (cast_eq_zero_iff α p e).mp he,
  have e ∣ p, from dvd_of_mul_left_eq d (eq.symm hmul),
  have e = p, from dvd_antisymm ‹e ∣ p› ‹p ∣ e›,
  have h₀ : p > 0, from gt_of_ge_of_gt hp (nat.zero_lt_succ 1),
  have d * p = 1 * p, by rw ‹e = p› at hmul; rw [one_mul]; exact eq.symm hmul,
  show d = 1 ∨ d = p, from or.inl (eq_of_mul_eq_mul_right h₀ this))

--integral_domain
lemma char_p_prime_or_zero (p : ℕ) [hc : char_p α p] : nat.prime p ∨ p = 0 :=
match p, hc with
| 0,     _  := or.inr rfl
| 1,     hc := absurd (eq.refl (1 : ℕ)) (@char_p_ne_one α _ (1 : ℕ) hc)
| (m+2), hc := or.inl (@char_p_prime_of_ge_two α _ (m+2) hc (nat.le_add_left 2 m))
end

--integral_domain
lemma char_p_prime [fintype α] [decidable_eq α] (p : ℕ) [char_p α p] : nat.prime p :=
or.resolve_right (char_p_prime_or_zero α p) (char_p.ne_zero α p)

lemma ring_char_prime [fintype α] [decidable_eq α] : nat.prime (ring_char α) :=
@char_p_prime α _ _ _ (ring_char α) ⟨ring_char.spec α⟩

end integral_domain

namespace finite_field

open fintype

variables (α : Type u) {β : Type v}
variables [discrete_field α] [fintype α]
variables [discrete_field β] [fintype β]

--finite field
theorem fin_field_card (p : ℕ) [char_p α p] :
∃ (n : ℕ+), nat.prime p ∧ card α = p^(n : ℕ) :=
have hp : nat.prime p, from char_p_prime α p,
have V : vector_space (zmodp p hp) α, from {..zmod.to_module' α},
let ⟨n, h⟩ := @vector_space.card_fin _ _ _ _ _ _ V _ in
have hn : n > 0, from or.resolve_left (nat.eq_zero_or_pos n)
  (assume h0 : n = 0,
  have card α = 1, by rw[←nat.pow_zero (card _), ←h0]; exact h,
  have (1 : α) = 0, from (fintype.card_le_one_iff.mp (le_of_eq this)) 1 0,
  absurd this one_ne_zero),
⟨⟨n, hn⟩, hp, fintype.card_fin p ▸ h⟩

theorem fin_field_card_exists :
∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ card α = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists α in
⟨p, @fin_field_card α _ _ p hc⟩

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
