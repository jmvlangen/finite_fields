import ring_theory.principal_ideal_domain
import data.zmod.basic

import ring_theory

namespace int

open euclidean_domain ideal is_ring_hom ideal.quotient

lemma gen_ideal_ℤ (I : ideal ℤ) :
∃ n : ℕ, I = span {(n : ℤ)} :=
have ∃ m : ℤ, I = span {m}, from (principal_ideal_domain.principal I).principal,
let ⟨m, _⟩ := this in
have I = span {(nat_abs m : ℤ)}, from
calc
    I = span {m}                                : by assumption
  ... = (span {m}) * ⊤                          : by rw mul_top
  ... = (span {m}) * (span {(norm_unit m : ℤ)}) : by rw [iff.mpr (@span_singleton_eq_top _ _ ↑(norm_unit m)) ⟨(norm_unit m), refl (norm_unit m)⟩]
  ... = span {m * (norm_unit m : ℤ)}            : by simp [span_mul_span]
  ... = span {(nat_abs m : ℤ)}                  : by rw coe_nat_abs_eq_mul_norm_unit,
show ∃ n : ℕ, I = span {(n : ℤ)}, from ⟨nat_abs m, this⟩

lemma gen_prime_ideal_ℤ (I : ideal ℤ) [is_prime I] :
∃ p : ℕ, I = span {(p : ℤ)} ∧ (p = 0 ∨ nat.prime p) :=
have ∃ n : ℕ, I = span {(n : ℤ)}, from gen_ideal_ℤ I,
let ⟨n, h⟩ := this in
or.elim (nat.eq_zero_or_eq_succ_pred n)
  (assume h₀ : n = 0,
   show ∃ p : ℕ, I = span {(p : ℤ)} ∧ (p = 0 ∨ nat.prime p), from  ⟨n, h, or.inl h₀⟩)
  (assume h₁ : n = nat.succ (nat.pred n),
   have n ≠ 0, from eq.symm h₁ ▸ nat.succ_ne_zero (nat.pred n),
   have (n : ℤ) ≠ 0, by simp [this],
   have prime (↑n : ℤ), from iff.mp (span_singleton_prime this) (h ▸ ‹is_prime I›),
   have nat.prime n, from iff.mpr nat.prime_iff_prime_int this,
   show ∃ p : ℕ, I = span {(p : ℤ)} ∧ (p = 0 ∨ nat.prime p), from  ⟨n, h, or.inr this⟩)

lemma maximal_ideal_ℤ (p : ℕ) : nat.prime p → is_maximal (span {(p : ℤ)} : ideal ℤ) :=
assume h₀ : nat.prime p,
have prime (p : ℤ), from iff.mp nat.prime_iff_prime_int h₀,
have irreducible (p : ℤ), from irreducible_of_prime this,
show is_maximal (span {(p : ℤ)}), from principal_ideal_domain.is_maximal_of_irreducible this

lemma gen_maximal_ideal_ℤ (I : ideal ℤ) [is_maximal I] :
∃ p : ℕ, I = span {(p : ℤ)} ∧ nat.prime p :=
have ∃ p : ℕ, I = span {(p : ℤ)} ∧ (p = 0 ∨ nat.prime p), from gen_prime_ideal_ℤ I,
let ⟨p, hI, hp⟩ := this in
or.elim hp
  (assume h₀ : p = 0,
   have (p : ℤ) = 0, by simp [h₀], --nat.cast_eq_zero
   have I = ⊥, from eq.symm hI ▸ iff.mpr span_singleton_eq_bot this,
   let J := (span {(2 : ℤ)} : ideal ℤ) in
   have J ≠ (⊥ : ideal ℤ), from
     assume h₁ : J = ⊥,
     have h2 : (2 : ℤ) = 0, from iff.mp span_singleton_eq_bot h₁,
     have h2n : (2 : ℤ) ≠ 0, from iff.mpr int.coe_nat_ne_zero (nat.succ_ne_zero 1),
     absurd h2 h2n,
   have I < J, from eq.symm ‹I = ⊥› ▸ (iff.mpr lattice.bot_lt_iff_ne_bot ‹J ≠ (⊥ : ideal ℤ)›),
   have J = ⊤, from and.right ‹is_maximal I› J this,
   have (1 : ℤ) ∈ J, from iff.mp (eq_top_iff_one J) this,
   have (2 : ℤ) ∣ 1, from iff.mp mem_span_singleton this,
   have (2 : ℤ) ≤ 1, from int.le_of_dvd int.one_pos this,
   have (2 : ℤ) > 1, from one_lt_two,
   absurd ‹(2 : ℤ) ≤ 1› (not_le_of_gt ‹(2 : ℤ) > 1›))
  (assume h₁ : nat.prime p,
   show ∃ p : ℕ, I = span {(p : ℤ)} ∧ nat.prime p, from ⟨p, hI, h₁⟩)

lemma quotient_equiv (n : ℕ+) : ideal.quotient (@span ℤ _ {(n : ℤ)}) ≃r zmod n :=
let n' : ℤ := n in
let nℤ := @span ℤ _ {n'} in
let ι : ℤ → zmod n := int.cast in
have hI : nℤ ≤ ker ι, from span_le.mpr $ set.singleton_subset_iff.mpr $ mem_ker.mpr $ zmod.eq_zero_iff_dvd_int.mpr $ dvd_refl n,
show quotient nℤ ≃r zmod n, from
{ to_fun := factor ι nℤ hI,
  inv_fun := λ m, ideal.quotient.mk nℤ (m.val),
  left_inv :=
    assume x : quotient nℤ,
    suffices ∀ y : ℤ, (λ m : zmod n, ideal.quotient.mk nℤ (m.val)) ((factor ι nℤ hI) (ideal.quotient.mk nℤ y)) = ideal.quotient.mk nℤ y,
      from quotient.induction_on' x this,
    assume y : ℤ,
    have y - y % n' = n' * (y / n'), from
    calc
      y - y % n' = y % n' + n' * (y / n') - y % n' : by rw (int.mod_add_div y n')
             ... = n' * (y / n')                   : by rw (add_sub_cancel'),
    have n' ∣ y - y % n', from dvd_of_mul_right_eq (y / n') (eq.symm this),
    have n' ∣ y - ((ι y).val : ℤ), from eq.symm (@zmod.coe_val_cast_int n y) ▸ this,
    begin
      unfold,
      rw (factor_commutes hI),
      apply eq.symm,
      apply ideal.quotient.eq.mpr,
      apply mem_span_singleton.mpr,
      assumption,
    end,
  right_inv :=
    assume x : zmod n,
    eq.symm (@factor_commutes _ _ _ _ _ _ _ hI x.val) ▸ zmod.cast_val x,
  hom := factor_to_ring_hom' }

end int
