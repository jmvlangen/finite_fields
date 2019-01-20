import ring_theory.principal_ideal_domain
import data.zmod.basic

import ring_theory

namespace int

open euclidean_domain ideal is_ring_hom ideal.quotient

def nℤ (n : ℕ) : ideal ℤ := span {(n : ℤ)}

lemma nℤ_maximal (p : ℕ) : nat.prime p → is_maximal (nℤ p) :=
assume h₀ : nat.prime p,
have prime (p : ℤ), from iff.mp nat.prime_iff_prime_int h₀,
have irreducible (p : ℤ), from irreducible_of_prime this,
show is_maximal (nℤ p), from principal_ideal_domain.is_maximal_of_irreducible this

lemma bot_not_maximal : ¬(is_maximal (⊥ : ideal ℤ)) :=
assume h : is_maximal ⊥,
let J := nℤ 2 in
have J ≠ (⊥ : ideal ℤ), from
  assume h₁ : J = ⊥,
  have h2 : (2 : ℤ) = 0, from iff.mp span_singleton_eq_bot h₁,
  have h2n : (2 : ℤ) ≠ 0, from iff.mpr int.coe_nat_ne_zero (nat.succ_ne_zero 1),
  absurd h2 h2n,
have ⊥ < J, from (iff.mpr lattice.bot_lt_iff_ne_bot ‹J ≠ (⊥ : ideal ℤ)›),
have J = ⊤, from and.right ‹is_maximal ⊥› J this,
have J ≠ ⊤, from and.left (nℤ_maximal 2 nat.prime_two),
absurd ‹J = ⊤› ‹J ≠ ⊤›

lemma ideal_eq_nℤ (I : ideal ℤ) : ∃ n : ℕ, I = nℤ n :=
have ∃ m : ℤ, I = span {m}, from (principal_ideal_domain.principal I).principal,
let ⟨m, _⟩ := this in
have I = nℤ (nat_abs m), from
calc
    I = span {m}                                : by assumption
  ... = (span {m}) * ⊤                          : by rw mul_top
  ... = (span {m}) * (span {(norm_unit m : ℤ)}) : by rw [iff.mpr (@span_singleton_eq_top _ _ ↑(norm_unit m)) ⟨(norm_unit m), refl (norm_unit m)⟩]
  ... = span {m * (norm_unit m : ℤ)}            : by simp [span_mul_span]
  ... = span {(nat_abs m : ℤ)}                  : by rw coe_nat_abs_eq_mul_norm_unit,
show ∃ n : ℕ, I = nℤ n, from ⟨nat_abs m, this⟩

lemma prime_ideal_eq_nℤ (I : ideal ℤ) [is_prime I] :
∃ p : ℕ, I = nℤ p ∧ (p = 0 ∨ nat.prime p) :=
have ∃ n : ℕ, I = nℤ n, from ideal_eq_nℤ I,
let ⟨n, h⟩ := this in
or.elim (nat.eq_zero_or_eq_succ_pred n)
  (assume h₀ : n = 0,
   show ∃ p : ℕ, I = nℤ p ∧ (p = 0 ∨ nat.prime p), from  ⟨n, h, or.inl h₀⟩)
  (assume h₁ : n = nat.succ (nat.pred n),
   have n ≠ 0, from eq.symm h₁ ▸ nat.succ_ne_zero (nat.pred n),
   have (n : ℤ) ≠ 0, from λ h, this (int.of_nat.inj h),
   have is_prime (nℤ n), from h ▸ ‹is_prime I›,
   have prime (n : ℤ), from iff.mp (span_singleton_prime ‹(n : ℤ) ≠ 0›) this,
   have nat.prime n, from iff.mpr nat.prime_iff_prime_int this,
   show ∃ p : ℕ, I = nℤ p ∧ (p = 0 ∨ nat.prime p), from  ⟨n, h, or.inr this⟩)

lemma maximal_ideal_eq_nℤ (I : ideal ℤ) [is_maximal I] :
∃ p : ℕ, I = nℤ p ∧ nat.prime p :=
have ∃ p : ℕ, I = nℤ p ∧ (p = 0 ∨ nat.prime p), from prime_ideal_eq_nℤ I,
let ⟨p, hI, hp⟩ := this in
or.elim hp
  (assume h₀ : p = 0,
   have (p : ℤ) = 0, from int.of_nat.inj_eq.mpr h₀,
   have I = ⊥, from eq.symm hI ▸ iff.mpr span_singleton_eq_bot this,
   absurd ‹is_maximal I› (eq.symm this ▸ bot_not_maximal))
  (assume h₁ : nat.prime p,
   show ∃ p : ℕ, I = nℤ p ∧ nat.prime p, from ⟨p, hI, h₁⟩)

def ℤmodnℤ (n : ℕ) : Type* := ideal.quotient (nℤ n)

instance ℤmodnℤ_comm_ring (n : ℕ) : comm_ring (ℤmodnℤ n) :=
ideal.quotient.comm_ring (nℤ n)

def ℤmodnℤ_equiv_zmod (n : ℕ+) : ℤmodnℤ n ≃r zmod n :=
let n' : ℤ := n in
let ι : ℤ → zmod n := int.cast in
have hI : (nℤ n) ≤ ker ι, from span_le.mpr $ set.singleton_subset_iff.mpr $ mem_ker.mpr $ zmod.eq_zero_iff_dvd_int.mpr $ dvd_refl n,
show quotient (nℤ n) ≃r zmod n, from
{ to_fun := factor ι (nℤ n) hI,
  inv_fun := λ m, ideal.quotient.mk (nℤ n) (m.val),
  left_inv :=
    assume x : quotient (nℤ n),
    suffices ∀ y : ℤ, (λ m : zmod n, ideal.quotient.mk (nℤ n) (m.val)) ((factor ι (nℤ n) hI) (ideal.quotient.mk (nℤ n) y)) = ideal.quotient.mk (nℤ n) y,
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

def zmod_equiv_ℤmodnℤ (n : ℕ+) : zmod n ≃r ℤmodnℤ n :=
ring_equiv.symm (ℤmodnℤ_equiv_zmod n)

instance ℤmodnℤ_fintype (n : ℕ+) : fintype (ℤmodnℤ n) :=
(fintype.of_equiv (zmod n) $ ring_equiv.to_equiv $ zmod_equiv_ℤmodnℤ n)

lemma quotient_nℤ_card (n : ℕ+) : fintype.card (ℤmodnℤ n) = n :=
have h₁ : fintype.card (ℤmodnℤ n) = fintype.card (zmod n), from (fintype.of_equiv_card $ ring_equiv.to_equiv $ zmod_equiv_ℤmodnℤ n),
have h₂ : fintype.card (zmod n) = n, from zmod.card_zmod n,
show fintype.card (ℤmodnℤ n) = n, from eq.trans h₁ h₂

--def ℤmodnℤ_equiv_zmodp (p : ℕ) (hp : nat.prime p) : (ℤmodnℤ p) ≃r zmodp p hp :=
--ℤmodnℤ_equiv_zmod ⟨p, hp.pos⟩

end int
