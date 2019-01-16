import ring_theory.algebra
import ring_theory.ideals
import ring_theory.principal_ideal_domain
import ring_theory.ideal_operations
import field_theory.finite
import algebra.euclidean_domain
import algebra.module
import algebra.ring
import set_theory.cardinal
import linear_algebra.dimension
import linear_algebra.basic
import linear_algebra.basis
import data.finset
import data.equiv.algebra
import ring_theory
import group_theory.subgroup

universes u v w

namespace int

open euclidean_domain ideal

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

end int

namespace ideal

variable {α : Type u}
variable [comm_ring α]

lemma mem_of_not_bot (I : ideal α) : I ≠ (⊥ : ideal α) → ∃ x ∈ I, (x : α) ≠ 0 :=
assume h : I ≠ ⊥,
have ¬ (∀ x : α, x ∈ I ↔ x ∈ (⊥ : ideal α)), from mt submodule.ext h,
have ∃ x : α, ¬ (x ∈ I ↔ x ∈ (⊥ : ideal α)), from classical.not_forall.mp this,
let ⟨x, h₁⟩ := this in
have x ≠ 0, from
  assume h0 : x = 0,
  have x ∈ I, from (eq.symm h0 ▸ ideal.zero_mem I),
  have x ∈ (⊥ : ideal α), from (eq.symm h0 ▸ ideal.zero_mem (⊥ : ideal α)),
  have x ∈ I ↔ x ∈ (⊥ : ideal α),
    from iff_of_true ‹x ∈ I› ‹x ∈ (⊥ : ideal α)›,
  absurd this h₁,
have ¬ (x ∈ (⊥ : ideal α)), from mt submodule.mem_bot.mp this,
have x ∈ I, from classical.not_not.mp
  (assume hI : ¬ (x ∈ I),
   absurd (iff_of_false hI ‹¬(x ∈ (⊥ : ideal α))›) h₁),
show ∃ x ∈ I, (x : α) ≠ 0, from ⟨x, ‹x ∈ I›, ‹x ≠ 0›⟩

end ideal

namespace is_ring_hom

variables {α : Type u} {β : Type v}
variables [comm_ring α] [comm_ring β]

def ker (f : α → β) [is_ring_hom f] : ideal α := ideal.comap f ⊥

lemma ker_eq_bot {f : α → β} [is_ring_hom f] (h : ker f = ⊥) : function.injective f :=
(is_add_group_hom.injective_iff _).2
  (λ a ha, by rw[←submodule.mem_bot, ←h]; constructor; exact ha)

end is_ring_hom

namespace field

open ideal

variable {α : Type u}
variable [field α]

def ne_bot_is_top : ∀ I : ideal α, I ≠ ⊥ → I = ⊤ :=
assume I : ideal α,
assume h : I ≠ ⊥,
have ∃ x ∈ I, (x : α) ≠ (0 : α), from mem_of_not_bot I h,
let ⟨x, hI, h0⟩ := this in
have is_unit x, from is_unit_of_mul_one x (x⁻¹) (field.mul_inv_cancel h0),
show I = ⊤, from eq_top_of_is_unit_mem I hI this

def bot_is_max : is_maximal (⊥ : ideal α) :=
have h₁ : (⊥ : ideal α) ≠ (⊤ : ideal α), from
  assume h : (⊥ : ideal α) = (⊤ : ideal α),
  have (1 : α) ∈ (⊥ : ideal α), from iff.mp (eq_top_iff_one (⊥ : ideal α)) h,
  have (1 : α) = 0, from iff.mp submodule.mem_bot this,
  absurd this one_ne_zero,
have h₂ : ∀ I : ideal α, ⊥ < I → I = ⊤, from 
  assume I : ideal α,
  assume hI : ⊥ < I,
  have I ≠ ⊥, from lattice.bot_lt_iff_ne_bot.mp hI,
  show I = ⊤, from ne_bot_is_top I this,
show is_maximal (⊥ : ideal α), from ⟨h₁, h₂⟩

def bot_is_prime : is_prime (⊥ : ideal α) :=
is_maximal.is_prime bot_is_max

end field

namespace vector_space
 
open fintype vector_space cardinal submodule set function
 
variables (α : Type u) (β : Type v)
variables [discrete_field α] [fintype α]
variables [add_comm_group β] [fintype β]
variables [vector_space α β]
 
include α β 
 
lemma dim_fin : ∃ n : ℕ, dim α β = n :=
let ⟨b, hb⟩ := exists_is_basis β in
have dim α β < omega, from
  calc dim α β = cardinal.mk b : by rw[is_basis.mk_eq_dim hb]
           ... ≤ cardinal.mk β : le_mk_iff_exists_set.mpr ⟨b, rfl⟩
           ... = card β        : fintype_card _
           ... < omega         : nat_lt_omega _,
lt_omega.mp this
 
variables (b : set β) (hb : is_basis b)
 
/-#check fintype.card
#check is_basis.repr_range
#check (module_equiv_lc hb).to_equiv.bijective
#check linear_map.range_eq_top-/
 
lemma card_fin_vector_space : ∃ n : ℕ, card β = (card α) ^ n :=
let ⟨n, hn⟩ := dim_fin α β in
⟨n,
let ⟨b, hb⟩ := exists_is_basis β in
/-have fb : fintype b, from (finite.of_fintype b).fintype,
have h1 : β ≃ (b → α), from sorry,
have h2 : n = @fintype.card b fb, from sorry,
have db : decidable_eq b, from sorry,
calc card β = @card (b → α) (fintype.of_equiv β h1) : eq.symm $ fintype.of_equiv_card h1
        ... = card α ^ @card b fb : @fintype.card_fun b α fb db _
        ... = (card α) ^ n : by rw[h2]-/
sorry
⟩
 
end vector_space

namespace finite_field

open fintype field ring ideal is_group_hom

variables {α : Type u} {β : Type v}
variables [field α] [fintype α]
variables [field β] [fintype β]

theorem fin_field_card (α : Type*) [discrete_field α] [fintype α] : ∃ p n : ℕ, prime p ∧ card α = p^n :=
have alg_ℤ : algebra ℤ α, from ring.to_ℤ_algebra α,
let ι : ℤ → α := alg_ℤ.to_fun in
let I := is_ring_hom.ker ι in
have is_prime I,
  from @is_prime.comap _ _ _ _ ι _ _ field.bot_is_prime,
have ∃ p : ℕ, I = span {(p : ℤ)} ∧ (p = 0 ∨ nat.prime p),
  from @int.gen_prime_ideal_ℤ I this,
let ⟨p, hI, hp⟩ := this in
or.elim hp
  (assume h0 : p = 0,
  have I = ⊥, by rw [hI, span_singleton_eq_bot]; simpa,
  have function.injective ι, from is_ring_hom.ker_eq_bot this,
  absurd this set.not_injective_int_fintype)
  (assume hprime : nat.prime p,
   have is_maximal I, from eq.symm hI ▸ int.maximal_ideal_ℤ p hprime,
   let F := I.quotient in
   have field F, from @quotient.field _ _ I ‹is_maximal I›,
   have ∀ x : ℤ, x ∈ I → ι x = 0, from
     assume x : ℤ,
     assume hI : x ∈ I,
     have ι x ∈ (⊥ : ideal α), from eq.mp set.mem_preimage_eq hI,
     show ι x = 0, from submodule.mem_bot.mp this,
   have algebra.core F α, from
     { to_fun := @ideal.quotient.lift _ _ _ _ I ι _ this,
       hom :=  ideal.quotient.is_ring_hom},
   have algebra F α, from algebra.of_core this,
   sorry) --Do more!

theorem exists_fin_field : ∀ p n : ℕ, prime p → ∃ α : Type*, ∃ [hf : field α], ∃ [hfin : fintype α], @card α hfin = p^n :=
sorry

theorem unique_fin_field [field α] [field β] : card α = card β → (α ≃r β) :=
sorry

end finite_field
