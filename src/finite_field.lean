import ring_theory.algebra
import field_theory.finite
import ring_theory.ideals
import algebra.euclidean_domain
import ring_theory.principal_ideal_domain

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
     have 2 = 0, from sorry, --iff.mp (is_principal.eq_bot_iff_generator_eq_zero J) h₁,
     show false, from sorry,
   show ∃ p : ℕ, I = span {(p : ℤ)} ∧ nat.prime p, from sorry)
  (assume h₁ : nat.prime p,
   show ∃ p : ℕ, I = span {(p : ℤ)} ∧ nat.prime p, from ⟨p, hI, h₁⟩)

end int

namespace ring

open function

class iso (α : Type u) (β : Type v) [ring α] [ring β] :=
(to_fun : α → β)
[is_hom : is_ring_hom to_fun]
(inv_fun : β → α)
(left_inv : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

infix ` ≅ `:20 := iso

variables {α : Type u} {β : Type v} {γ : Type w}
variables [ring α] [ring β] [ring γ]

def refl (α : Type u) [ring α] : α ≅ α :=
sorry

def symm (e : α ≅ β) : β ≅ α :=
sorry

def trans (e₁ : α ≅ β) (e₂ : β ≅ γ) : α ≅ γ :=
sorry

end ring

namespace ideal

variables {α : Type u} {β : Type v}
variables [comm_ring α] [comm_ring β]

/-- The pullback of an ideal under a ring homomorphism --/
def comap (f : α → β) [is_ring_hom f] (I : ideal β) : ideal α :=
{carrier := f ⁻¹' I,
 zero := by rw [set.mem_preimage_eq, is_add_group_hom.zero f]; exact I.zero,
 add := 
 assume x y _ _,
 have f x ∈ I, from eq.mp set.mem_preimage_eq ‹x ∈ f ⁻¹' I›,
 have f y ∈ I, from eq.mp set.mem_preimage_eq ‹y ∈ f ⁻¹' I›,
 have f x + f y ∈ I, from I.add ‹f x ∈ I› ‹f y ∈ I›,
 show f (x + y) ∈ I, from eq.substr (is_add_group_hom.add f x y) ‹f x + f y ∈ I›,
 smul := 
 assume c x _,
 have f x ∈ I, from eq.mp set.mem_preimage_eq ‹x ∈ f ⁻¹' I›,
 have (f c) • (f x) ∈ I, from I.smul (f c) ‹f x ∈ I›,
 show f (c • x) ∈ I, from eq.substr (@is_ring_hom.map_mul _ _ _ _ f _ c x) ‹(f c) • (f x) ∈ I›}

def comap_prime (f : α → β) [is_ring_hom f] (I : ideal β) [is_prime I] : is_prime (comap f I) :=
have proper : comap f I ≠ ⊤, from
  assume h : comap f I = ⊤,
  have (1 : α) ∈ comap f I, from iff.mp (ideal.eq_top_iff_one (comap f I)) h,
  have f 1 ∈ I, from eq.mp set.mem_preimage_eq ‹(1 : α) ∈ f ⁻¹' I›,
  have (1 : β) ∈ I, from eq.subst (is_ring_hom.map_one f) ‹f 1 ∈ I›,
  have I = ⊤, from iff.mpr (ideal.eq_top_iff_one I) ‹(1 : β) ∈ I›,
  show false, from ‹is_prime I›.left ‹I = ⊤›,
have mult : ∀ x y : α, x * y ∈ comap f I → x ∈ comap f I ∨ y ∈ comap f I, from
  assume x y _,
  have f (x * y) ∈ I, from eq.mp set.mem_preimage_eq ‹x * y ∈ f ⁻¹' I›,
  have f x * f y ∈ I, from eq.subst (@is_ring_hom.map_mul _ _ _ _ f _ x y) ‹f (x * y) ∈ I›,
  have f x ∈ I ∨ f y ∈ I, from ‹is_prime I›.right ‹f x * f y ∈ I›,
  or.elim ‹f x ∈ I ∨ f y ∈ I›
    (assume _ : f x ∈ I,
     have x ∈ comap f I, from eq.mp set.mem_preimage_eq ‹f x ∈ I›,
     show x ∈ comap f I ∨ y ∈ comap f I, from or.inl this)
    (assume _ : f y ∈ I,
     have y ∈ comap f I, from eq.mp set.mem_preimage_eq ‹f y ∈ I›,
     show x ∈ comap f I ∨ y ∈ comap f I, from or.inr this),
show is_prime (comap f I), from ⟨proper, mult⟩

end ideal

namespace finite_field

open fintype field ring ideal

variables {α : Type u} {β : Type v}
variables [field α] [fintype α]
variables [field β] [fintype β]

theorem fin_field_card (α : Type*) [field α] [fintype α] : ∃ p n : ℕ, prime p ∧ card α = p^n :=
have alg_ℤ : algebra ℤ α, from ring.to_ℤ_algebra α,
let ι : ℤ → α := alg_ℤ.to_fun in
have is_ring_hom ι, from alg_ℤ.hom,
have ∃ p : ℕ, prime p ∧ ideal.comap ι (⊥ : ideal α) = span {(p : ℤ)}, from sorry,
sorry

theorem exists_fin_field : ∀ p n : ℕ, prime p → ∃ α : Type*, ∃ [hf : field α], ∃ [hfin : fintype α], @card α hfin = p^n :=
sorry

theorem unique_fin_field [field α] [field β] : card α = card β → (α ≅ β) :=
sorry

end finite_field
