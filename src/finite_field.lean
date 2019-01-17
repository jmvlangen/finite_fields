import set_theory.cardinal
import linear_algebra.dimension

import integer
import field

universes u v w

namespace finsupp
/-
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)
-/

variables {α : Type u} {β : Type v}
variables [fintype α] [decidable_eq α]
variables [fintype β] [decidable_eq β] [has_zero β]

instance decidable_mem_fun {α : Type*} [decidable_eq α] (s : finset α): decidable_pred (λ a, a ∈ s) :=
assume a, finset.decidable_mem a s

--if ha : a = 0 then 0 else classical.some (exists_inv ha)


--∀a, a ∈ support ↔ to_fun a ≠ 0

lemma subtype_domain_extend (p : α → Prop) [decidable_pred p] (f : subtype p →₀ β) : α →₀ β :=
{ support            := finset.map ⟨subtype.val, subtype.val_injective⟩ f.support,
  to_fun             := λ a, if h : p a then f ⟨a, h⟩ else 0,
  mem_support_to_fun := λ a,
    iff.intro
    (assume hmap,
    let ⟨ap, hap, _⟩ := finset.mem_map.mp hmap in
    have h : (if h : p a then f ⟨a, h⟩ else 0) = f ap, from sorry,
    by rw[h]; exact (mem_support_to_fun f ap).mp hap)
    (sorry) }


lemma finsupp_fin_support (b : finset α) : {l : α →₀ β // l.support ⊆ b} ≃ ({x // x ∈ b} →₀ β) :=
{ to_fun    := (finsupp.subtype_domain (λ a, a ∈ b)) ∘ subtype.val,
  inv_fun   := sorry,--λ f, ⟨on_finset b (λ a : α, if h : a ∈ b then f ⟨a, h⟩ else 0) (λ a, ), sorry⟩,
  left_inv  := sorry,
  right_inv := sorry
}

end finsupp

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
 
--variables (b : set β) (hb : is_basis b)
 
/-#check fintype.card
#check is_basis.repr_range
#check (module_equiv_lc hb).to_equiv.bijective
#check linear_map.range_eq_top-/
 
#check module_equiv_lc
#check linear_equiv.to_equiv


lemma card_fin_vector_space : ∃ n : ℕ, card β = (card α) ^ n :=
let ⟨n, hn⟩ := dim_fin α β in
⟨n,
let ⟨b, hb⟩ := exists_is_basis β in
have f : β ≃ lc.supported b, from (module_equiv_lc hb).to_equiv,
have g : lc.supported b ≃ (lc.supported b).carrier, from sorry, --⟨submodule.carrier, ⟩,
have β ≃ {l : lc α β | ↑l.support ⊆ b}, from equiv.trans f g,

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
variables [discrete_field α] [fintype α]
variables [field β] [fintype β]

def char_ideal (α : Type u) [discrete_field α] [fintype α] : ideal ℤ :=
is_ring_hom.ker (int.cast : ℤ → α)

def prime_field (α : Type u) [discrete_field α] [fintype α] : Type :=
quotient (char_ideal α)

instance char_ideal_is_prime : is_prime (char_ideal α) :=
@is_prime.comap _ _ _ _ int.cast _ _ field.bot_is_prime

lemma char_ideal_ne_zero : ∃ p : ℕ, char_ideal α = span {(p : ℤ)} ∧ nat.prime p :=
let ⟨p, hspan, hp⟩ := int.gen_prime_ideal_ℤ (char_ideal α) in
or.elim hp
  (assume h0 : p = 0,
  have char_ideal α = ⊥, by rw [hspan, span_singleton_eq_bot]; simpa,
  have function.injective int.cast, from (@is_ring_hom.ker_eq_bot ℤ α _ _ int.cast _).mp this,
  absurd this set.not_injective_int_fintype)
  (assume h : nat.prime p, ⟨p, hspan, h⟩)

instance char_ideal_is_maximal : is_maximal (char_ideal α) :=
let ⟨p, h, hp⟩ := @char_ideal_ne_zero α _ _ in
eq.symm h ▸ int.maximal_ideal_ℤ p hp

noncomputable instance prime_field_is_field : field (prime_field α) :=
quotient.field (char_ideal α)

--need [decidable (λ a, a ∈ I)]
--comes from ker
lemma decidable_mem_ideal {α : Type*} [comm_ring α] [decidable_eq α] (I : ideal α) :
decidable_rel (λ x y, x - y ∈ I) := sorry

noncomputable instance prime_field_is_discrete_field : discrete_field (prime_field α) :=
{ has_decidable_eq := @quotient.decidable_eq ℤ (submodule.quotient_rel _) (decidable_mem_ideal _),
  inv_zero := sorry,
  ..finite_field.prime_field_is_field }

instance prime_field_fintype : fintype (prime_field α) := sorry

lemma card_prime_field_prime : nat.prime (card (prime_field α)) := sorry

instance prime_field_module : module (prime_field α) α := sorry

theorem fin_field_card (α : Type*) [discrete_field α] [fintype α] : ∃ p n : ℕ, nat.prime p ∧ card α = p^n :=
let ι : ℤ → α := int.cast in
let ⟨p, hc, hp⟩ := @char_ideal_ne_zero α _ _ in
have ∀ x : ℤ, x ∈ (char_ideal α) → ι x = 0, from
  assume x hI,
  have ι x ∈ (⊥ : ideal α), from set.mem_preimage_eq.mp hI,
  show ι x = 0, from submodule.mem_bot.mp this,
have V : vector_space (prime_field α) α, from @vector_space.mk (prime_field α) α finite_field.prime_field_is_discrete_field _ _,
let ⟨n, h⟩ := @vector_space.card_fin_vector_space (prime_field α) α _ _ _ _ V in
⟨card (prime_field α), n, card_prime_field_prime, h⟩

theorem exists_fin_field : ∀ p n : ℕ, prime p → ∃ α : Type*, ∃ [hf : field α], ∃ [hfin : fintype α], @card α hfin = p^n :=
sorry

theorem unique_fin_field [field α] [field β] : card α = card β → (α ≃r β) :=
sorry

end finite_field
