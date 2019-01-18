import set_theory.cardinal
import linear_algebra.dimension

import integer
import field

universes u v w

namespace finsupp

variables {α : Type u} {β : Type v}
variables [decidable_eq α]
variables [decidable_eq β] [has_zero β]
variables (p : α → Prop) [d : decidable_pred p]

variable (s : finset α)

def finsupp_equiv_fintype_domain [h : fintype α] : (α →₀ β) ≃ (α → β) :=
{ to_fun := finsupp.to_fun,
  inv_fun := λ f, finsupp.mk (finset.filter (λ a, f a ≠ 0) h.elems) f
    (assume a, by rw[finset.mem_filter]; apply and_iff_right; exact fintype.complete a),
  left_inv := λ f, finsupp.ext (λ a, rfl),
  right_inv := λ f, funext (λ a, rfl) }

include d

def subtype_domain_extend (f : subtype p →₀ β) : α →₀ β :=
{ support            := finset.map ⟨subtype.val, subtype.val_injective⟩ f.support,
  to_fun             := λ a, if hc : p a then f ⟨a, hc⟩ else 0,
  mem_support_to_fun := λ a,
    iff.intro
      (assume hmap,
      let ⟨ap, hsup, hs⟩ := finset.mem_map.mp hmap in
      have hp : p a, by rw[←hs]; exact ap.property,
      have ap = ⟨a, hp⟩, by rw[subtype.ext]; exact hs,
      by rw [dif_pos hp, ←this]; exact (mem_support_to_fun f ap).mp hsup)
      (assume hne0,
      have hp : p a, from match d a with
        | is_false hnp := absurd (dif_neg hnp) hne0
        | is_true  hp  := hp
      end,
      have h1 : (if hc : p a then f ⟨a, hc⟩ else 0) = f ⟨a, hp⟩, from dif_pos hp,
      have h2 : f ⟨a, hp⟩ ≠ 0, by rw[←h1]; exact hne0,
      finset.mem_map_of_mem _ ((mem_support_to_fun f ⟨a, hp⟩).mpr h2)) }

lemma subtype_domain_extend_apply {f : subtype p →₀ β} {a : subtype p} :
(subtype_domain_extend p f) (a.val) = f a := 
by rw[←subtype.coe_eta a _]; exact dif_pos a.property

lemma subtype_domain_extend_restrict (f : α →₀ β) (h : ∀ a ∈ f.support, p a) :
subtype_domain_extend p (subtype_domain p f) = f :=
finsupp.ext
  (assume a,
  match d a with
    | is_false hna :=
      have a ∉ f.support, from assume hs, absurd (h a hs) hna,
      have hf : f a = 0, from not_mem_support_iff.mp this,
      let g := (subtype_domain_extend p (subtype_domain p f)) in
      have hg : g a = 0, from dif_neg hna,
      by rw[hf, hg]
    | is_true ha := have a = (subtype.mk a ha).val, from rfl,
      by rw[this, subtype_domain_extend_apply p, subtype_domain_apply]
  end)

lemma subtype_domain_restrict_extend (f : {a // p a} →₀ β) :
subtype_domain p (subtype_domain_extend p f) = f :=
by apply finsupp.ext; intro a; rw[subtype_domain_apply, subtype_domain_extend_apply p]

def finnsup_equiv_subtype_domain : {f : α →₀ β // ∀ a ∈ f.support, p a} ≃ ({a // p a} →₀ β) :=
{ to_fun    := (finsupp.subtype_domain p) ∘ subtype.val,
  inv_fun   := (λ f, subtype.mk (subtype_domain_extend p f)
    (assume a h,
    match d a with
      | is_false hnb :=
        let g := (subtype_domain_extend p f) in
        have g a = 0, from dif_neg hnb,
        have hn : a ∉ g.support, from not_mem_support_iff.mpr this,
        absurd h hn
      | is_true hb := hb
    end)),
  left_inv := λ f, by rw[subtype.ext]; exact subtype_domain_extend_restrict _ f.val f.property,
  right_inv := λ f, subtype_domain_restrict_extend _ f }

end finsupp

namespace vector_space
 
open fintype vector_space cardinal finsupp
 
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

--set_option class.instance_max_depth 32
--set_option trace.class_instances true
--set_option pp.notation false
--set_option pp.implicit true

lemma card_fun_of_equiv {α : Type*} {β : Type*} {γ : Type*} [fintype α] [fintype β] [fintype γ]
[decidable_eq β] (f : α ≃ (β → γ)) : card α = card γ ^ card β :=
calc card α = @card (β → γ) (of_equiv α f) : eq.symm $ of_equiv_card f
        ... = card (β → γ)                 : by congr
        ... = card γ ^ card β              : card_fun

lemma card_fin_vector_space : ∃ n : ℕ, card β = (card α) ^ n :=
let ⟨n, hn⟩ := dim_fin α β in
⟨n,
let ⟨b, hb⟩ := exists_is_basis β in
have heq : (λ l : β →₀ α, ↑l.support ⊆ b) = (λ l, ∀ a ∈ l.support, a ∈ b),
  from funext (assume l, set.subset_def),
have deβ : decidable_eq β, from sorry,
have fb : fintype ↥b, from (set.finite.of_fintype b).fintype,
have db : decidable_pred (λ a, a ∈ b), from (λ a, @set.decidable_mem_of_fintype _ deβ b fb a),
have deb : decidable_eq ↥b, from @subtype.decidable_eq _ _ deβ,
have fb2 : fintype ↥b, from @subtype.fintype _ _ _ db,
have f : β ≃ (b → α), from
  calc β ≃ lc.supported b                         : (module_equiv_lc hb).to_equiv
     ... ≃ {l : lc α β  | ↑l.support ⊆ b}         : equiv.cast $ rfl
     ... ≃ {l : β →₀ α // ↑l.support ⊆ b}         : by apply equiv.cast; rw[set.set_coe_eq_subtype]; refl
     ... ≃ {l : β →₀ α // ∀ a ∈ l.support, a ∈ b} : by apply equiv.cast; rw[heq]
     ... ≃ ({x // x ∈ b} →₀ α)                    : @finnsup_equiv_subtype_domain _ _ deβ _ _ _ db 
     ... ≃ ({x // x ∈ b} → α)                     : @finsupp_equiv_fintype_domain _ _ deb _ _ fb2
     ... ≃ (b → α)                                : by apply equiv.cast; refl,

have h0 : cardinal.mk ↥b = ↑n, from hn ▸ hb.mk_eq_dim,
--have nonempty (↥b ≃ fin n), begin rw[←@quotient.eq _ _ ↥b (fin n)],  end,
have h1 : ↥b ≃ fin n, from sorry,
have h : @card ↥b fb = n, by rw[←fintype.card_fin n]; apply card_congr; exact h1,
--have h : @card b fb = cardinal.mk n, from hn, --from hn ▸ hb.mk_eq_dim,
/-calc card β = @card (b → α) (of_equiv β f) : eq.symm $ of_equiv_card f
        ... = card (b → α)                 : by congr
        ... = card α ^ @card b fb          : card_fun
        ... = (card α) ^ n                 : sorry--by rw[h]-/
h ▸ @card_fun_of_equiv _ _ _ _ fb _ deb f
⟩

variable (b : set β)
#check has_coe_to_sort b

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
let ⟨p, hspan, hp⟩ := int.prime_ideal_eq_nℤ (char_ideal α) in
or.elim hp
  (assume h0 : p = 0,
  have char_ideal α = ⊥, by rw [hspan, span_singleton_eq_bot]; simpa,
  have function.injective int.cast, from (@is_ring_hom.ker_eq_bot ℤ α _ _ int.cast _).mp this,
  absurd this set.not_injective_int_fintype)
  (assume h : nat.prime p, ⟨p, hspan, h⟩)

instance char_ideal_is_maximal : is_maximal (char_ideal α) :=
let ⟨p, h, hp⟩ := @char_ideal_ne_zero α _ _ in
eq.symm h ▸ int.nℤ_maximal p hp

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
