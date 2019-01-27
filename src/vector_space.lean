import set_theory.cardinal
import linear_algebra.dimension

universes u v

namespace finsupp

open finset

variables {α : Type u} {β : Type v}
variables [decidable_eq α]
variables [decidable_eq β] [add_comm_monoid β]
variables (p : α → Prop) [d : decidable_pred p]

variable (s : finset α)

def finsupp_equiv_fintype_domain [h : fintype α] : (α →₀ β) ≃ (α → β) :=
{ to_fun := finsupp.to_fun,
  inv_fun := λ f, finsupp.mk (finset.filter (λ a, f a ≠ 0) h.elems) f
    (assume a, by rw[mem_filter]; exact and_iff_right (fintype.complete a)),
  left_inv := λ f, finsupp.ext (λ _, rfl),
  right_inv := λ f, rfl }

lemma map_domain_apply {α₁ α₂ : Type*} [decidable_eq α₁] [decidable_eq α₂]
(v : α₁ → α₂) (f : α₁ →₀ β) (h : function.injective v) {a : α₁} :
(map_domain v f) (v a) = f a :=
sorry

include d

lemma extend_restrict (f : {f : α →₀ β // ∀ a ∈ f.support, p a}) :
map_domain subtype.val (subtype_domain p f.val) = f :=
finsupp.ext $ λ a, sorry

lemma restrict_extend (f : subtype p →₀ β) :
subtype_domain p (map_domain subtype.val f) = f :=
finsupp.ext $ λ a, map_domain_apply _ _ (subtype.val_injective)

def finnsup_equiv_subtype_domain : {f : α →₀ β // ∀ a ∈ f.support, p a} ≃ (subtype p →₀ β) :=
{ to_fun := (finsupp.subtype_domain p) ∘ subtype.val,
  inv_fun := λ f, ⟨map_domain subtype.val f,
    assume a h,
    have h0 : a ∈ image _ _, from mem_of_subset map_domain_support h,
    let ⟨ap, _, hs⟩ := mem_image.mp h0 in hs ▸ ap.property⟩,
  left_inv := λ f, subtype.eq $ extend_restrict _ f,
  right_inv := restrict_extend _ }

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

lemma card_fun_of_equiv {α : Type*} {β : Type*} {γ : Type*} [fintype α] [fintype β] [fintype γ]
[decidable_eq β] (f : α ≃ (β → γ)) : card α = card γ ^ card β :=
calc card α = card (β → γ)                 : card_congr f
        ... = card γ ^ card β              : card_fun

example [vector_space α β] {b : set β} [is_basis b] : β ≃ (b →₀ α) := sorry

example [vector_space α β] {b : set β} [is_basis b] [set.finite b] : β ≃ (b → α) := sorry

lemma card_fin [deβ : decidable_eq β] : ∃ n : ℕ, card β = (card α) ^ n :=
let ⟨n, hn⟩ := dim_fin α β in
⟨n,
let ⟨b, hb⟩ := exists_is_basis β in
have fb : fintype ↥b, from (set.finite.of_fintype b).fintype,
have db : decidable_pred (λ a, a ∈ b), from (λ a, @set.decidable_mem_of_fintype _ deβ b fb a),
have deb : decidable_eq ↥b, from subtype.decidable_eq,
have fb2 : fintype ↥b, from @subtype.fintype _ _ _ db,
have f : β ≃ (b → α), from
  calc β ≃ {l : lc α β  | ↑l.support ⊆ b} : (module_equiv_lc hb).to_equiv
     ... ≃ (b →₀ α)                       : @finnsup_equiv_subtype_domain _ _ deβ _ _ _ db 
     ... ≃ (b → α)                        : @finsupp_equiv_fintype_domain _ _ deb _ _ fb2,
have h : @card ↥b fb = n,
by rw[←card_fin n, card_eq, ←lift_mk_eq, lift_mk_fin,
  is_basis.mk_eq_dim hb, lift_id _]; assumption,
h ▸ @card_fun_of_equiv _ _ _ _ fb _ deb f⟩

end vector_space 
