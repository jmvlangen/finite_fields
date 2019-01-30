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

lemma map_domain_apply {α₁ α₂ : Type*} [decidable_eq α₁] [decidable_eq α₂]
(v : α₁ → α₂) (f : α₁ →₀ β) (h : function.injective v) {a : α₁} :
(map_domain v f) (v a) = f a := show (f.sum $ λ x, single (v x)) (v a) = f a,
begin
  rw[←sum_single f],
  simp,
  apply sum_congr, refl,
  intros,
  simp[single_apply, function.injective.eq_iff h],
  congr
end

include d

lemma extend_restrict (f : {f : α →₀ β // ∀ a ∈ f.support, p a}) :
map_domain subtype.val (subtype_domain p f.val) = f :=
finsupp.ext $ λ a, sorry

lemma restrict_extend (f : subtype p →₀ β) :
subtype_domain p (map_domain subtype.val f) = f :=
finsupp.ext $ λ a, map_domain_apply _ _ (subtype.val_injective)

end finsupp

namespace finsupp
/-- Proving some equivalences --/

variables {α : Type u} {β : Type v}
variables [decidable_eq α] [has_zero α]

open finset

def equiv_fun [h : fintype β] : (β →₀ α) ≃ (β → α) :=
{ to_fun := finsupp.to_fun,
  inv_fun := λ f, finsupp.mk (finset.filter (λ a, f a ≠ 0) h.elems) f
    (assume a, by rw[mem_filter]; exact and_iff_right (fintype.complete a)),
  left_inv := λ f, finsupp.ext (λ _, rfl),
  right_inv := λ f, rfl }

end finsupp

namespace finsupp

variables {α : Type u} {β : Type v}
variables [ring α] [decidable_eq α]
variables [add_comm_group β] [module α β] [decidable_eq β]

open finset

def equiv_lc {s : set β} [decidable_pred s] :
(s →₀ α) ≃ lc.supported s :=
{
  to_fun := λ f, ⟨map_domain subtype.val f,
    assume a h,
    have h0 : a ∈ image _ _, from mem_of_subset map_domain_support h,
    let ⟨ap, _, hs⟩ := mem_image.mp h0 in hs ▸ ap.property⟩,
  inv_fun := (finsupp.subtype_domain s) ∘ subtype.val,
  left_inv := restrict_extend _,
  right_inv := λ f, subtype.eq $ extend_restrict _ f,
}

end finsupp

namespace fintype

variables {α : Type*} {β : Type*} {γ : Type*}
variables [fintype α] [fintype β] [fintype γ]

lemma card_eq_of_equiv_fun [decidable_eq β] (f : α ≃ (β → γ)) :
card α = card γ ^ card β :=
calc card α = card (β → γ)    : card_congr f
        ... = card γ ^ card β : card_fun

end fintype

namespace module

open set

variables {α : Type u} {β : Type v}
variables [ring α] [decidable_eq α]
variables [add_comm_group β] [module α β] [decidable_eq β]
variables {b : set β}

include α β

noncomputable def equiv_finsupp_basis [decidable_pred b] (h : is_basis b) : β ≃ (b →₀ α) :=
calc
    β ≃ lc.supported b : (module_equiv_lc h).to_equiv
  ... ≃ (b →₀ α)       : equiv.symm finsupp.equiv_lc

noncomputable def equiv_fun_basis [decidable_pred b] [fintype b] (h : is_basis b) : β ≃ (b → α) := 
calc
    β ≃ (b →₀ α) : equiv_finsupp_basis h
  ... ≃ (b → α)  : finsupp.equiv_fun

open cardinal fintype

noncomputable def basis_is_finite [fintype β] (h : is_basis b) : fintype b :=
set.finite.fintype (set.finite.of_fintype b)

lemma card_of_basis [fintype α] [fintype β] [hf : fintype b] (h : is_basis b) : 
card β = (card α)^(card b) :=
have db : decidable_pred b, from set.decidable_mem_of_fintype b,
card_eq_of_equiv_fun (@equiv_fun_basis _ _ _ _ _ _ _ _ db _ h)

end module

namespace vector_space
 
open fintype vector_space cardinal finsupp module
 
variables (α : Type u) (β : Type v)
variables [discrete_field α] [fintype α]
variables [add_comm_group β] [fintype β]
variables [vector_space α β]

lemma card_fin [deβ : decidable_eq β] : ∃ n : ℕ, card β = (card α) ^ n :=
let ⟨b, hb⟩ := exists_is_basis β in
have hf : fintype b, from basis_is_finite hb,
⟨@card b hf, @card_of_basis _ _ _ _ _ _ _ _ _ _ hf hb⟩

end vector_space 
