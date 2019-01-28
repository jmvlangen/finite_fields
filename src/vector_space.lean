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
(map_domain v f) (v a) = f a :=
sorry

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
variables [ring α] [decidable_eq α]
variables [decidable_eq β]

instance to_module_of_ring : module α (β →₀ α) :=
finsupp.to_module β α

instance fun_to_module_of_ring : module α (β → α) :=
pi.module α

open finset

def equiv_fun [h : fintype β] : (β →₀ α) ≃ₗ (β → α) :=
{ to_fun := finsupp.to_fun,
  add := λ f g, funext (λ a, 
    calc to_fun (f + g) a = (to_fun f a) + (to_fun g a) : finsupp.add_apply
                      ... = (to_fun f + to_fun g) a     : pi.add_apply ⇑f ⇑g a),
  smul := λ r f, funext (λ a,
    calc to_fun (r • f) a = r • (to_fun f a) : finsupp.smul_apply
                      ... = (r • to_fun f) a : pi.smul_apply ⇑f a r),
  inv_fun := λ f, finsupp.mk (finset.filter (λ a, f a ≠ 0) h.elems) f
    (assume a, by rw[mem_filter]; exact and_iff_right (fintype.complete a)),
  left_inv := λ f, finsupp.ext (λ _, rfl),
  right_inv := λ f, rfl }

variable [add_comm_group β]
variable [module α β]

set_option pp.implicit true

noncomputable def equiv_lc {s : set β} [decidable_pred s] : (s →₀ α) ≃ₗ lc.supported s :=
{
  to_fun := λ f, ⟨map_domain subtype.val f,
    assume a h,
    have h0 : a ∈ image _ _, from mem_of_subset map_domain_support h,
    let ⟨ap, _, hs⟩ := mem_image.mp h0 in hs ▸ ap.property⟩,
  add := λ f g, begin
      rw subtype.coe_ext,
      rw subtype.coe_mk,
      rw finsupp.map_domain_add,
      rw submodule.coe_add,
      rw subtype.coe_mk,
      rw subtype.coe_mk,
      sorry, --refl
    end,
  smul := sorry,
  inv_fun := (finsupp.subtype_domain s) ∘ subtype.val,
  left_inv := restrict_extend _,
  right_inv := λ f, subtype.eq $ extend_restrict _ f,
}

variable (p : β → Prop)
variable [decidable_pred p]

def finnsup_equiv_subtype_domain : {f : β →₀ α // ∀ a ∈ f.support, p a} ≃ (subtype p →₀ α) :=
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

noncomputable def equiv_finsupp_basis [vector_space α β] (b : set β) {hb : is_basis b} [decidable_eq b] [db : decidable_pred b] [deβ : decidable_eq β]:
β ≃ (b →₀ α) := 
calc
    β ≃ {l : lc α β | ↑l.support ⊆ b} : (module_equiv_lc hb).to_equiv
  ... ≃ (b →₀ α)                      : @finnsup_equiv_subtype_domain _ _ deβ _ _ _ db 

def [vector_space α β] {b : set β} [hb : is_basis b] [set.finite b] [deb : decidable_eq b] [decidable_eq β] [decidable_pred b] : β ≃ (b → α) := 
calc
    β ≃ (b →₀ α) : equiv_finsupp_basis α β b
  ... ≃ (b → α)  : @equiv_fun _ _ deb _ _ (subtype.finite b)

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
     ... ≃ (b → α)                        : @equiv_fun _ _ deb _ _ fb2,
have h : @card ↥b fb = n,
by rw[←card_fin n, card_eq, ←lift_mk_eq, lift_mk_fin,
  is_basis.mk_eq_dim hb, lift_id _]; assumption,
h ▸ @card_fun_of_equiv _ _ _ _ fb _ deb f⟩

end vector_space 
