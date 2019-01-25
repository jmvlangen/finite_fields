import set_theory.cardinal
import linear_algebra.dimension

universes u v

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

def extend_by_zero (f : subtype p → β) : α → β := λ a, if hc : p a then f ⟨a, hc⟩ else 0

/-- `subtype_domain_extend f` is the extension of the finitely supported function
  `f` on the subtype `p` to the finitely supported function by extending by zero. -/
def subtype_domain_extend (f : subtype p →₀ β) : α →₀ β :=
{ support            := finset.map ⟨subtype.val, subtype.val_injective⟩ f.support,
  to_fun             := extend_by_zero p f,
  mem_support_to_fun := λ a,
    iff.intro
      (assume hmem,
      let ⟨ap, hsup, hs⟩ := finset.mem_map.mp hmem in
      have hp : p a, from hs ▸ ap.property,
      have ap = ⟨a, hp⟩, by rwa[subtype.ext],
      by unfold extend_by_zero; rw [dif_pos hp, ←this]; exact (mem_support_to_fun f ap).mp hsup)
      (assume hne0 : dite _ _ _ ≠ 0,
      have hp : p a, from decidable.by_contradiction (assume hnp, absurd (dif_neg hnp) hne0),
      have h : f ⟨a, hp⟩ ≠ 0, by rwa [dif_pos] at hne0,
      finset.mem_map_of_mem _ ((mem_support_to_fun f ⟨a, hp⟩).mpr h)) }

def subtype_domain_extend' [add_comm_monoid β] (f : subtype p →₀ β) : α →₀ β :=
sorry --map_domain (@subtype.val α p) f

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
      have hg : (subtype_domain_extend p (subtype_domain p f)) a = 0, from dif_neg hna,
      by rw[hf, hg]
    | is_true ha := have a = (subtype.mk a ha).val, from rfl,
      by rw[this, subtype_domain_extend_apply p, subtype_domain_apply]
  end)

lemma subtype_domain_restrict_extend (f : {a // p a} →₀ β) :
subtype_domain p (subtype_domain_extend p f) = f :=
by apply finsupp.ext; intro a; rw[subtype_domain_apply, subtype_domain_extend_apply p]

example (s : set α) : {f : α →₀ β // ↑f.support ⊆ s} ≃ s →₀ β := sorry

example : {f : α →₀ β // ∀ a : α, f a ≠ 0 → p a} ≃ subtype p →₀ β := sorry

set_option eqn_compiler.zeta true

def finnsup_equiv_subtype_domain : {f : α →₀ β // ∀ a ∈ f.support, p a} ≃ ({a // p a} →₀ β) :=
{ to_fun    := (finsupp.subtype_domain p) ∘ subtype.val,
  inv_fun   := λ f,
    let g := (subtype_domain_extend p f) in
    subtype.mk g
      (assume a (h : a ∈ g.support),
      decidable.by_contradiction 
        (assume hnp : ¬p a,
        have g a = 0, from dif_neg hnp,
        have hn : a ∉ g.support, from not_mem_support_iff.mpr this,
        absurd h hn)),
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
