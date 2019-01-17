import ring_theory

universe u

namespace field

open ideal

variable {α : Type u}
variable [field α]

lemma ne_bot_is_top : ∀ I : ideal α, I ≠ ⊥ → I = ⊤ :=
assume I : ideal α,
assume h : I ≠ ⊥,
have ∃ x ∈ I, (x : α) ≠ (0 : α), from mem_of_not_bot I h,
let ⟨x, hI, h0⟩ := this in
have is_unit x, from is_unit_of_mul_one x (x⁻¹) (field.mul_inv_cancel h0),
show I = ⊤, from eq_top_of_is_unit_mem I hI this

lemma bot_is_max : is_maximal (⊥ : ideal α) :=
have h : ∀ I : ideal α, ⊥ < I → I = ⊤, from 
  assume I : ideal α,
  assume hI : ⊥ < I,
  have I ≠ ⊥, from lattice.bot_lt_iff_ne_bot.mp hI,
  show I = ⊤, from ne_bot_is_top I this,
show is_maximal (⊥ : ideal α), from ⟨bot_ne_top, h⟩

lemma bot_is_prime : is_prime (⊥ : ideal α) :=
is_maximal.is_prime bot_is_max

end field
