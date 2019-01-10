import ring_theory.algebra
import field_theory.finite
import ring_theory.ideals

universes u v w

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
