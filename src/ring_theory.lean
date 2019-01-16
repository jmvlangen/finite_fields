import ring_theory.ideals
import ring_theory.ideal_operations
import logic.basic
import data.equiv.algebra

universes u v

namespace ideal

variable {α : Type u}
variable [comm_ring α]

lemma eq_bot (I : ideal α) : I = ⊥ ↔ ∀ x : α, x ∈ I → x = 0 :=
begin
  apply (iff.trans lattice.eq_bot_iff),
  apply (iff.trans submodule.le_def),
  apply forall_congr,
  intro x,
  apply imp_congr_right,
  intro h,
  apply submodule.mem_bot
end

end ideal

namespace is_ring_hom

open function ideal ideal.quotient

variables {α : Type u} {β : Type v}
variables [comm_ring α] [comm_ring β]

def ker (f : α → β) [is_ring_hom f] : ideal α := comap f ⊥
n
variables {f : α → β} [is_ring_hom f]

lemma mem_ker {x : α} : x ∈ ker f ↔ f x = 0 :=
submodule.mem_bot

theorem ker_eq_bot : ker f = ⊥ ↔ injective f :=
begin
  rw (is_add_group_hom.injective_iff f),
  rw eq_bot,
  apply forall_congr,
  intro,
  rw mem_ker,
end

lemma le_ker {I : ideal α} : I ≤ ker f ↔ ∀ x : α, x ∈ I → f x = 0 :=
begin
  apply forall_congr,
  intro x,
  apply imp_congr_right,
  intro h,
  exact mem_ker
end

variable {I : ideal α}

lemma map_mk_eq_bot : map_mk I I = ⊥ :=
suffices ∀ x : quotient I, x ∈ map_mk I I → x = 0, from (eq_bot (map_mk I I)).mpr this,
assume x : quotient I,
assume hx : x ∈ map_mk I I,
have ∃ y : α, y ∈ I ∧ ideal.quotient.mk I y = x,
  from (set.mem_image (ideal.quotient.mk I) I x).mp hx,
let ⟨y, hy, heq⟩ := this in
have y - 0 ∈ I, from eq.symm (sub_zero y) ▸ hy,
have x = ideal.quotient.mk I 0, from heq ▸ ideal.quotient.eq.mpr this,
show x = 0, from eq.symm this ▸ mk_zero I

/-- The homomorphism theorem for rings --/
def factor (f : α → β) [is_ring_hom f] (I : ideal α) (h : I ≤ ker f) : quotient I → β := 
lift I f (le_ker.mp h)

lemma factor_to_ring_hom' {h : I ≤ ker f} : is_ring_hom (factor f I h) :=
ideal.quotient.is_ring_hom

instance factor_to_ring_hom {h : I ≤ ker f} : is_ring_hom (factor f I h) :=
ideal.quotient.is_ring_hom

theorem factor_commutes (h : I ≤ ker f) {x : α} :
                        (factor f I h) (ideal.quotient.mk I x) = f x := 
lift_mk

lemma ker_factor (h : I ≤ ker f) : ker (factor f I h) = map_mk I (ker f) :=
suffices ∀ x : quotient I, x ∈ ker (factor f I h) ↔ x ∈ map_mk I (ker f),
  from ext this,
assume x : quotient I,
suffices ∀ y : α, ideal.quotient.mk I y ∈ ker (factor f I h) ↔ ideal.quotient.mk I y ∈ map_mk I (ker f),
  from quotient.induction_on' x this,
assume y : α,
suffices y ∈ ker f ↔ ideal.quotient.mk I y ∈ map_mk I (ker f),
  by rw [mem_ker, factor_commutes h]; rw mem_ker at this; assumption,
iff.intro
  (assume h0 : y ∈ ker f,
   show ideal.quotient.mk I y ∈ map_mk I (ker f),
     from set.mem_image_of_mem (ideal.quotient.mk I) h0)
  (assume h0 : ideal.quotient.mk I y ∈ map_mk I (ker f),
   have ∃ y' : α, y' ∈ ker f ∧ ideal.quotient.mk I y' = ideal.quotient.mk I y,
     from (set.mem_image (ideal.quotient.mk I) (ker f) (ideal.quotient.mk I y)).mp h0,
   let ⟨y', hy', heq⟩ := this in
   have y - y' ∈ I, from ideal.quotient.eq.mp (eq.symm heq),
   have y - y' ∈ ker f, from h this,
   show y ∈ ker f, from sub_add_cancel y y' ▸ (ker f).add this hy')

/-- The first isomorphism theorem for rings --/
theorem factor_injective (h : I = ker f) : injective (factor f I (h ▸ le_refl I)) :=
begin
  apply ker_eq_bot.mp,
  rw ker_factor,
  rw ←h,
  exact map_mk_eq_bot
end

theorem factor_surjective (h : I ≤ ker f) (hf : surjective f) : surjective (factor f I h) :=
assume y : β,
have ∃ x : α, f x = y, from hf y,
let ⟨x, hfx⟩ := this in
have (factor f I h) (ideal.quotient.mk I x) = y, from hfx ▸ factor_commutes h,
show ∃ x' : quotient I, (factor f I h) x' = y, from ⟨ideal.quotient.mk I x, this⟩

theorem factor_bijective (h : I = ker f) (hf : surjective f) :
                         bijective (factor f I (h ▸ le_refl I)) :=
⟨factor_injective h, factor_surjective (h ▸ le_refl I) hf⟩

noncomputable theorem factor_iso (h : I = ker f) (hf : surjective f) : quotient I ≃r β :=
ring_equiv.mk (equiv.of_bijective (factor_bijective h hf)) factor_to_ring_hom'

end is_ring_hom
