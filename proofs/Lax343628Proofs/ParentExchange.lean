import Lax343628Proofs.SetBirth

namespace Lax343628Proofs.ParentExchange

open Lax343628Proofs.SetBirth Lax343628Proofs.ConeExpansion
open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.MeanCone Lax343628Proofs.FiniteExchange
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def twoLabel (D : Finset (Fin n)) (e g : Fin n) (he : e ∉ D) (hg : g ∉ D) (heg : e ≠ g) :
    D ⊕ Fin 2 ↪ Fin n where
  toFun := Sum.elim Subtype.val (fun b ↦ if b = 0 then e else g)
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr b =>
        fin_cases b <;> norm_num at hab
        · exact False.elim (he (hab ▸ a.property))
        · exact False.elim (hg (hab ▸ a.property))
    | inr a =>
      cases b with
      | inl b =>
        fin_cases a <;> norm_num at hab
        · exact False.elim (he (hab.symm ▸ b.property))
        · exact False.elim (hg (hab.symm ▸ b.property))
      | inr b =>
        fin_cases a <;> fin_cases b <;> simp_all

lemma twoLabel_range (D : Finset (Fin n)) (e g : Fin n) (he : e ∉ D) (hg : g ∉ D)
    (heg : e ≠ g) (x : Fin n) :
    x ∈ insert e (insert g D) ↔ ∃ a, twoLabel D e g he hg heg a = x := by
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨Sum.inr 0, by simp [twoLabel]⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨Sum.inr 1, by simp [twoLabel]⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    cases a with
    | inl a => exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem a.property)
    | inr a => fin_cases a <;> simp [twoLabel]

lemma asymmetric_geometry (S U : Finset (Fin n)) {e g : Fin n}
    (heS : e ∉ S) (hgS : g ∉ S) (heU : e ∈ U) (hgU : g ∉ U) :
    (insert e S ∩ U = insert e (S ∩ U)) ∧
      (insert g S ∩ U = S ∩ U) ∧
      (differing (insert g S) U = insert e (insert g (differing (insert e S) U))) ∧
      e ∉ differing (insert e S) U ∧ g ∉ differing (insert e S) U ∧ e ≠ g := by
  have heg : e ≠ g := by intro h; exact hgU (h ▸ heU)
  refine ⟨?_, ?_, ?_, ?_, ?_, heg⟩
  · ext x; simp only [Finset.mem_inter, Finset.mem_insert]; by_cases h : x = e <;> simp_all
  · ext x; simp only [Finset.mem_inter, Finset.mem_insert]; by_cases h : x = g <;> simp_all
  · ext x
    simp only [mem_differing, Finset.mem_insert]
    by_cases hxe : x = e <;> by_cases hxg : x = g <;> simp_all
  · simp [mem_differing, heU]
  · simp [mem_differing, hgS, hgU, heg.symm]

lemma swap_insert (S : Finset (Fin n)) {e g : Fin n} (he : e ∉ S) (hg : g ∉ S) :
    (insert e S).map (Equiv.swap e g).toEmbedding = insert g S := by
  rw [Finset.map_insert]
  simp only [Equiv.toEmbedding_apply, Equiv.swap_apply_left]
  congr 1
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    have hfix : Equiv.swap e g a = a := Equiv.swap_apply_of_ne_of_ne
      (fun h ↦ he (h ▸ ha)) (fun h ↦ hg (h ▸ ha))
    simpa only [Equiv.toEmbedding_apply, hfix] using ha
  · simp

lemma swap_partner (U : Finset (Fin n)) {e g : Fin n} (hu : e ∈ U ↔ g ∈ U) :
    U.map (Equiv.swap e g).toEmbedding = U := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    by_cases hae : a = e
    · subst a; simpa using hu.mp ha
    by_cases hag : a = g
    · subst a; simpa using hu.mpr ha
    · simpa only [Equiv.toEmbedding_apply, Equiv.swap_apply_of_ne_of_ne hae hag] using ha
  · simp

end
end Lax343628Proofs.ParentExchange
