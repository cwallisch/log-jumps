import Lax343628Proofs.ConeExpansion

namespace Lax343628Proofs.BalancedCone

open Lax343628Proofs.FiniteExchange Lax343628Proofs.MeanCone
open Lax343628Proofs.BirthGeometry Lax343628Proofs.BirthCouplings
open Lax343628Proofs.ConeExpansion Lax343628Proofs.ShadowMeans
open Lax343628Proofs.FiniteDrift Lax343628Proofs.NamedBirth
open scoped Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma swap_near {α : Type*} [DecidableEq α] (S : Finset α) (e g : α) :
    Near S (S.map (Equiv.swap e g).toEmbedding) := by
  refine ⟨by simp, ?_⟩
  have hsub : S \ S.map (Equiv.swap e g).toEmbedding ⊆ {if e ∈ S then e else g} := by
    intro x hx
    obtain ⟨hxS, hxnot⟩ := Finset.mem_sdiff.mp hx
    have hneq : Equiv.swap e g x ≠ x := by
      intro hfix
      exact hxnot (Finset.mem_map.mpr ⟨x, hxS, hfix⟩)
    rcases Equiv.eq_or_eq_of_swap_apply_ne_self hneq with rfl | rfl
    · simp [hxS]
    · by_cases he : e ∈ S
      · exact False.elim (hxnot (Finset.mem_map.mpr ⟨e, he, Equiv.swap_apply_left e x⟩))
      · simp [he]
  exact (Finset.card_le_card hsub).trans (by simp)

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

omit [Fintype α] [DecidableEq α] in
lemma realize_rename (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (p : Equiv.Perm (Fin n)) (hR : ∀ x ∈ R, p x = x)
    (hL : ∀ a, label a ∉ R) (hL' : ∀ a, p (label a) ∉ R)
    (S : Finset (α ⊕ Fin R.card)) :
    realize (C.map p.toEmbedding) (label.trans p.toEmbedding) R hL' S =
      (realize C label R hL S).map p.toEmbedding := by
  unfold realize
  rw [Finset.map_union, Finset.map_map]
  congr 1
  congr 1
  apply Function.Embedding.ext
  intro a
  cases a with
  | inl a => rfl
  | inr a => exact (hR _ (R.equivFin.symm a).property).symm

omit [Fintype α] [DecidableEq α] in
lemma admissible_rename (C : Finset (Fin n)) (label : α ↪ Fin n) (R : Finset (Fin n))
    (hA : Admissible C label R) (p : Equiv.Perm (Fin n)) (hR : ∀ x ∈ R, p x = x) :
    Admissible (C.map p.toEmbedding) (label.trans p.toEmbedding) R := by
  constructor
  · intro a ha
    have he : p (label a) = label a := p.injective (hR _ ha)
    exact hA.named_fresh a (he ▸ ha)
  · intro a ha
    obtain ⟨x, hx, he⟩ := Finset.mem_map.mp ha
    exact hA.named_common a (by have := p.injective he; simpa using this ▸ hx)
  · apply Finset.disjoint_left.mpr
    intro x hxC hxR
    obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hxC
    have hp : p x = x := hR x hxR
    have hyx : y = x := p.injective (he.trans hp.symm)
    exact Finset.disjoint_left.mp hA.common_fresh hy (hyx.symm ▸ hxR)

lemma comparison {r K : ℕ} (hr : r ≤ K) (C : Finset (Fin n)) (label : α ↪ Fin n)
    (R : Finset (Fin n)) (hA : Admissible C label R) (hC : C.card ≤ r) (hK : K ≤ R.card)
    {i e g : Fin n} (hi : Extra C label R i) (hie : i ≠ e) (hig : i ≠ g)
    (heR : e ∉ R) (hgR : g ∉ R) (rho : ℝ) (h : Finset (Fin n) → ℝ)
    (hz : ∀ Z, Z.card ≠ r → h Z = 0) (hc : Cone i r rho h) :
    setValue K (C.map (Equiv.swap e g).toEmbedding)
        (label.trans (Equiv.swap e g).toEmbedding) R h ≤ rho * setValue K C label R h ∧
      setValue K C label R h ≤ rho * setValue K (C.map (Equiv.swap e g).toEmbedding)
        (label.trans (Equiv.swap e g).toEmbedding) R h := by
  let p := Equiv.swap e g
  have hR : ∀ x ∈ R, p x = x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (fun he ↦ heR (he ▸ hx)) (fun hg ↦ hgR (hg ▸ hx))
  have hpi : p i = i := Equiv.swap_apply_of_ne_of_ne hie hig
  have hA' := admissible_rename C label R hA p hR
  rw [normalized hr _ _ _ hA' (by simpa using hC) hK h hz,
    normalized hr C label R hA hC hK h hz]
  rw [same_card_mass r _ C (by simp) (label.trans p.toEmbedding)]
  have hmass : mass r C (label.trans p.toEmbedding) = mass r C label := rfl
  rw [hmass]
  have ht : expect (C.map p.toEmbedding) (label.trans p.toEmbedding) R hA'.named_fresh
        (r - C.card) h ≤ rho * expect C label R hA.named_fresh (r - C.card) h ∧
      expect C label R hA.named_fresh (r - C.card) h ≤ rho *
        expect (C.map p.toEmbedding) (label.trans p.toEmbedding) R hA'.named_fresh
          (r - C.card) h := by
    have hp (S : Finset (α ⊕ Fin R.card))
        (hS : S ∈ (PlacedBase.placedLaw (r - C.card)).support) :
        h (realize (C.map p.toEmbedding) (label.trans p.toEmbedding) R hA'.named_fresh S) ≤
            rho * h (realize C label R hA.named_fresh S) ∧
          h (realize C label R hA.named_fresh S) ≤ rho *
            h (realize (C.map p.toEmbedding) (label.trans p.toEmbedding) R hA'.named_fresh S) := by
      rw [realize_rename C label R p hR hA.named_fresh hA'.named_fresh]
      have hsize : (realize C label R hA.named_fresh S).card = r := by
        rw [realize_card C label R hA, SlotBirth.placedLaw_card
          (by simpa using (Nat.sub_le r C.card).trans (hr.trans hK)) S hS]
        omega
      have hiS := extra_not_realize C label R hA.named_fresh hi S
      have hiMap : i ∉ (realize C label R hA.named_fresh S).map p.toEmbedding := by
        intro hiM
        obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp hiM
        exact hiS ((p.injective (hea.trans hpi.symm)) ▸ ha)
      exact cone_pair hc _ _ hsize hiS hiMap (swap_near _ e g)
    constructor
    · have ht := mean_mono_on_support (PlacedBase.placedLaw (α := α) (β := Fin R.card) (r - C.card))
        (fun S hS ↦ (hp S hS).1)
      rw [mean_mul] at ht
      exact ht
    · have ht := mean_mono_on_support (PlacedBase.placedLaw (α := α) (β := Fin R.card) (r - C.card))
        (fun S hS ↦ (hp S hS).2)
      rw [mean_mul] at ht
      exact ht
  have hm := (mass_pos r C label).le
  simp only [Finset.card_map]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ht.1 hm]
  · nlinarith [mul_le_mul_of_nonneg_left ht.2 hm]

end
end Lax343628Proofs.BalancedCone
