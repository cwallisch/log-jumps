import Lax343628Proofs.Trajectories

namespace Lax343628Proofs.LastExit

open scoped Classical

noncomputable section

lemma last_outside {α : Type*} {H : ℕ} (h : Fin (H + 1) → α) (A : Set α)
    (t : Fin (H + 1)) (ht : h t ∈ A) (hprev : ∃ i ≤ t, h i ∉ A) :
    ∃ s, s < t ∧ h s ∉ A ∧ ∀ i, s < i → i ≤ t → h i ∈ A := by
  let S : Finset (Fin (H + 1)) := Finset.univ.filter (fun i ↦ i ≤ t ∧ h i ∉ A)
  have hS : S.Nonempty := by
    obtain ⟨i, hit, hi⟩ := hprev
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hit, hi⟩⟩
  let s := S.max' hS
  have hs : s ∈ S := Finset.max'_mem S hS
  have hs' : s ≤ t ∧ h s ∉ A := (Finset.mem_filter.mp hs).2
  have hst : s < t := lt_of_le_of_ne hs'.1 (by intro heq; exact hs'.2 (heq ▸ ht))
  refine ⟨s, hst, hs'.2, ?_⟩
  intro i hsi hit
  by_contra hi
  have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hit, hi⟩
  have his : i ≤ s := Finset.le_max' S i hiS
  exact (not_le_of_gt hsi) his

end
end Lax343628Proofs.LastExit
