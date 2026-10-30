import Lax343628Proofs.NamedBirth
import Lax343628Proofs.SlotBirth

namespace Lax343628Proofs.PhysicalSlotLaw

open Lax343628.Algorithm Lax343628Proofs.NamedBirth
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.UniformMutation Lax343628Proofs.MaskCounts
open Lax343628Proofs.GeneralBirthApproximation Lax343628Proofs.CountStatistics
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma uniform_freshMean {α : Type*} [Fintype α] [DecidableEq α] {N w : ℕ} (hw : w ≤ N)
    (h : Finset (α ⊕ Fin N) → ℝ) (J : Finset α) :
    mean (uniformWeight N ⟨w, by omega⟩) (fun fresh ↦ h (J.disjSum (onesSet fresh))) =
      SlotBirth.freshMean h J w := by
  have hm := mean_map (uniformWeight N ⟨w, by omega⟩) onesSet
    (fun F ↦ h (J.disjSum F))
  rw [uniformWeight_sets] at hm
  unfold SlotBirth.freshMean SlotBirth.freshLaw
  have heq : (⟨min w (Fintype.card (Fin N)), by omega⟩ : Fin (Fintype.card (Fin N) + 1)) =
      ⟨w, by simpa using (show w < N + 1 by omega)⟩ := by
    apply Fin.ext
    simp only [Fintype.card_fin, Nat.min_eq_left hw]
  rw [heq]
  exact hm.symm

lemma ideal_eq_birthMean {n k : ℕ} (R : Finset (Fin n)) (hk : k ≤ R.card) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (f : BitString n → ℝ) :
    idealBirthMean k R x y f =
      SlotBirth.birthMean k (fun S ↦ f (physicalChild R x y S)) := by
  unfold idealBirthMean
  rw [outsideLaw_zero_mean]
  have htest (inherited : Differing R x y → Fin 2) :
      poissonPlacement k R.card (fun fresh ↦
        f (freshChild R (outsideFromBits R x y (fun j ↦ 1 - inherited j)) fresh)) =
      poissonMean k (SlotBirth.freshMean (fun S ↦ f (physicalChild R x y S))
        (MaskSets.selected inherited)) := by
    unfold poissonPlacement poissonMean
    apply Finset.sum_congr rfl
    intro w hw
    have hwk : w ≤ k := by have := Finset.mem_range.mp hw; omega
    have hwN := hwk.trans hk
    rw [weightAverage, dif_pos hwN]
    congr 1
    have hu := uniform_freshMean hwN (fun S ↦ f (physicalChild R x y S)) (MaskSets.selected inherited)
    refine (congrArg (mean (uniformWeight R.card ⟨w, by omega⟩)) ?_).trans hu
    funext fresh
    exact congrArg f (child_eq_physicalChild R x y hR inherited fresh)
  simp_rw [htest]
  exact MaskSets.fair_mean (α := Differing R x y)
    (fun J ↦ poissonMean k (SlotBirth.freshMean (fun S ↦ f (physicalChild R x y S)) J))

end
end Lax343628Proofs.PhysicalSlotLaw
