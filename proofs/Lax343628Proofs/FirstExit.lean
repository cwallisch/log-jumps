import Lax343628Proofs.Trajectories

namespace Lax343628Proofs.FirstExit

open Lax343628Proofs.Trajectories
open scoped Classical
noncomputable section

variable {α : Type*}

lemma frozen_before {R : ℕ} (A : Set α) (h : Fin (R + 1) → α)
    (t : Fin (R + 1)) (ht : h t ∉ A) :
    ∃ j, j ≤ t ∧ frozen A h = h j ∧ h j ∉ A := by
  induction R with
  | zero =>
    have ht0 : t = 0 := Fin.ext (by have := t.isLt; omega)
    subst t
    exact ⟨0, le_rfl, rfl, ht⟩
  | succ R ih =>
    by_cases htv : t.val < R + 1
    · let t' : Fin (R + 1) := ⟨t.val, htv⟩
      have htt : t'.castSucc = t := Fin.ext rfl
      have ht' : Fin.init h t' ∉ A := by change h t'.castSucc ∉ A; rw [htt]; exact ht
      obtain ⟨j, hj, heq, hnot⟩ := ih (Fin.init h) t' ht'
      have hf : frozen A (Fin.init h) ∉ A := heq ▸ hnot
      refine ⟨j.castSucc, ?_, ?_, hnot⟩
      · exact Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hj)
      · change (if frozen A (Fin.init h) ∈ A then h (Fin.last (R + 1)) else frozen A (Fin.init h)) = h j.castSucc
        rw [if_neg hf]
        exact heq
    · have htt : t = Fin.last (R + 1) := Fin.ext (by have := t.isLt; simp only [Fin.val_last]; omega)
      by_cases hf : frozen A (Fin.init h) ∈ A
      · refine ⟨t, le_rfl, ?_, ht⟩
        change (if frozen A (Fin.init h) ∈ A then h (Fin.last (R + 1)) else frozen A (Fin.init h)) = h t
        rw [if_pos hf, htt]
      · obtain ⟨j, hj⟩ := frozen_mem_range A (Fin.init h)
        refine ⟨j.castSucc, Fin.le_iff_val_le_val.mpr (by rw [htt]; exact Nat.le_of_lt j.isLt), ?_, ?_⟩
        · change (if frozen A (Fin.init h) ∈ A then h (Fin.last (R + 1)) else frozen A (Fin.init h)) = h j.castSucc
          rw [if_neg hf]
          exact hj
        · change Fin.init h j ∉ A
          rw [← hj]
          exact hf

lemma frozen_in_of_exit_before {R : ℕ} (A B : Set α) (h : Fin (R + 1) → α)
    (t : Fin (R + 1)) (ht : h t ∉ A) (hB : ∀ j, j ≤ t → h j ∉ A → h j ∈ B) :
    frozen A h ∈ B := by
  obtain ⟨j, hj, heq, hnot⟩ := frozen_before A h t ht
  rw [heq]
  exact hB j hj hnot

end
end Lax343628Proofs.FirstExit
