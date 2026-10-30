import Lax343628Proofs.FairCount

namespace Lax343628Proofs.FairMedian

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.FairCount
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def probability (N : ℕ) (A : Set (Fin (N + 1))) : ℝ :=
  mean (law N) (fun w ↦ if w ∈ A then 1 else 0)

lemma mono (N : ℕ) {A B : Set (Fin (N + 1))} (h : A ⊆ B) : probability N A ≤ probability N B := by
  apply mean_mono
  intro w
  by_cases ha : w ∈ A
  · rw [if_pos ha, if_pos (h ha)]
  · rw [if_neg ha]
    split_ifs <;> norm_num

lemma split (N : ℕ) (A : Set (Fin (N + 1))) : probability N A + probability N Aᶜ = 1 := by
  rw [probability, probability, ← mean_add]
  convert mean_const (law N) 1 using 1
  congr 1
  funext w
  by_cases hw : w ∈ A <;> simp [hw]

lemma tail_symmetry (N : ℕ) : probability N {w | N < 2 * w.val} = probability N {w | 2 * w.val < N} := by
  have hh := congrArg (fun p : PMF (Fin (N + 1)) ↦ mean p (fun w ↦ if w ∈ {v : Fin (N + 1) | N < 2 * v.val} then (1 : ℝ) else 0)) (reflection N)
  rw [mean_map] at hh
  unfold probability
  convert hh.symm using 1
  all_goals congr 1
  all_goals funext w
  all_goals have hw := w.isLt
  all_goals simp only [Fin.revPerm_apply, Fin.val_rev, Nat.add_sub_add_right, Set.mem_ofPred_eq]
  all_goals split_ifs <;> norm_num <;> omega

lemma center (N : ℕ) (hN : 1 ≤ N) : probability N {w | 2 * w.val = N} ≤ 1 / 2 := by
  by_cases hex : ∃ w : Fin (N + 1), 2 * w.val = N
  · obtain ⟨w, hw⟩ := hex
    have hs : {v : Fin (N + 1) | 2 * v.val = N} ⊆ {w} := by
      intro v hv
      apply Fin.ext
      change 2 * v.val = N at hv
      omega
    apply (mono N hs).trans
    have heq : probability N {w} = (law N w).toReal := by
      unfold probability
      simpa only [Set.mem_singleton_iff, mul_one] using mean_pick (law N) w 1
    rw [heq]
    exact atom N hN w
  · have hz : probability N {w | 2 * w.val = N} = 0 := by
      unfold probability
      have hn : ∀ w : Fin (N + 1), 2 * w.val ≠ N := by simpa only [not_exists] using hex
      simp only [Set.mem_ofPred_eq, if_neg (hn _), mean_const]
    rw [hz]
    norm_num

lemma strict_upper (N : ℕ) (hN : 1 ≤ N) : 1 / 4 ≤ probability N {w | N < 2 * w.val} := by
  have hsum : probability N {w | N < 2 * w.val} + probability N {w | 2 * w.val < N} +
      probability N {w | 2 * w.val = N} = 1 := by
    unfold probability
    rw [← mean_add, ← mean_add]
    convert mean_const (law N) 1 using 1
    congr 1
    funext w
    simp only [Set.mem_ofPred_eq]
    split_ifs <;> norm_num <;> omega
  have hc := center N hN
  rw [← tail_symmetry] at hsum
  linarith

lemma weak_upper (N : ℕ) : 1 / 2 ≤ probability N {w | N ≤ 2 * w.val} := by
  have hsum := split N {w | N ≤ 2 * w.val}
  have hcomp : probability N {w | N ≤ 2 * w.val}ᶜ = probability N {w | 2 * w.val < N} := by
    congr 1
    ext w
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hcomp, ← tail_symmetry] at hsum
  have hh := mono N (show {w : Fin (N + 1) | N < 2 * w.val} ⊆ {w | N ≤ 2 * w.val} from by
    intro w hw
    change N < 2 * w.val at hw
    change N ≤ 2 * w.val
    omega)
  linarith

lemma deviation (N : ℕ) (a : ℝ) (ha : 0 < a) :
    probability N {w | a ≤ |(w.val : ℝ) - (N : ℝ) / 2|} ≤ (N : ℝ) / (4 * a ^ 2) := by
  have hh : a ^ 2 * probability N {w | a ≤ |(w.val : ℝ) - (N : ℝ) / 2|} ≤ (N : ℝ) / 4 := by
    rw [probability, ← mean_mul, ← second]
    apply mean_mono
    intro w
    split_ifs with hw
    · have hs : a ^ 2 ≤ |(w.val : ℝ) - (N : ℝ) / 2| ^ 2 := pow_le_pow_left₀ ha.le hw 2
      simpa only [mul_one, sq_abs] using hs
    · simp only [mul_zero, sq_nonneg]
  apply (le_div_iff₀ (by positivity : 0 < 4 * a ^ 2)).mpr
  linarith

lemma weak_lower (N : ℕ) : 1 / 2 ≤ probability N {w | 2 * w.val ≤ N} := by
  have hh := congrArg (fun p : PMF (Fin (N + 1)) ↦ mean p
    (fun w ↦ if w ∈ {v : Fin (N + 1) | N ≤ 2 * v.val} then (1 : ℝ) else 0)) (reflection N)
  rw [mean_map] at hh
  have heq : probability N {w | N ≤ 2 * w.val} = probability N {w | 2 * w.val ≤ N} := by
    unfold probability
    convert hh.symm using 1
    all_goals congr 1
    all_goals funext w
    all_goals have hw := w.isLt
    all_goals simp only [Fin.revPerm_apply, Fin.val_rev, Nat.add_sub_add_right, Set.mem_ofPred_eq]
    all_goals split_ifs <;> norm_num <;> omega
  rw [← heq]
  exact weak_upper N

lemma cover (N : ℕ) (A B C : Set (Fin (N + 1))) (h : A ⊆ B ∪ C) :
    probability N A ≤ probability N B + probability N C := by
  unfold probability
  rw [← mean_add]
  apply mean_mono
  intro w
  by_cases ha : w ∈ A
  · have hh := h ha
    rcases hh with hb | hc
    · simp only [if_pos ha, if_pos hb]
      split_ifs <;> norm_num
    · simp only [if_pos ha, if_pos hc]
      split_ifs <;> norm_num
  · rw [if_neg ha]
    split_ifs <;> norm_num

end
end Lax343628Proofs.FairMedian
