import Lax343628Proofs.PlateauApproximation
import Lax343628Proofs.IdealKernel

namespace Lax343628Proofs.IdealCountKernel

open Lax343628Proofs.CountStatistics Lax343628Proofs.PlateauApproximation
open Lax343628Proofs.FiniteDrift Lax343628Proofs.IdealKernel Lax343628Proofs.Weights
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma fair_countMean (N : ℕ) (f : ℕ → ℝ) :
    countMean N (1 / 2) f = (2 : ℝ)⁻¹ ^ N *
      ∑ w ∈ Finset.range (N + 1), (N.choose w : ℝ) * f w := by
  rw [countMean_formula N _ (by norm_num), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hwN : w ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
  have hpow : (2 : ℝ)⁻¹ ^ w * (2 : ℝ)⁻¹ ^ (N - w) = (2 : ℝ)⁻¹ ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hwN]
  norm_num only [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
    show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num]
  norm_num only [inv_eq_one_div] at hpow
  rw [← hpow]
  ring

lemma fair_balanced_mean (D a u : ℕ) (ψ : ℕ → ℝ) :
    countMean D (1 / 2) (fun v ↦ balanced ψ a (u + v)) =
      (2 : ℝ)⁻¹ ^ D * ψ a * (if u ≤ a then (D.choose (a - u) : ℝ) else 0) := by
  rw [fair_countMean]
  by_cases hua : u ≤ a
  · rw [if_pos hua]
    by_cases hv : a - u ≤ D
    · rw [Finset.sum_eq_single (a - u)]
      · rw [balanced, if_pos (by omega : a = u + (a - u))]
        ring
      · intro v _ hv'
        rw [balanced, if_neg (by omega : a ≠ u + v), mul_zero]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    · have hchoose : D.choose (a - u) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hchoose, Nat.cast_zero, mul_zero]
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro v hv'
      rw [balanced, if_neg (by have h := Finset.mem_range.mp hv'; omega), mul_zero]
  · rw [if_neg hua, mul_zero]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro v _
    rw [balanced, if_neg (by omega : a ≠ u + v), mul_zero]

lemma poisson_fair_balanced (k D a u : ℕ) (ha : a ≤ k) (ψ : ℕ → ℝ) :
    poissonMean k (fun w ↦ countMean D (1 / 2)
      (fun v ↦ balanced ψ a (u + w + v))) =
        Real.exp (-1) * (2 : ℝ)⁻¹ ^ D * ψ a *
          (if u ≤ a then ∑ w ∈ Finset.range (a - u + 1),
            (D.choose (a - u - w) : ℝ) / (w.factorial : ℝ) else 0) := by
  unfold poissonMean
  simp_rw [fair_balanced_mean]
  by_cases hua : u ≤ a
  · rw [if_pos hua]
    have hrestrict :
        (∑ w ∈ Finset.range (k + 1), Real.exp (-1) / (w.factorial : ℝ) *
          ((2 : ℝ)⁻¹ ^ D * ψ a * (if u + w ≤ a then (D.choose (a - (u + w)) : ℝ) else 0))) =
        ∑ w ∈ Finset.range (a - u + 1), Real.exp (-1) / (w.factorial : ℝ) *
          ((2 : ℝ)⁻¹ ^ D * ψ a * (if u + w ≤ a then (D.choose (a - (u + w)) : ℝ) else 0)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro w _ hw
      have hwa : ¬u + w ≤ a := by simp only [Finset.mem_range] at hw; omega
      rw [if_neg hwa, mul_zero, mul_zero]
    rw [hrestrict, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    have hwa : u + w ≤ a := by have h := Finset.mem_range.mp hw; omega
    rw [if_pos hwa, show a - (u + w) = a - u - w by omega]
    ring
  · rw [if_neg hua, mul_zero]
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg (by omega : ¬u + w ≤ a), mul_zero, mul_zero]

lemma idealMean_formula (k A D t u : ℕ) (hA : t + A ≤ k) (ψ : ℕ → ℝ) :
    idealMean k A D t u ψ = Real.exp (-1) * (2 : ℝ)⁻¹ ^ (A + D) *
      ∑ l ∈ Finset.range (A + 1), (A.choose l : ℝ) * ψ (t + l) *
        (if u ≤ t + l then ∑ w ∈ Finset.range (t + l - u + 1),
          (D.choose (t + l - u - w) : ℝ) / (w.factorial : ℝ) else 0) := by
  unfold idealMean
  rw [fair_countMean, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have htl : t + l ≤ k := by have h := Finset.mem_range.mp hl; omega
  rw [poisson_fair_balanced k D (t + l) u htl ψ, pow_add]
  ring

lemma idealMean_weight_kernel {k i j t u : ℕ}
    (ht : 2 * t ≤ i + j) (hu : 2 * u ≤ i + j) (hA : t + (i + j - 2 * t) ≤ k) :
    idealMean k (i + j - 2 * t) (i + j - 2 * u) t u weight =
      Real.exp (-1) * kernel i j t u := by
  rw [idealMean_formula _ _ _ _ _ hA]
  have hexponent : (i + j - 2 * t) + (i + j - 2 * u) =
      2 * (i + j - t - u) := by omega
  rw [hexponent, kernel]
  ring

def cloneWeight (r : ℕ) : ℝ := if r = 0 then 1 else 0

lemma idealMean_clone_formula (k A D t u : ℕ) (hA : t + A ≤ k) :
    idealMean k A D t u cloneWeight =
      if t = 0 ∧ u = 0 then Real.exp (-1) * (2 : ℝ)⁻¹ ^ (A + D) else 0 := by
  rw [idealMean_formula _ _ _ _ _ hA]
  by_cases ht : t = 0
  · subst t
    simp only [Nat.zero_add]
    rw [Finset.sum_eq_single 0]
    · by_cases hu : u = 0
      · subst u
        norm_num [cloneWeight, Finset.sum_range_succ]
      · have hule : ¬u ≤ 0 := by omega
        simp [cloneWeight, hu, hule]
    · intro l _ hl
      simp [cloneWeight, hl]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg (by simp [ht])]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro l _
    simp [cloneWeight, ht]

lemma idealMean_clone_kernel {k i j t u : ℕ}
    (hA : t + (i + j - 2 * t) ≤ k) :
    idealMean k (i + j - 2 * t) (i + j - 2 * u) t u cloneWeight =
      Real.exp (-1) * copyKernel i j t u := by
  rw [idealMean_clone_formula _ _ _ _ _ hA, copyKernel]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    simp only [Nat.mul_zero, Nat.sub_zero]
    rw [show i + j + (i + j) = 2 * (i + j) by omega, pow_mul,
      show (2 : ℝ)⁻¹ ^ 2 = (4 : ℝ)⁻¹ by norm_num, pow_add]
  · simp

lemma idealMean_viability {k r : ℕ} (hr : r ≤ k) :
    idealMean k r r 0 0 (fun _ ↦ 1) = Real.exp (-1) *
      Lax343628Proofs.Profiles.viability r := by
  rw [idealMean_formula _ _ _ _ _ (by simpa using hr)]
  simp only [Nat.zero_add, Nat.zero_le, if_true, mul_one, Nat.sub_zero]
  rw [show r + r = 2 * r by omega, pow_mul,
    show (2 : ℝ)⁻¹ ^ 2 = (4 : ℝ)⁻¹ by norm_num]
  rw [← Lax343628Proofs.WeightSums.coefficient_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  unfold coefficient
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

end
end Lax343628Proofs.IdealCountKernel
