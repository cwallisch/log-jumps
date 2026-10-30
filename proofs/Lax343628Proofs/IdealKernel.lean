import Lax343628Proofs.WeightSums

namespace Lax343628Proofs.IdealKernel

open Lax343628Proofs.Weights Lax343628Proofs.WeightSums
open scoped BigOperators

noncomputable section

def kernel (i j t u : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ (2 * (i + j - t - u)) *
    ∑ l ∈ Finset.range (i + j - 2 * t + 1),
      (i + j - 2 * t).choose l * weight (t + l) *
        (if u ≤ t + l then
          ∑ s ∈ Finset.range (t + l - u + 1),
            ((i + j - 2 * u).choose (t + l - u - s) : ℝ) / (s.factorial : ℝ)
        else 0)

def copyKernel (i j t u : ℕ) : ℝ :=
  if t = 0 ∧ u = 0 then (4 : ℝ)⁻¹ ^ i * (4 : ℝ)⁻¹ ^ j else 0

lemma kernel_nonneg (i j t u : ℕ) : 0 ≤ kernel i j t u := by
  unfold kernel
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro l _
  apply mul_nonneg (mul_nonneg (by positivity) (weight_nonneg _))
  split_ifs <;> positivity

lemma copy_le (i j t u : ℕ) :
    copyKernel i j t u ≤ (4 : ℝ)⁻¹ ^ i * (4 : ℝ)⁻¹ ^ j := by
  unfold copyKernel
  split_ifs
  · exact le_rfl
  · positivity

lemma kernel_anchor (r : ℕ) :
    kernel 0 r 0 0 = ∑ l ∈ Finset.range (r + 1), coefficient r l * weight l := by
  unfold kernel
  simp only [Nat.zero_add, Nat.mul_zero, Nat.sub_zero, Nat.zero_le, if_true]
  rw [pow_mul, show (2 : ℝ)⁻¹ ^ 2 = (4 : ℝ)⁻¹ by norm_num, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  unfold coefficient
  ring

lemma kernel_anchor_zero : kernel 0 0 0 0 = 0 := by
  norm_num [kernel, Finset.sum_range_succ, weight_zero]

lemma twice_anchor_one : 2 * kernel 0 1 0 0 = 1 := by
  rw [kernel_anchor]
  exact anchor_crossing_one

lemma twice_anchor {r : ℕ} (hr : 2 ≤ r) : 2 * kernel 0 r 0 0 = (17 / 16 : ℝ) * weight r := by
  rw [kernel_anchor]
  exact anchor_crossing hr

lemma kernel_one_one : kernel 1 1 1 1 = 1 := by
  norm_num [kernel, Finset.sum_range_succ, weight_zero, weight_one, weight_two]

lemma kernel_one_zero : kernel 1 1 1 0 = 3 / 4 := by
  norm_num [kernel, Finset.sum_range_succ, weight_zero, weight_one, weight_two]

lemma kernel_zero_one : kernel 1 1 0 1 = 4 / 5 := by
  norm_num [kernel, Finset.sum_range_succ, weight_zero, weight_one, weight_two]

lemma kernel_zero_zero : kernel 1 1 0 0 = 51 / 80 := by
  norm_num [kernel, Finset.sum_range_succ, weight_zero, weight_one, weight_two]

lemma distance_one_bounds {t u : ℕ} (ht : t ≤ 1) (hu : u ≤ 1) :
    (51 / 80 : ℝ) ≤ kernel 1 1 t u ∧ kernel 1 1 t u ≤ 1 := by
  interval_cases t <;> interval_cases u <;>
    norm_num [kernel_one_one, kernel_one_zero, kernel_zero_one, kernel_zero_zero]

end
end Lax343628Proofs.IdealKernel
