import Lax343628Proofs.PhaseScale
import Lax343628Proofs.GrowthParameters
import Lax343628Proofs.CoreWaitingBound

namespace Lax343628Proofs.SeedBudget

open Lax343628Proofs.BlockParameterBounds
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma rho_small (S rho : ℝ) (hS : 16777216 ≤ S) (hrho : rho ≤ 1 / S ^ 49) : rho ≤ 1 / 4 := by
  have hs : 1 ≤ S := by linarith
  have hp : S ^ 1 ≤ S ^ 49 := pow_le_pow_right₀ hs (by norm_num)
  norm_num only [pow_one] at hp
  apply hrho.trans ((div_le_div_of_nonneg_left (by norm_num) (by linarith : 0 < S) hp).trans _)
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

lemma cost (S K rho n : ℝ) (hS : 16777216 ≤ S) (hK : 1 ≤ K) (hKS : K ≤ S)
    (hrho : rho ≤ 1 / S ^ 49) (hn : S ^ 300 ≤ n) :
    2 * K * (1 / S ^ 8) + 2 * rho + 256 * K ^ 2 / n + 1 / n ≤ Real.exp (-1) / (64 * K ^ 2) := by
  have hs : 1 ≤ S := by linarith
  have hsp : 0 < S := by linarith
  have hnp : 0 < n := (pow_pos hsp 300).trans_le hn
  have hKp : 0 < K := by linarith
  have hk2 := pow_le_pow_left₀ hKp.le hKS 2
  have hs2 : 1 ≤ S ^ 2 := one_le_pow₀ hs
  have h1a := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKS (show (0 : ℝ) ≤ 2 by norm_num))
    (show 0 ≤ S ^ 8 by positivity)
  have h1b := denominator S (S ^ 8) 2 1 8 7 hs (by norm_num) le_rfl (by norm_num)
  norm_num only [pow_one] at h1b
  have h1 : 2 * K * (1 / S ^ 8) ≤ 2 / S ^ 7 := by
    have hh := h1a.trans h1b
    convert hh using 1 <;> first | rfl | ring
  have hpow : S ^ 7 ≤ S ^ 49 := pow_le_pow_right₀ hs (by norm_num)
  have h2 : 2 * rho ≤ 2 / S ^ 7 := by
    have hh := hrho.trans (div_le_div_of_nonneg_left (by norm_num) (pow_pos hsp 7) hpow)
    linear_combination 2 * hh
  have h3a : 256 * K ^ 2 / n + 1 / n ≤ 257 * S ^ 2 / n := by
    have hh := div_le_div_of_nonneg_right (show 256 * K ^ 2 + 1 ≤ 257 * S ^ 2 by nlinarith) hnp.le
    convert hh using 1 <;> first | rfl | ring
  have h3b := denominator S n 257 2 300 7 hs (by norm_num) hn (by norm_num)
  have hsum : 2 * K * (1 / S ^ 8) + 2 * rho + 256 * K ^ 2 / n + 1 / n ≤ 261 / S ^ 7 := by
    linear_combination h1 + h2 + h3a + h3b
  have hs5 : (66816 : ℝ) ≤ S ^ 5 := by
    have hh : S ^ 1 ≤ S ^ 5 := pow_le_pow_right₀ hs (by norm_num)
    norm_num only [pow_one] at hh
    linarith
  have hsmall : 261 / S ^ 7 ≤ 1 / (256 * S ^ 2) := by
    apply (div_le_div_iff₀ (pow_pos hsp 7) (by positivity : 0 < 256 * S ^ 2)).mpr
    have hh := mul_le_mul_of_nonneg_left hs5 (sq_nonneg S)
    have heq : S ^ 7 = S ^ 2 * S ^ 5 := by rw [← pow_add]
    rw [heq]
    nlinarith
  have hright : 1 / (256 * S ^ 2) ≤ Real.exp (-1) / (64 * K ^ 2) := by
    have h1 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      (show 0 < 64 * K ^ 2 by positivity) (mul_le_mul_of_nonneg_left hk2 (show (0 : ℝ) ≤ 64 by norm_num))
    have h2 := div_le_div_of_nonneg_right GrowthParameters.exp_lower (show 0 ≤ 64 * K ^ 2 by positivity)
    have hh := h1.trans h2
    convert hh using 1 <;> first | rfl | (field_simp; ring)
  exact hsum.trans (hsmall.trans hright)

lemma mutation (S K n pc : ℝ) (hS : 16777216 ≤ S) (hK : 1 ≤ K) (hKS : K ≤ S)
    (hn : S ^ 300 ≤ n) (hpc : 1 / S ≤ pc) : K / n ≤ pc * Real.exp (-1) / (128 * K ^ 2) := by
  have hs : 1 ≤ S := by linarith
  have hsp : 0 < S := by linarith
  have hnp : 0 < n := (pow_pos hsp 300).trans_le hn
  have hKp : 0 < K := by linarith
  have hpc0 : 0 ≤ pc := (by positivity : (0 : ℝ) ≤ 1 / S).trans hpc
  have h1 := div_le_div_of_nonneg_right hKS hnp.le
  have h2 := denominator S n 1 1 300 299 hs (by norm_num) hn (by norm_num)
  norm_num only [one_mul, pow_one] at h2
  have hs296 : (512 : ℝ) ≤ S ^ 296 := by
    have hh : S ^ 1 ≤ S ^ 296 := pow_le_pow_right₀ hs (by norm_num)
    norm_num only [pow_one] at hh
    linarith
  have h3 : 1 / S ^ 299 ≤ 1 / (512 * S ^ 3) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < 512 * S ^ 3)
    have hh := mul_le_mul_of_nonneg_left hs296 (show 0 ≤ S ^ 3 by positivity)
    have heq : S ^ 299 = S ^ 3 * S ^ 296 := by rw [← pow_add]
    rw [heq]
    nlinarith
  have hk2 := pow_le_pow_left₀ hKp.le hKS 2
  have hright : 1 / (512 * S ^ 3) ≤ pc * Real.exp (-1) / (128 * K ^ 2) := by
    have hnum := mul_le_mul hpc GrowthParameters.exp_lower (by norm_num : (0 : ℝ) ≤ 1 / 4) hpc0
    have hd := div_le_div_of_nonneg_left (show 0 ≤ (1 / S) * (1 / 4 : ℝ) by positivity)
      (show 0 < 128 * K ^ 2 by positivity) (mul_le_mul_of_nonneg_left hk2 (show (0 : ℝ) ≤ 128 by norm_num))
    have hn' := div_le_div_of_nonneg_right hnum (show 0 ≤ 128 * K ^ 2 by positivity)
    have hh := hd.trans hn'
    convert hh using 1 <;> first | rfl | (field_simp; ring)
  exact h1.trans (h2.trans (h3.trans hright))

end
end Lax343628Proofs.SeedBudget
