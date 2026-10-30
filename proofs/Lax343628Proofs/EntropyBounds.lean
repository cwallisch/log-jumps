import Lax343628Proofs.EntropyLedger

namespace Lax343628Proofs.EntropyBounds

open Lax343628Proofs.SparseEnvironment
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma net (n k R J : ℕ) (rs : ℕ+) (hk : k ≤ n) (hn : 1 ≤ n) (S W : ℝ)
    (hS : 16777216 ≤ S) (hW : 1 ≤ W) (hkS : (k : ℝ) ≤ S)
    (hJ : (J : ℝ) ≤ S ^ 54) (hrs : ((rs : ℕ) : ℝ) ≤ S ^ 120)
    (hlogn : Real.log n ≤ W) (hlogR : Real.log ((R : ℝ) + 1) ≤ S ^ 2 * W) :
    Real.log (Fintype.card (Net n k R J rs) : ℝ) ≤ S ^ 176 * W := by
  have hS1 : 1 ≤ S := by linarith
  have hSp : 0 < S := by linarith
  have hWp : 0 ≤ W := by linarith
  have hprod : (J : ℝ) * (rs : ℕ) * k ≤ S ^ 175 := by
    calc
      _ ≤ S ^ 54 * S ^ 120 * S := by gcongr
      _ = _ := by ring
  have hmul := mul_le_mul hprod hlogn
    (Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)) (show 0 ≤ S ^ 175 by positivity)
  have hnet := net_log_card (R := R) (J := J) hk hn rs
  have hpow : S ^ 2 ≤ S ^ 175 := pow_le_pow_right₀ hS1 (by norm_num)
  have hp := mul_le_mul_of_nonneg_right hpow hWp
  have hs2 : (2 : ℝ) ≤ S := by linarith
  have hm := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ S ^ 175 * W by positivity)
  have heq : S ^ 176 * W = S * (S ^ 175 * W) := by ring
  rw [heq]
  linarith

lemma coefficient (C R : ℕ) (S W : ℝ) (hC : 1 ≤ C) (hS : 16777216 ≤ S) (hW : 1 ≤ W)
    (hlogC : Real.log (C : ℝ) ≤ S ^ 176 * W)
    (hlogR : Real.log ((R : ℝ) + 1) ≤ S ^ 2 * W) :
    Real.log (4 * (C : ℝ) * ((R : ℝ) + 1) + 1) ≤ S ^ 180 * W := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hS1 : 1 ≤ S := by linarith
  have hWp : 0 ≤ W := by linarith
  have hCR : 1 ≤ (C : ℝ) * ((R : ℝ) + 1) := by
    have hR : (0 : ℝ) ≤ R := by positivity
    nlinarith
  have hh := Real.log_le_log (show 0 < 4 * (C : ℝ) * ((R : ℝ) + 1) + 1 by positivity)
    (show 4 * (C : ℝ) * ((R : ℝ) + 1) + 1 ≤ 5 * (C : ℝ) * ((R : ℝ) + 1) by nlinarith)
  rw [Real.log_mul (by positivity : 5 * (C : ℝ) ≠ 0) (by positivity : ((R : ℝ) + 1) ≠ 0),
    Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hCp.ne'] at hh
  have hl5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
  have hpow : S ^ 2 ≤ S ^ 176 := pow_le_pow_right₀ hS1 (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hpow hWp
  have hbase : 1 ≤ S ^ 176 * W := by
    have hp : 1 ≤ S ^ 176 := one_le_pow₀ hS1
    nlinarith
  have hp4 : (6 : ℝ) ≤ S ^ 4 := by
    have hp : S ^ 1 ≤ S ^ 4 := pow_le_pow_right₀ hS1 (by norm_num)
    norm_num only [pow_one] at hp
    linarith
  have hfinal := mul_le_mul_of_nonneg_right hp4 (show 0 ≤ S ^ 176 * W by positivity)
  have heq : S ^ 180 * W = S ^ 4 * (S ^ 176 * W) := by ring
  rw [heq]
  linarith

lemma error (C R : ℕ) (S W delta : ℝ) (hC : 1 ≤ C) (hS : 16777216 ≤ S) (hW : 1 ≤ W)
    (hd : 0 < delta) (hlogd : Real.log (1 / delta) ≤ W)
    (hlog : Real.log (4 * (C : ℝ) * ((R : ℝ) + 1) + 1) ≤ S ^ 180 * W) :
    (4 * (C : ℝ) * ((R : ℝ) + 1) + 1) * Real.exp (-(S ^ 184 * W)) ≤ delta := by
  have hSp : 0 < S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hCp : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hcoef : 0 < 4 * (C : ℝ) * ((R : ℝ) + 1) + 1 := by positivity
  have hp180 : 1 ≤ S ^ 180 := one_le_pow₀ hS1
  have hp4 : (2 : ℝ) ≤ S ^ 4 := by
    have hp : S ^ 1 ≤ S ^ 4 := pow_le_pow_right₀ hS1 (by norm_num)
    norm_num only [pow_one] at hp
    linarith
  have hpow : S ^ 180 + 1 ≤ S ^ 184 := by
    have hh := mul_le_mul_of_nonneg_left hp4 (show 0 ≤ S ^ 180 by positivity)
    have heq : S ^ 184 = S ^ 180 * S ^ 4 := by rw [← pow_add]
    rw [heq]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ W by linarith)
  have hlogd' : -Real.log delta ≤ W := by simpa only [one_div, Real.log_inv] using hlogd
  have hlower : Real.log (4 * (C : ℝ) * ((R : ℝ) + 1) + 1) - S ^ 184 * W ≤ Real.log delta := by
    nlinarith
  have hh := Real.exp_le_exp.mpr hlower
  rw [Real.exp_log hd] at hh
  have heq : Real.exp (Real.log (4 * (C : ℝ) * ((R : ℝ) + 1) + 1) - S ^ 184 * W) =
      (4 * (C : ℝ) * ((R : ℝ) + 1) + 1) * Real.exp (-(S ^ 184 * W)) := by
    rw [Real.exp_sub, Real.exp_log hcoef, Real.exp_neg]
    rfl
  rwa [heq] at hh

end
end Lax343628Proofs.EntropyBounds
