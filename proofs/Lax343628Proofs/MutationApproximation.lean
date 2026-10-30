import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Lax343628Proofs.MutationApproximation

lemma log_one_sub_lower (u : ℝ) (_hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    -u - 2 * u ^ 2 ≤ Real.log (1 - u) := by
  have hb : 0 < 1 - u := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hb
  have heq : 1 - (1 - u)⁻¹ = -u / (1 - u) := by field_simp; ring
  rw [heq] at hlog
  apply le_trans _ hlog
  apply (le_div_iff₀ hb).mpr
  nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 1 - 2 * u by linarith)]

lemma log_one_sub_upper (u : ℝ) (hu : u < 1) : Real.log (1 - u) ≤ -u := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 - u by linarith)
  linarith

lemma no_mutation_approximation (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (-1) - 2 / n ≤ (1 - 1 / (n : ℝ)) ^ n ∧
      (1 - 1 / (n : ℝ)) ^ n ≤ Real.exp (-1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hq : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
  have hq0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hb : 0 < 1 - 1 / (n : ℝ) := by linarith
  have heq : Real.exp ((n : ℝ) * Real.log (1 - 1 / (n : ℝ))) =
      (1 - 1 / (n : ℝ)) ^ n := by rw [Real.exp_nat_mul, Real.exp_log hb]
  have hlow : -1 - 2 / (n : ℝ) ≤ (n : ℝ) * Real.log (1 - 1 / (n : ℝ)) := by
    calc
      -1 - 2 / (n : ℝ) = (n : ℝ) * (-(1 / (n : ℝ)) - 2 * (1 / (n : ℝ)) ^ 2) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_one_sub_lower _ hq0 hq) hnpos.le
  have hupp : (n : ℝ) * Real.log (1 - 1 / (n : ℝ)) ≤ -1 := by
    have h := mul_le_mul_of_nonneg_left (log_one_sub_upper (1 / (n : ℝ)) (by linarith)) hnpos.le
    have hid : (n : ℝ) * (-(1 / (n : ℝ))) = -1 := by field_simp
    simpa only [hid] using h
  constructor
  · have hexp := Real.add_one_le_exp (-(2 / (n : ℝ)))
    have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-1)).le
    have hnonneg := mul_nonneg (show 0 ≤ 2 / (n : ℝ) by positivity) (show 0 ≤ 1 - Real.exp (-1) by linarith)
    have hmain : Real.exp (-1) - 2 / n ≤ Real.exp (-1 - 2 / n) := by
      have hfactor : Real.exp (-1 - 2 / (n : ℝ)) =
          Real.exp (-1) * Real.exp (-(2 / (n : ℝ))) := by rw [sub_eq_add_neg, Real.exp_add]
      rw [hfactor]
      nlinarith
    exact hmain.trans ((Real.exp_le_exp.mpr hlow).trans_eq heq)
  · exact heq.symm.trans_le (Real.exp_le_exp.mpr hupp)

lemma shorter_mutation_approximation (n N : ℕ) (hn : 2 ≤ n) (hN : N ≤ n) :
    |(1 - 1 / (n : ℝ)) ^ N - Real.exp (-1)| ≤ 2 * ((n - N : ℕ) + 1) / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hq : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
  have hq0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hb : 0 < 1 - 1 / (n : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hN
  have hdef : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := Nat.cast_sub hN
  have hd0 : (0 : ℝ) ≤ ((n - N : ℕ) : ℝ) / n := by positivity
  have hd1 : ((n - N : ℕ) : ℝ) / n ≤ 1 := by
    apply (div_le_one hnpos).mpr
    rw [hdef]
    linarith
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hbase : 1 - 1 / (n : ℝ) ≤ 1 := by linarith
  have hlower : Real.exp (-1) - 2 / n ≤ (1 - 1 / (n : ℝ)) ^ N :=
    (no_mutation_approximation n hn).1.trans (pow_le_pow_of_le_one hb.le hbase hN)
  have hupp : (1 - 1 / (n : ℝ)) ^ N ≤ Real.exp (-1) + 2 * ((n - N : ℕ) : ℝ) / n := by
    have hlog := mul_le_mul_of_nonneg_left (log_one_sub_upper (1 / (n : ℝ)) (by linarith)) hN0
    have hprod : (N : ℝ) * (-(1 / (n : ℝ))) = -1 + ((n - N : ℕ) : ℝ) / n := by
      rw [hdef]
      field_simp
      ring
    rw [hprod] at hlog
    have hpow : (1 - 1 / (n : ℝ)) ^ N ≤
        Real.exp (-1 + ((n - N : ℕ) : ℝ) / n) := by
      have h := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_nat_mul, Real.exp_log hb] at h
    have hsmall : |((n - N : ℕ) : ℝ) / n| ≤ 1 := by rw [abs_of_nonneg hd0]; exact hd1
    have hexp := (le_abs_self (Real.exp (((n - N : ℕ) : ℝ) / n) - 1)).trans
      (Real.abs_exp_sub_one_le hsmall)
    rw [abs_of_nonneg hd0] at hexp
    have hscaled := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-1)).le
    have herror := mul_nonneg hd0 (show 0 ≤ 1 - Real.exp (-1) by linarith)
    rw [Real.exp_add] at hpow
    simp only [div_eq_mul_inv] at hexp hscaled herror hpow ⊢
    nlinarith
  have hradius : 2 * (((n - N : ℕ) : ℝ) + 1) / n =
      2 / (n : ℝ) + 2 * ((n - N : ℕ) : ℝ) / n := by ring
  rw [hradius]
  apply abs_le.mpr
  simp only [div_eq_mul_inv] at hlower hupp hd0 ⊢
  constructor <;> nlinarith

end Lax343628Proofs.MutationApproximation
