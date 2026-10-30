import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Lax343628Proofs.ElementaryBounds

lemma no_mutation_lower (n : ℕ) (hn : 2 ≤ n) :
    (1 / 8 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hq0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hq : 1 / (n : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hnR
  have hb0 : 0 ≤ 1 - 1 / (n : ℝ) := by linarith
  have hb1 : 1 - 1 / (n : ℝ) ≤ 1 := by linarith
  have hmR : (n / 2 : ℕ) * (2 : ℝ) ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n 2
  have hm : ((n / 2 : ℕ) : ℝ) * (1 / (n : ℝ)) ≤ 1 / 2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hnpos).mpr
    nlinarith
  have hbern := one_add_mul_le_pow (a := -(1 / (n : ℝ))) (by linarith :
    (-2 : ℝ) ≤ -(1 / (n : ℝ))) (n / 2)
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ (n / 2) := by
    have hbern' : 1 - (n / 2 : ℕ) * (1 / (n : ℝ)) ≤
        (1 - 1 / (n : ℝ)) ^ (n / 2) := by simpa only [sub_eq_add_neg, mul_neg] using hbern
    linarith
  have hcount : n ≤ 3 * (n / 2) := by omega
  calc
    (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
    _ ≤ ((1 - 1 / (n : ℝ)) ^ (n / 2)) ^ 3 := pow_le_pow_left₀ (by norm_num) hhalf 3
    _ = (1 - 1 / (n : ℝ)) ^ (3 * (n / 2)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (1 - 1 / (n : ℝ)) ^ n := pow_le_pow_of_le_one hb0 hb1 hcount

end Lax343628Proofs.ElementaryBounds
