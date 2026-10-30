import Lax343628Proofs.ElementaryBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lax343628Proofs.ReciprocalCosts

open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma sqrt_step (x : ℝ) (hx : 0 ≤ x) : 1 / Real.sqrt (x + 1) ≤ 2 * (Real.sqrt (x + 1) - Real.sqrt x) := by
  have hp : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr (by linarith)
  apply (div_le_iff₀ hp).mpr
  have h1 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have h0 := Real.sq_sqrt hx
  nlinarith [sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x)]

lemma sum_inv_sqrt (M : ℕ) : (∑ j ∈ Finset.range M, 1 / Real.sqrt ((j : ℝ) + 1)) ≤ 2 * Real.sqrt M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hh := sqrt_step (M : ℝ) (by positivity)
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

lemma reciprocal_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (a + b) ≤ 1 / (Real.sqrt a * Real.sqrt b) := by
  have hsum : Real.sqrt a * Real.sqrt b ≤ a + b := by
    have h1 := Real.sq_sqrt ha.le
    have h2 := Real.sq_sqrt hb.le
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsum

lemma point (M j : ℕ) (hM : 0 < M) (hj : 0 < j) (a : ℝ) (ha : 0 < a) :
    1 / (a + (j : ℝ) / M) ≤ (Real.sqrt M / Real.sqrt a) * (1 / Real.sqrt j) := by
  have hmR : (0 : ℝ) < M := by exact_mod_cast hM
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hh := reciprocal_add a ((j : ℝ) / M) ha (div_pos hjR hmR)
  apply hh.trans_eq
  rw [Real.sqrt_div hjR.le]
  field_simp

lemma offset (M : ℕ) (a : ℝ) (ha : 0 < a) :
    (∑ j ∈ Finset.range M, 1 / (a + (j : ℝ) / M)) ≤ 1 / a + 2 * M / Real.sqrt a := by
  cases M with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero, zero_div, add_zero]; positivity
  | succ M =>
    rw [Finset.sum_range_succ']
    have hpoint := Finset.sum_le_sum (s := Finset.range M) (fun j _ ↦ point (M + 1) (j + 1) (by omega) (by omega) a ha)
    rw [← Finset.mul_sum] at hpoint
    have hsum := sum_inv_sqrt M
    have hsum' : (∑ j ∈ Finset.range M, 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (M + 1 : ℕ) := by
      have hsqrt := Real.sqrt_le_sqrt (show (M : ℝ) ≤ (M + 1 : ℕ) by exact_mod_cast Nat.le_succ M)
      norm_num only [Nat.cast_add, Nat.cast_one] at *
      linarith
    have hh := hpoint.trans (mul_le_mul_of_nonneg_left hsum'
      (show 0 ≤ Real.sqrt (M + 1 : ℕ) / Real.sqrt a by positivity))
    have heq : (Real.sqrt (M + 1 : ℕ) / Real.sqrt a) * (2 * Real.sqrt (M + 1 : ℕ)) =
        2 * (M + 1 : ℕ) / Real.sqrt a := by
      rw [div_mul_eq_mul_div]
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M + 1 : ℕ) by positivity)
      congr 1
      nlinarith
    rw [heq] at hh
    norm_num only [Nat.cast_zero, zero_div, add_zero]
    linarith

end
end Lax343628Proofs.ReciprocalCosts
