import Lax343628Proofs.BaseRanks
import Lax343628Proofs.Profiles
import Mathlib.RingTheory.PowerSeries.Exp

namespace Lax343628Proofs.SlotProfiles

open scoped BigOperators
open PowerSeries
open Lax343628Proofs.BaseRanks

noncomputable section

set_option backward.isDefEq.respectTransparency false

def series (v : ℕ) : PowerSeries ℝ := (1 + X) ^ v * PowerSeries.exp ℝ

def beta (v j : ℕ) : ℝ := coeff j (series v)

lemma binomial_series (v : ℕ) :
    (1 + (X : PowerSeries ℝ)) ^ v =
      ∑ s ∈ Finset.range (v + 1), C (v.choose s : ℝ) * X ^ s := by
  rw [add_comm (1 : PowerSeries ℝ) X, add_pow]
  apply Finset.sum_congr rfl
  intro s _
  simp
  ring

lemma beta_eq_rankMass (v j : ℕ) : beta v j = rankMass v j := by
  unfold beta series
  rw [binomial_series, Finset.sum_mul, map_sum]
  rw [rankMass, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro s hs
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_exp]
  simp only [map_div₀, map_one, map_natCast, rankWeight]
  split_ifs <;> simp [div_eq_mul_inv]

lemma beta_pos (v j : ℕ) : 0 < beta v j := by rw [beta_eq_rankMass]; exact rankMass_pos _ _

lemma beta_nonneg (v j : ℕ) : 0 ≤ beta v j := (beta_pos v j).le

lemma coeff_binomial (v s : ℕ) :
    coeff s ((1 + (X : PowerSeries ℝ)) ^ v) = (v.choose s : ℝ) := by
  have h : (1 + (X : PowerSeries ℝ)) ^ v =
      (((1 : Polynomial ℝ) + Polynomial.X) ^ v).toPowerSeries := by simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

lemma beta_formula (v j : ℕ) : beta v j =
    ∑ w ∈ Finset.range (j + 1), (v.choose (j - w) : ℝ) / (w.factorial : ℝ) := by
  unfold beta series
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro w _
  simp [coeff_binomial, div_eq_mul_inv, mul_comm]

lemma beta_binomial_lower (v j : ℕ) : (v.choose j : ℝ) ≤ beta v j := by
  rw [beta_formula]
  have h := Finset.single_le_sum (s := Finset.range (j + 1))
    (f := fun w ↦ (v.choose (j - w) : ℝ) / (w.factorial : ℝ))
    (fun w _ ↦ by positivity) (Finset.mem_range.mpr (show 0 < j + 1 by omega))
  simpa using h

lemma beta_upper (v j : ℕ) : beta v j ≤ (2 : ℝ) ^ v := by
  rw [beta_eq_rankMass, rankMass]
  calc
    _ ≤ ∑ s : Fin (v + 1), (v.choose s.val : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      unfold rankWeight
      split_ifs
      · apply div_le_self (by positivity)
        exact_mod_cast Nat.factorial_pos (j - s.val)
      · positivity
    _ = (2 : ℝ) ^ v := by
      rw [Fin.sum_univ_eq_sum_range (f := fun s ↦ (v.choose s : ℝ))]
      exact_mod_cast Nat.sum_range_choose v

lemma beta_zero (v : ℕ) : beta v 0 = 1 := by
  simp [beta, series]

lemma beta_one (v : ℕ) : beta v 1 = (v : ℝ) + 1 := by
  simp [beta, series, coeff_one_mul, coeff_one_pow, coeff_exp]

lemma series_derivative (v : ℕ) :
    (1 + X) * (PowerSeries.derivative ℝ (series v)) =
      (C ((v : ℝ) + 1) + X) * series v := by
  unfold series
  rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_exp]
  simp only [map_add, PowerSeries.derivative_one, PowerSeries.derivative_X, zero_add, mul_one,
    smul_eq_mul]
  cases v with
  | zero => simp
  | succ v =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [map_add, map_one, map_natCast]
    ring

lemma beta_recurrence (v j : ℕ) :
    ((j : ℝ) + 2) * beta v (j + 2) =
      ((v : ℝ) - j) * beta v (j + 1) + beta v j := by
  have h := congrArg (coeff (j + 1)) (series_derivative v)
  simp only [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul] at h
  rw [show j + 1 + 1 = j + 2 by omega,
    show (j + 1 : ℕ) = j + 1 from rfl] at h
  have hX (f : PowerSeries ℝ) : coeff (j + 1) (X * f) = coeff j f := by
    simpa only [pow_one, Nat.add_sub_cancel] using coeff_X_pow_mul f 1 j
  rw [hX, hX, coeff_derivative] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  change beta v (j + 2) * (j + 1 + 1) + beta v (j + 1) * (j + 1) =
    (v : ℝ) * beta v (j + 1) + beta v (j + 1) + beta v j at h
  nlinarith

lemma beta_recurrence_at {v j : ℕ} (hj : 1 ≤ j) :
    ((j : ℝ) + 1) * beta v (j + 1) =
      ((v : ℝ) + 1 - j) * beta v j + beta v (j - 1) := by
  have h := beta_recurrence v (j - 1)
  have hsub : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj, Nat.cast_one]
  rw [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega, hsub] at h
  nlinarith

lemma beta_pascal (v j : ℕ) :
    beta (v + 1) (j + 1) = beta v (j + 1) + beta v j := by
  have hs : series (v + 1) = series v + X * series v := by
    unfold series
    rw [pow_succ]
    ring
  unfold beta
  rw [hs, map_add]
  congr 1
  simpa only [pow_one] using coeff_X_pow_mul (series v) 1 j

lemma beta_pascal_twice (v j : ℕ) :
    beta (v + 2) (j + 2) = beta v (j + 2) + 2 * beta v (j + 1) + beta v j := by
  rw [show v + 2 = v + 1 + 1 by omega, show j + 2 = j + 1 + 1 by omega,
    beta_pascal, beta_pascal, beta_pascal]
  ring

lemma beta_pascal_twice_at (v j : ℕ) :
    beta (v + 2) (j + 1) = beta v (j + 1) + 2 * beta v j +
      (if j = 0 then 0 else beta v (j - 1)) := by
  by_cases hj : j = 0
  · subst j
    norm_num [beta_one, beta_zero]
    ring
  · rw [if_neg hj]
    have h := beta_pascal_twice v (j - 1)
    rwa [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega] at h

lemma choose_step_le {v r : ℕ} (h : 2 * r + 1 ≤ v) : v.choose r ≤ v.choose (r + 1) := by
  have hd : r + 1 ≤ v - r := by omega
  have hm := Nat.mul_le_mul_left (v.choose r) hd
  rw [← Nat.choose_succ_right_eq] at hm
  exact Nat.le_of_mul_le_mul_right hm (by omega)

lemma beta_step_le {v j : ℕ} (h : 2 * j + 1 ≤ v) : beta v j ≤ beta v (j + 1) := by
  rw [beta_formula, beta_formula]
  have hsum : (∑ w ∈ Finset.range (j + 1), (v.choose (j - w) : ℝ) / (w.factorial : ℝ)) ≤
      ∑ w ∈ Finset.range (j + 1), (v.choose (j + 1 - w) : ℝ) / (w.factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro w hw
    have hwj : w ≤ j := by have := Finset.mem_range.mp hw; omega
    have hdiff : j + 1 - w = (j - w) + 1 := by omega
    rw [hdiff]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast choose_step_le (show 2 * (j - w) + 1 ≤ v by omega)
  simpa only [Finset.sum_range_succ] using hsum.trans (le_add_of_nonneg_right (by positivity :
    0 ≤ (v.choose (j + 1 - (j + 1)) : ℝ) / ((j + 1).factorial : ℝ)))

lemma beta_even_rise (d : ℕ) : beta (2 * d) d ≤ beta (2 * d) (d + 1) := by
  cases d with
  | zero => norm_num [beta_zero, beta_one]
  | succ d =>
    have h := beta_recurrence (2 * (d + 1)) d
    have hp := beta_nonneg (2 * (d + 1)) d
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    nlinarith

end
end Lax343628Proofs.SlotProfiles
