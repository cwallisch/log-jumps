import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

namespace Lax343628Proofs.Profiles

open scoped BigOperators

noncomputable section

def central (r : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ r * r.centralBinom

lemma central_pos (r : ℕ) : 0 < central r := by
  unfold central
  have h : (0 : ℝ) < r.centralBinom := by exact_mod_cast Nat.centralBinom_pos r
  positivity

lemma central_recurrence (r : ℕ) :
    ((r : ℝ) + 1) * central (r + 1) = ((r : ℝ) + 1 / 2) * central r := by
  have h : ((r : ℝ) + 1) * ((r + 1).centralBinom : ℝ) =
      2 * (2 * (r : ℝ) + 1) * r.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ r
  unfold central
  rw [pow_succ]
  nlinarith [congrArg (fun x : ℝ ↦ x * (4 : ℝ)⁻¹ ^ r) h]

lemma central_antitone : Antitone central := by
  apply antitone_nat_of_succ_le
  intro r
  have heq := central_recurrence r
  have hp := central_pos r
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith

lemma central_square_lower {r : ℕ} (hr : 1 ≤ r) : (1 / 4 : ℝ) ≤ r * central r ^ 2 := by
  induction r, hr using Nat.le_induction with
  | base => norm_num [central, Nat.centralBinom]
  | succ r hr ih =>
    have heq := central_recurrence r
    have hs := congrArg (fun x : ℝ ↦ x ^ 2) heq
    have hcp := central_pos (r + 1)
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    norm_num only [Nat.cast_add, Nat.cast_one] at *
    nlinarith [sq_nonneg (central r), sq_nonneg (central (r + 1))]

lemma central_lower {r : ℕ} (hr : 1 ≤ r) : (1 : ℝ) / (2 * Real.sqrt r) ≤ central r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hspos := Real.sqrt_pos.mpr hrpos
  have hs := Real.sq_sqrt hrpos.le
  have hcpos := central_pos r
  have hc := central_square_lower hr
  have hprod : (1 / 4 : ℝ) ≤ (Real.sqrt r * central r) ^ 2 := by
    rw [mul_pow, hs]
    exact hc
  have hprodpos : 0 ≤ Real.sqrt r * central r := mul_nonneg hspos.le hcpos.le
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt r)).mpr
  nlinarith

lemma factorial_inverse_sum_le (r : ℕ) :
    (∑ w ∈ Finset.range (r + 1), (1 : ℝ) / (w.factorial : ℝ)) ≤ 3 := by
  have hstrong : (∑ w ∈ Finset.range (r + 1), (1 : ℝ) / (w.factorial : ℝ)) +
      (1 : ℝ) / (r.factorial : ℝ) ≤ 3 := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [Finset.sum_range_succ]
      have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
      by_cases hr : r = 0
      · norm_num [hr]
      · have hrR : (2 : ℝ) ≤ r + 1 := by exact_mod_cast (show 2 ≤ r + 1 by omega)
        have hnext : 2 * ((1 : ℝ) / ((r + 1).factorial : ℝ)) ≤ 1 / (r.factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          apply (le_div_iff₀ hfac).mpr
          field_simp
          nlinarith
        linarith
  have hnonneg : 0 ≤ (1 : ℝ) / (r.factorial : ℝ) := by positivity
  linarith

def viability (r : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ r *
  ∑ w ∈ Finset.range (r + 1), ((2 * r).choose (r - w) : ℝ) / (w.factorial : ℝ)

lemma viability_upper (r : ℕ) : viability r ≤ 3 * central r := by
  have hsum : (∑ w ∈ Finset.range (r + 1),
      ((2 * r).choose (r - w) : ℝ) / (w.factorial : ℝ)) ≤
      (r.centralBinom : ℝ) * 3 := by
    calc
      _ ≤ ∑ w ∈ Finset.range (r + 1), (r.centralBinom : ℝ) / (w.factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro w _
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_centralBinom (r - w) r)
          (by positivity)
      _ = (r.centralBinom : ℝ) *
          (∑ w ∈ Finset.range (r + 1), (1 : ℝ) / (w.factorial : ℝ)) := by
        rw [Finset.mul_sum]
        simp only [mul_one_div]
      _ ≤ (r.centralBinom : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left (factorial_inverse_sum_le r) (by positivity)
  unfold viability central
  nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (4 : ℝ)⁻¹ ^ r)]

lemma viability_lower {r : ℕ} (hr : 1 ≤ r) :
    (1 : ℝ) / (2 * Real.sqrt r) ≤ viability r := by
  have hterm : (r.centralBinom : ℝ) ≤ ∑ w ∈ Finset.range (r + 1),
      ((2 * r).choose (r - w) : ℝ) / (w.factorial : ℝ) := by
    have h := Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun w ↦ ((2 * r).choose (r - w) : ℝ) / (w.factorial : ℝ))
      (fun w _ ↦ by positivity) (Finset.mem_range.mpr (Nat.succ_pos r))
    simpa only [Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, div_one, Nat.centralBinom] using h
  exact (central_lower hr).trans (mul_le_mul_of_nonneg_left hterm (by positivity))

lemma viability_zero : viability 0 = 1 := by
  norm_num [viability, Finset.sum_range_succ]

lemma viability_uniform_lower {k r : ℕ} (hk : 1 ≤ k) (hr : r ≤ k) :
    (1 : ℝ) / (2 * Real.sqrt k) ≤ viability r := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqrt : (1 : ℝ) ≤ Real.sqrt k := by simpa using Real.sqrt_le_sqrt hkR
  have hpos : (0 : ℝ) < Real.sqrt k := by linarith
  by_cases hr0 : r = 0
  · rw [hr0, viability_zero]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * Real.sqrt k)).mpr
    linarith
  · have hr1 : 1 ≤ r := by omega
    have hs : Real.sqrt r ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast hr)
    have hpr : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr (by exact_mod_cast hr1)
    exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * Real.sqrt r)
      (by linarith)).trans (viability_lower hr1)

lemma viability_le_seventeen {r : ℕ} (hr : 6 ≤ r) : viability r ≤ 17 / 32 := by
  by_cases hr10 : r < 10
  · interval_cases r <;>
      norm_num [viability, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  · have h := (viability_upper r).trans
      (mul_le_mul_of_nonneg_left (central_antitone (show 10 ≤ r by omega)) (by norm_num :
        (0 : ℝ) ≤ 3))
    norm_num [central, Nat.centralBinom, Nat.choose] at h
    linarith

end
end Lax343628Proofs.Profiles
