import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

namespace Lax343628Proofs.Weights

open scoped BigOperators

noncomputable section

def coefficient (r l : ℕ) : ℝ :=
  (4 : ℝ)⁻¹ ^ r * (r.choose l : ℝ) *
    ∑ w ∈ Finset.range (l + 1), (r.choose (l - w) : ℝ) / (w.factorial : ℝ)

lemma coefficient_nonneg (r l : ℕ) : 0 ≤ coefficient r l := by
  unfold coefficient
  positivity

lemma coefficient_one (r : ℕ) : coefficient r 1 = (4 : ℝ)⁻¹ ^ r * r * (r + 1) := by
  norm_num [coefficient, Finset.sum_range_succ, Nat.choose_one_right]

lemma coefficient_diagonal_le (r : ℕ) : coefficient r r ≤ (1 / 2 : ℝ) ^ r := by
  have hsum : (∑ w ∈ Finset.range (r + 1), (r.choose (r - w) : ℝ) / (w.factorial : ℝ)) ≤
      (2 : ℝ) ^ r := by
    calc
      (∑ w ∈ Finset.range (r + 1), (r.choose (r - w) : ℝ) / (w.factorial : ℝ)) ≤
          ∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        have hwle : w ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
        rw [Nat.choose_symm hwle]
        exact div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos w)
      _ = (2 : ℝ) ^ r := by exact_mod_cast Nat.sum_range_choose r
  calc
    coefficient r r = (4 : ℝ)⁻¹ ^ r *
        (∑ w ∈ Finset.range (r + 1), (r.choose (r - w) : ℝ) / (w.factorial : ℝ)) := by
      simp [coefficient]
    _ ≤ (4 : ℝ)⁻¹ ^ r * 2 ^ r := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 / 2 : ℝ) ^ r := by rw [← mul_pow]; norm_num

def denominator (r : ℕ) : ℝ := 17 / 16 - 2 * coefficient r r

lemma denominator_lower {r : ℕ} (hr : 2 ≤ r) : (1 / 2 : ℝ) ≤ denominator r := by
  have hc := coefficient_diagonal_le r
  have hp : (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
  norm_num at hp
  unfold denominator
  linarith

lemma denominator_pos {r : ℕ} (hr : 2 ≤ r) : 0 < denominator r :=
  lt_of_lt_of_le (by norm_num) (denominator_lower hr)

lemma denominator_upper (r : ℕ) : denominator r ≤ 17 / 16 := by
  have h := coefficient_nonneg r r
  unfold denominator
  linarith

def weight (r : ℕ) : ℝ :=
  if r = 0 then 0 else if r = 1 then 1 else
    (2 * ∑ l : Fin r, coefficient r l * weight l) / denominator r
termination_by r

@[simp] lemma weight_zero : weight 0 = 0 := by rw [weight]; simp

@[simp] lemma weight_one : weight 1 = 1 := by rw [weight]; simp

lemma weight_rec {r : ℕ} (hr : 2 ≤ r) :
    weight r = (2 * ∑ l : Fin r, coefficient r l * weight l) / denominator r := by
  rw [weight, if_neg (by omega), if_neg (by omega)]

lemma weight_nonneg (r : ℕ) : 0 ≤ weight r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr0 : r = 0
    · simp [hr0]
    by_cases hr1 : r = 1
    · simp [hr1]
    have hr : 2 ≤ r := by omega
    rw [weight_rec hr]
    apply div_nonneg _ (denominator_pos hr).le
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (coefficient_nonneg r l) (ih l l.isLt)

lemma weight_lower {r : ℕ} (hr : 2 ≤ r) :
    (32 / 17 : ℝ) * r * (r + 1) * (4 : ℝ)⁻¹ ^ r ≤ weight r := by
  let one : Fin r := ⟨1, by omega⟩
  have hterm : coefficient r 1 ≤ ∑ l : Fin r, coefficient r l * weight l := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun l : Fin r ↦ coefficient r l * weight l)
      (fun l _ ↦ mul_nonneg (coefficient_nonneg r l) (weight_nonneg l)) (Finset.mem_univ one)
    simpa only [one, weight_one, mul_one] using h
  rw [weight_rec hr]
  apply (le_div_iff₀ (denominator_pos hr)).mpr
  have hden := denominator_upper r
  have hc := coefficient_nonneg r 1
  rw [coefficient_one] at hterm hc
  have hp : 0 ≤ (32 / 17 : ℝ) * r * (r + 1) * (4 : ℝ)⁻¹ ^ r := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hden hp]

lemma weight_two : weight 2 = 6 / 5 := by
  rw [weight_rec (by norm_num : 2 ≤ 2), Fin.sum_univ_two]
  norm_num [denominator, coefficient, Finset.sum_range_succ, weight_zero, weight_one]

lemma copy_le_weight {r : ℕ} (hr : 1 ≤ r) : (4 : ℝ)⁻¹ ^ r ≤ weight r := by
  by_cases hr1 : r = 1
  · norm_num [hr1]
  have hr2 : 2 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hc : (1 : ℝ) ≤ (32 / 17 : ℝ) * r * (r + 1) := by nlinarith
  have h := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (4 : ℝ)⁻¹ ^ r)
  have h' : (4 : ℝ)⁻¹ ^ r ≤ (32 / 17 : ℝ) * r * (r + 1) * (4 : ℝ)⁻¹ ^ r := by
    simpa only [one_mul] using h
  exact h'.trans (weight_lower hr2)

lemma copy_le_small_weight {r : ℕ} (hr : 2 ≤ r) :
    (4 : ℝ)⁻¹ ^ r ≤ (5 / 96 : ℝ) * weight r := by
  by_cases hr2 : r = 2
  · norm_num [hr2, weight_two]
  have hr3 : 3 ≤ r := by omega
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr3
  have hc : (96 / 5 : ℝ) ≤ (32 / 17 : ℝ) * r * (r + 1) := by nlinarith
  have h := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (4 : ℝ)⁻¹ ^ r)
  have hw := weight_lower hr
  nlinarith

lemma uniform_weight_lower {k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    (4 : ℝ)⁻¹ ^ k ≤ weight r :=
  (pow_le_pow_of_le_one (by norm_num) (by norm_num) hrk).trans (copy_le_weight hr)

end
end Lax343628Proofs.Weights
