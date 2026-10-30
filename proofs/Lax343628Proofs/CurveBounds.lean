import Lax343628Proofs.SlotProfiles

namespace Lax343628Proofs.CurveBounds

open Lax343628Proofs.SlotProfiles
open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma beta_prev_le {v j : ℕ} (hj : 1 ≤ j) (hmode : 2 * j ≤ v + 1) :
    beta v (j - 1) ≤ beta v j := by
  have h := beta_step_le (v := v) (j := j - 1) (by omega)
  simpa only [show j - 1 + 1 = j by omega] using h

lemma beta_even_adjacent (d : ℕ) :
    3 * beta (2 * d) d ≤ beta (2 * (d + 1)) (d + 1) ∧
      2 * beta (2 * (d + 1)) (d + 1) ≤ 9 * beta (2 * d) d := by
  by_cases hd : d = 0
  · subst d
    norm_num [beta_formula, Finset.sum_range_succ]
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hrec := beta_recurrence_at (v := 2 * d) hd1
  have hprev := beta_prev_le (v := 2 * d) hd1 (by omega)
  have hrise := beta_even_rise d
  have hpos := beta_nonneg (2 * d) (d - 1)
  have hsum := beta_pascal_twice (2 * d) (d - 1)
  rw [show 2 * d + 2 = 2 * (d + 1) by omega, show d - 1 + 2 = d + 1 by omega,
    show d - 1 + 1 = d by omega] at hsum
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hrec
  have hdiff : 0 ≤ beta (2 * d) (d + 1) - beta (2 * d) d := sub_nonneg.mpr hrise
  have hscale := mul_nonneg (by linarith : 0 ≤ (d : ℝ) - 1) hdiff
  constructor <;> nlinarith

lemma beta_odd_upper_adjacent (d : ℕ) :
    3 * beta (2 * d + 1) (d + 1) ≤ beta (2 * (d + 1) + 1) (d + 2) ∧
      2 * beta (2 * (d + 1) + 1) (d + 2) ≤ 9 * beta (2 * d + 1) (d + 1) := by
  have hrec := beta_recurrence (2 * d + 1) d
  have hprev := beta_step_le (v := 2 * d + 1) (j := d) (by omega)
  have hpos := beta_nonneg (2 * d + 1) d
  have hcenter : beta (2 * d + 1) (d + 1) ≤ 2 * beta (2 * d + 1) d := by
    by_cases hd : d = 0
    · subst d
      norm_num [beta_zero, beta_one]
    have hd1 : 1 ≤ d := by omega
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hrec0 := beta_recurrence_at (v := 2 * d + 1) hd1
    have hprev0 := beta_prev_le (v := 2 * d + 1) hd1 (by omega)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hrec0
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < d + 1 by positivity)).mp
    nlinarith [mul_nonneg (by linarith : 0 ≤ (d : ℝ) - 1) hpos]
  have hsum := beta_pascal_twice (2 * d + 1) d
  rw [show 2 * d + 1 + 2 = 2 * (d + 1) + 1 by omega] at hsum
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hrec
  have hnext : beta (2 * d + 1) (d + 2) ≤ beta (2 * d + 1) (d + 1) := by
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < d + 2 by positivity)).mp
    nlinarith
  have hlower : beta (2 * d + 1) (d + 1) ≤
      beta (2 * d + 1) (d + 2) + beta (2 * d + 1) d := by
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < d + 2 by positivity)).mp
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hpos]
  constructor <;> nlinarith

lemma beta_odd_lower_adjacent (d : ℕ) :
    3 * beta (2 * d + 1) d ≤ beta (2 * (d + 1) + 1) (d + 1) ∧
      2 * beta (2 * (d + 1) + 1) (d + 1) ≤ 9 * beta (2 * d + 1) d := by
  by_cases hd : d < 3
  · interval_cases d <;> norm_num [beta_formula, Finset.sum_range_succ, Nat.choose]
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
  have hrec := beta_recurrence_at (v := 2 * d + 1) hd1
  have hprev := beta_prev_le (v := 2 * d + 1) hd1 (by omega)
  have hrise := beta_step_le (v := 2 * d + 1) (j := d) (by omega)
  have hpos := beta_nonneg (2 * d + 1) (d - 1)
  have hsum := beta_pascal_twice (2 * d + 1) (d - 1)
  rw [show 2 * d + 1 + 2 = 2 * (d + 1) + 1 by omega, show d - 1 + 2 = d + 1 by omega,
    show d - 1 + 1 = d by omega] at hsum
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hrec
  have hdiff : 0 ≤ beta (2 * d + 1) (d + 1) - beta (2 * d + 1) d := sub_nonneg.mpr hrise
  have hscale := mul_nonneg (by linarith : 0 ≤ (d : ℝ) - 3) hdiff
  constructor <;> nlinarith

def profile (v j : ℕ) : ℝ := (1 / 2 : ℝ) ^ v * beta v j

def q (d : ℕ) : ℝ := profile (2 * d) d
def t (d : ℕ) : ℝ := profile (2 * d + 1) (d + 1)
def tLower (d : ℕ) : ℝ := profile (2 * d + 1) d

lemma profile_pos (v j : ℕ) : 0 < profile v j := mul_pos (by positivity) (beta_pos v j)

lemma profile_le_one (v j : ℕ) : profile v j ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (beta_upper v j)
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ v)
  have hp : (1 / 2 : ℝ) ^ v * (2 : ℝ) ^ v = 1 := by rw [← mul_pow]; norm_num
  exact h.trans_eq hp

lemma profile_even_rise (d : ℕ) : profile (2 * d) d ≤ profile (2 * d) (d + 1) :=
  mul_le_mul_of_nonneg_left (beta_even_rise d) (by positivity)

lemma catalyst_identity (d : ℕ) : t d - q d =
    (1 / 2 : ℝ) * (profile (2 * d) (d + 1) - profile (2 * d) d) := by
  unfold t q profile
  rw [beta_pascal, pow_succ]
  ring

lemma q_adjacent (d : ℕ) : (3 / 4 : ℝ) * q d ≤ q (d + 1) ∧
    q (d + 1) ≤ (9 / 8 : ℝ) * q d := by
  have h := beta_even_adjacent d
  have hpow : (1 / 2 : ℝ) ^ (2 * (d + 1)) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (2 * d) := by
    rw [show 2 * (d + 1) = 2 * d + 2 by omega, pow_add]
    ring
  unfold q profile
  rw [hpow]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * d))]
  · nlinarith [mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * d))]

lemma t_adjacent (d : ℕ) : (3 / 4 : ℝ) * t d ≤ t (d + 1) ∧
    t (d + 1) ≤ (9 / 8 : ℝ) * t d := by
  have h := beta_odd_upper_adjacent d
  have hpow : (1 / 2 : ℝ) ^ (2 * (d + 1) + 1) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (2 * d + 1) := by
    rw [show 2 * (d + 1) + 1 = (2 * d + 1) + 2 by omega, pow_add]
    ring
  unfold t profile
  rw [hpow, show d + 1 + 1 = d + 2 by omega]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * d + 1))]
  · nlinarith [mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * d + 1))]

lemma tLower_adjacent (d : ℕ) : (3 / 4 : ℝ) * tLower d ≤ tLower (d + 1) ∧
    tLower (d + 1) ≤ (9 / 8 : ℝ) * tLower d := by
  have h := beta_odd_lower_adjacent d
  have hpow : (1 / 2 : ℝ) ^ (2 * (d + 1) + 1) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (2 * d + 1) := by
    rw [show 2 * (d + 1) + 1 = (2 * d + 1) + 2 by omega, pow_add]
    ring
  unfold tLower profile
  rw [hpow]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * d + 1))]
  · nlinarith [mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * d + 1))]

lemma profile_adjacent {v j : ℕ} (hv : v = 2 * j ∨ v = 2 * j + 1 ∨ v + 1 = 2 * j) :
    (3 / 4 : ℝ) * profile v j ≤ profile (v + 2) (j + 1) ∧
      profile (v + 2) (j + 1) ≤ (9 / 8 : ℝ) * profile v j := by
  rcases hv with hv | hv | hv
  · subst v
    have h := q_adjacent j
    simpa only [q, show 2 * (j + 1) = 2 * j + 2 by omega] using h
  · subst v
    have h := tLower_adjacent j
    simpa only [tLower, show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega] using h
  · have hj : 1 ≤ j := by omega
    have h := t_adjacent (j - 1)
    have h1 : 2 * (j - 1) + 1 = v := by omega
    have h2 : j - 1 + 1 = j := by omega
    have h3 : 2 * j + 1 = v + 2 := by omega
    have h4 : j - 1 + 1 + 1 = j + 1 := by omega
    simpa only [t, h1, h2, h3, h4] using h

end
end Lax343628Proofs.CurveBounds
