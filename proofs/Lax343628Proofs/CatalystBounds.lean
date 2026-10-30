import Lax343628Proofs.CurveBounds

namespace Lax343628Proofs.CatalystBounds

open Lax343628Proofs.SlotProfiles Lax343628Proofs.CurveBounds
open Lax343628Proofs.Profiles
open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma half_central (d : ℕ) :
    (1 / 2 : ℝ) ^ (2 * d) * ((2 * d).choose d : ℝ) = central d := by
  unfold central Nat.centralBinom
  rw [pow_mul]
  norm_num

lemma beta_even_difference {d : ℕ} (hd : 1 ≤ d) :
    ((d : ℝ) + 1) * (beta (2 * d) (d + 1) - beta (2 * d) d) = beta (2 * d) (d - 1) := by
  have h := beta_recurrence_at (v := 2 * d) hd
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

lemma profile_even_difference {d : ℕ} (hd : 1 ≤ d) :
    ((d : ℝ) + 1) * (profile (2 * d) (d + 1) - profile (2 * d) d) =
      (1 / 2 : ℝ) ^ (2 * d) * beta (2 * d) (d - 1) := by
  have h := congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) ^ (2 * d) * z) (beta_even_difference hd)
  unfold profile
  nlinarith

lemma adjacent_binomial (d : ℕ) (hd : 1 ≤ d) :
    ((2 * d).choose (d - 1) : ℝ) * ((d : ℝ) + 1) =
      ((2 * d).choose d : ℝ) * d := by
  have h := congrArg (fun a : ℕ ↦ (a : ℝ)) (Nat.choose_succ_right_eq (2 * d) (d - 1))
  rw [show d - 1 + 1 = d by omega, show 2 * d - (d - 1) = d + 1 by omega] at h
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  exact h.symm

lemma even_gap_central {d : ℕ} (hd : 1 ≤ d) :
    central d * d / ((d : ℝ) + 1) ^ 2 ≤ profile (2 * d) (d + 1) - profile (2 * d) d := by
  have hchoose := adjacent_binomial d hd
  have hcoef := congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) ^ (2 * d) * z) hchoose
  have hbeta := mul_le_mul_of_nonneg_left (beta_binomial_lower (2 * d) (d - 1))
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * d))
  have hdiff := profile_even_difference hd
  have hscaled := mul_le_mul_of_nonneg_left hbeta (show (0 : ℝ) ≤ d + 1 by positivity)
  have hdiffscaled := congrArg (fun z : ℝ ↦ ((d : ℝ) + 1) * z) hdiff
  have hcentral := half_central d
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) + 1) ^ 2)).mpr
  nlinarith

lemma even_gap_lower {d : ℕ} (hd : 1 ≤ d) :
    1 / (8 * (d : ℝ) * Real.sqrt d) ≤ profile (2 * d) (d + 1) - profile (2 * d) d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hfactor : 1 / (4 * (d : ℝ)) ≤ (d : ℝ) / ((d : ℝ) + 1) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  calc
    1 / (8 * (d : ℝ) * Real.sqrt d) = (1 / (2 * Real.sqrt d)) * (1 / (4 * d)) := by ring
    _ ≤ central d * (1 / (4 * d)) :=
      mul_le_mul_of_nonneg_right (central_lower hd) (by positivity)
    _ ≤ central d * ((d : ℝ) / ((d : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hfactor (central_pos d).le
    _ = central d * d / ((d : ℝ) + 1) ^ 2 := by ring
    _ ≤ _ := even_gap_central hd

lemma catalyst_polynomial {d : ℕ} (hd : 1 ≤ d) :
    1 / (16 * (d : ℝ) * Real.sqrt d) ≤ t d - q d := by
  rw [catalyst_identity]
  have h := mul_le_mul_of_nonneg_left (even_gap_lower hd) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert h using 1 <;> first | rfl | ring

lemma beta_rise_by_mass {v j : ℕ} (hv : 2 * j + 1 ≤ v) :
    beta v j ≤ ((j : ℝ) + 1) * (beta v (j + 1) - beta v j) := by
  by_cases hj : j = 0
  · subst j
    rw [beta_zero, beta_one]
    have hR : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
    nlinarith
  have hrec := beta_recurrence_at (v := v) (by omega : 1 ≤ j)
  have hprev := beta_nonneg v (j - 1)
  have hR : (2 : ℝ) * j + 1 ≤ v := by exact_mod_cast hv
  nlinarith [mul_nonneg (by linarith : 0 ≤ (v : ℝ) - 2 * j - 1) (beta_nonneg v j)]

lemma profile_rise_by_mass {v j : ℕ} (hv : 2 * j + 1 ≤ v) :
    profile v j / ((j : ℝ) + 1) ≤ profile v (j + 1) - profile v j := by
  apply (div_le_iff₀ (show (0 : ℝ) < j + 1 by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left (beta_rise_by_mass hv)
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ v)
  unfold profile
  nlinarith

lemma profile_odd_central_lower (d : ℕ) : central d / 2 ≤ profile (2 * d + 1) d := by
  have hchoose : ((2 * d).choose d : ℝ) ≤ (2 * d + 1).choose d := by
    exact_mod_cast Nat.choose_le_succ (2 * d) d
  have hm := mul_le_mul_of_nonneg_left hchoose
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * d + 1))
  have hb := mul_le_mul_of_nonneg_left (beta_binomial_lower (2 * d + 1) d)
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * d + 1))
  have hc := half_central d
  rw [pow_succ] at hm hb
  unfold profile
  rw [pow_succ]
  nlinarith

lemma profile_even_left_central_lower {d : ℕ} (hd : 1 ≤ d) :
    central d / 2 ≤ profile (2 * d) (d - 1) := by
  have hchoose := adjacent_binomial d hd
  have hR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcoef := congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) ^ (2 * d) * z) hchoose
  have hb := mul_le_mul_of_nonneg_left (beta_binomial_lower (2 * d) (d - 1))
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * d))
  have hc := half_central d
  have hcentral := central_pos d
  have hsmall : central d ≤ 2 * ((1 / 2 : ℝ) ^ (2 * d) * ((2 * d).choose (d - 1) : ℝ)) := by
    have hden : (0 : ℝ) < d + 1 := by positivity
    apply (mul_le_mul_iff_left₀ hden).mp
    nlinarith [mul_nonneg (by linarith : 0 ≤ (d : ℝ) - 1) hcentral.le]
  unfold profile
  nlinarith

lemma odd_gap_lower {d : ℕ} (hd : 1 ≤ d) :
    1 / (8 * (d : ℝ) * Real.sqrt d) ≤ profile (2 * d + 1) (d + 1) - profile (2 * d + 1) d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hbase : 1 / (4 * Real.sqrt (d : ℝ)) ≤ profile (2 * d + 1) d := by
    calc
      _ = (1 / (2 * Real.sqrt d)) / 2 := by ring
      _ ≤ central d / 2 := div_le_div_of_nonneg_right (central_lower hd) (by norm_num)
      _ ≤ _ := profile_odd_central_lower d
  calc
    1 / (8 * (d : ℝ) * Real.sqrt d) = (1 / (4 * Real.sqrt d)) / (2 * d) := by ring
    _ ≤ profile (2 * d + 1) d / (2 * d) := div_le_div_of_nonneg_right hbase (by positivity)
    _ ≤ profile (2 * d + 1) d / ((d : ℝ) + 1) :=
      div_le_div_of_nonneg_left (profile_pos _ _).le (by positivity) (by linarith)
    _ ≤ _ := profile_rise_by_mass (by omega)

lemma even_left_gap_lower {d : ℕ} (hd : 1 ≤ d) :
    1 / (4 * (d : ℝ) * Real.sqrt d) ≤ profile (2 * d) d - profile (2 * d) (d - 1) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hbase : 1 / (4 * Real.sqrt (d : ℝ)) ≤ profile (2 * d) (d - 1) := by
    calc
      _ = (1 / (2 * Real.sqrt d)) / 2 := by ring
      _ ≤ central d / 2 := div_le_div_of_nonneg_right (central_lower hd) (by norm_num)
      _ ≤ _ := profile_even_left_central_lower hd
  have hstep := profile_rise_by_mass (v := 2 * d) (j := d - 1) (by omega)
  rw [show d - 1 + 1 = d by omega] at hstep
  have hcast : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast (show d - 1 + 1 = d by omega)
  rw [hcast] at hstep
  have hm := div_le_div_of_nonneg_right hbase hdpos.le
  exact (show 1 / (4 * (d : ℝ) * Real.sqrt d) ≤ profile (2 * d) (d - 1) / d by
    convert hm using 1 <;> first | rfl | ring).trans hstep

lemma odd_left_gap_lower {d : ℕ} (hd : 1 ≤ d) :
    1 / (4 * (d : ℝ) * Real.sqrt d) ≤ profile (2 * d - 1) d - profile (2 * d - 1) (d - 1) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hbase : 1 / (4 * Real.sqrt (d : ℝ)) ≤ profile (2 * d - 1) (d - 1) := by
    have hodd := profile_odd_central_lower (d - 1)
    rw [show 2 * (d - 1) + 1 = 2 * d - 1 by omega] at hodd
    have hmon := central_antitone (show d - 1 ≤ d by omega)
    calc
      _ = (1 / (2 * Real.sqrt d)) / 2 := by ring
      _ ≤ central d / 2 := div_le_div_of_nonneg_right (central_lower hd) (by norm_num)
      _ ≤ central (d - 1) / 2 := div_le_div_of_nonneg_right hmon (by norm_num)
      _ ≤ _ := hodd
  have hstep := profile_rise_by_mass (v := 2 * d - 1) (j := d - 1) (by omega)
  rw [show d - 1 + 1 = d by omega] at hstep
  have hcast : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast (show d - 1 + 1 = d by omega)
  rw [hcast] at hstep
  have hm := div_le_div_of_nonneg_right hbase hdpos.le
  exact (show 1 / (4 * (d : ℝ) * Real.sqrt d) ≤ profile (2 * d - 1) (d - 1) / d by
    convert hm using 1 <;> first | rfl | ring).trans hstep

end
end Lax343628Proofs.CatalystBounds
