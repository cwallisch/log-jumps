import Lax343628Proofs.CatalystBounds

namespace Lax343628Proofs.ShadowGaps

open Lax343628Proofs.CurveBounds Lax343628Proofs.CatalystBounds
open Lax343628Proofs.SlotProfiles
noncomputable section
set_option backward.isDefEq.respectTransparency false

def delta (k : ℕ) : ℝ := Real.exp (-1) / (32 * (k : ℝ) ^ 2)

lemma delta_pos {k : ℕ} (hk : 1 ≤ k) : 0 < delta k := by
  unfold delta
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  positivity

lemma delta_le_quarter {k : ℕ} (hk : 1 ≤ k) : delta k ≤ Real.exp (-1) / 4 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold delta
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num)
  nlinarith

lemma gap_uniform {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x : ℝ}
    (hx : 1 / (8 * (j : ℝ) * Real.sqrt j) ≤ x) : delta k ≤ Real.exp (-1) * x / 2 := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjkr : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hs : Real.sqrt (j : ℝ) ≤ j := Real.sqrt_le_self_iff.mpr (Or.inr hjr)
  have hsp : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hd : 8 * (j : ℝ) * Real.sqrt j ≤ 16 * (k : ℝ) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ j)
    nlinarith
  have hsmall : 1 / (16 * (k : ℝ) ^ 2) ≤ 1 / (8 * (j : ℝ) * Real.sqrt j) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
  have ht := mul_le_mul_of_nonneg_left (hsmall.trans hx) (Real.exp_pos (-1)).le
  have hh := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2)
  unfold delta
  convert hh using 1 <;> first | rfl | ring

lemma outside_nonneg {v j : ℕ} (hv : v = 2 * j ∨ v = 2 * j + 1) :
    0 ≤ profile v (j + 1) - profile v j := by
  rcases hv with rfl | rfl
  · exact sub_nonneg.mpr (profile_even_rise j)
  · exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (beta_step_le (v := 2 * j + 1) (j := j) (by omega)) (by positivity))

lemma outside_lower {k v j : ℕ} (hk : 1 ≤ k) (hjk : j ≤ k)
    (hv : v = 2 * j ∨ v = 2 * j + 1) (hgood : 1 ≤ j ∨ v = 2 * j + 1) :
    delta k ≤ Real.exp (-1) * (profile v (j + 1) - profile v j) / 2 := by
  by_cases hj : j = 0
  · subst j
    have hv' : v = 1 := by omega
    subst v
    have hh := delta_le_quarter hk
    norm_num [profile, beta_zero, beta_one] at *
    linarith
  · have hj' : 1 ≤ j := by omega
    rcases hv with rfl | rfl
    · exact gap_uniform hj' hjk (even_gap_lower hj')
    · exact gap_uniform hj' hjk (odd_gap_lower hj')

lemma inside_lower {k v j : ℕ} (hk : 1 ≤ k) (hjk : j ≤ k)
    (hv : v = 2 * j ∨ v + 1 = 2 * j) :
    delta k ≤ Real.exp (-1) *
      (profile v j - if j = 0 then 0 else profile v (j - 1)) / 2 := by
  by_cases hj : j = 0
  · subst j
    have hv' : v = 0 := by omega
    subst v
    have hh := delta_le_quarter hk
    norm_num [profile, beta_zero] at *
    have he := (Real.exp_pos (-1)).le
    linarith
  · rw [if_neg hj]
    have hj' : 1 ≤ j := by omega
    have hpos : (0 : ℝ) < 4 * (j : ℝ) * Real.sqrt j := by
      have hjr : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      positivity
    have hhalf : 1 / (8 * (j : ℝ) * Real.sqrt j) ≤ 1 / (4 * (j : ℝ) * Real.sqrt j) := by
      apply div_le_div_of_nonneg_left (by norm_num) hpos
      linarith
    rcases hv with hv | hv
    · subst v
      exact gap_uniform hj' hjk (hhalf.trans (even_left_gap_lower hj'))
    · have hv' : v = 2 * j - 1 := by omega
      subst v
      exact gap_uniform hj' hjk (hhalf.trans (odd_left_gap_lower hj'))

end
end Lax343628Proofs.ShadowGaps
