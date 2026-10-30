import Lax343628Proofs.PhaseScale

namespace Lax343628Proofs.ScaleProducts

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma multiply_inverse (s W : ℝ) (hs : 0 < s) (p g : ℕ) :
    s ^ (p + g) * W * (1 / s ^ p) = s ^ g * W := by
  rw [pow_add]
  field_simp

lemma mass (s W x y : ℝ) (hs : 1 ≤ s) (hW : 1 ≤ W) (hx : s ^ 300 * W ≤ x)
    (hy : 1 / s ^ 11 ≤ y) : s ^ 248 * W ≤ x * y := by
  have hsp : 0 < s := by linarith
  have hWp : 0 ≤ W := by linarith
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ s ^ 300 * W).trans hx
  have hh := mul_le_mul hx hy (by positivity : (0 : ℝ) ≤ 1 / s ^ 11) hx0
  have heq := multiply_inverse s W hsp 11 289
  rw [heq] at hh
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs (by norm_num : 248 ≤ 289)) hWp
  exact hp.trans hh

lemma dimension (s W x y : ℝ) (hs : 1 ≤ s) (hW : 1 ≤ W) (hx : s ^ 300 * W ≤ x)
    (hy : 1 / s ^ 11 ≤ y) : s ^ 40 ≤ x * y := by
  have hh := mass s W x y hs hW hx hy
  have hp : s ^ 40 ≤ s ^ 248 := pow_le_pow_right₀ hs (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hW (show 0 ≤ s ^ 248 by positivity)
  apply le_trans _ hh
  nlinarith

lemma twice_mass (s W x : ℝ) (hs : 16777216 ≤ s) (hW : 1 ≤ W) (hx : s ^ 300 * W ≤ x) :
    2 * (s ^ 248 * W) ≤ x := by
  have hs1 : 1 ≤ s := by linarith
  have hp : s ^ 1 ≤ s ^ 52 := pow_le_pow_right₀ hs1 (by norm_num)
  norm_num only [pow_one] at hp
  have hp2 : (2 : ℝ) ≤ s ^ 52 := by linarith
  have hWp : 0 ≤ W := by linarith
  have hh := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ s ^ 248 * W by positivity)
  have heq : s ^ 248 * W * s ^ 52 = s ^ 300 * W := by
    calc
      _ = (s ^ 248 * s ^ 52) * W := by ac_rfl
      _ = _ := by rw [← pow_add]
  rw [heq] at hh
  have hh' : 2 * (s ^ 248 * W) ≤ s ^ 300 * W := by simpa only [mul_comm] using hh
  exact hh'.trans hx

lemma divide_nine (s u : ℝ) (hs : 16777216 ≤ s) (hu : 1 / s ^ 10 ≤ u) : 1 / s ^ 11 ≤ u / 9 := by
  have hsp : 0 < s := by linarith
  have hden : 9 * s ^ 10 ≤ s ^ 11 := by
    have hh := mul_le_mul_of_nonneg_right (show (9 : ℝ) ≤ s by linarith) (show 0 ≤ s ^ 10 by positivity)
    nlinarith
  have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (show 0 < 9 * s ^ 10 by positivity) hden
  have hu9 := div_le_div_of_nonneg_right hu (show (0 : ℝ) ≤ 9 by norm_num)
  have heq : 1 / (9 * s ^ 10) = (1 / s ^ 10) / 9 := by ring
  rw [heq] at hd
  exact hd.trans hu9

end
end Lax343628Proofs.ScaleProducts
