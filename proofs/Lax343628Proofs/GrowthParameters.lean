import Lax343628Proofs.DimensionBounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Lax343628Proofs.GrowthParameters

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma exp_lower : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
  have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (Real.exp_pos 1) (show Real.exp 1 ≤ 4 by linarith [Real.exp_one_lt_three])
  simpa only [one_div, Real.exp_neg] using hh

lemma delta_lower (S : ℝ) (hS : 16777216 ≤ S) (k : ℕ) (hk : 1 ≤ k) (hkS : (k : ℝ) ≤ S) :
    1 / S ^ 4 ≤ ShadowGaps.delta k := by
  have hSp : 0 < S := by linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (k : ℝ) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by positivity) hkS 2
  have hS2 : (128 : ℝ) ≤ S ^ 2 := by nlinarith
  have hden : 128 * (k : ℝ) ^ 2 ≤ S ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hS2 (sq_nonneg S)
    nlinarith
  have h1 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℝ) < 128 * (k : ℝ) ^ 2 by positivity) hden
  have h2 := div_le_div_of_nonneg_right exp_lower (show (0 : ℝ) ≤ 32 * (k : ℝ) ^ 2 by positivity)
  apply h1.trans
  unfold ShadowGaps.delta
  convert h2 using 1; first | rfl | (field_simp; ring)

lemma log_lower (k : ℕ) (hk : 1 ≤ k) (a omega : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : 0 ≤ omega ∧ omega ≤ 1) :
    a * ShadowGaps.delta k * omega / (16 * (3 : ℝ) ^ k) ≤ Real.log (SparseGrowth.base k a omega) := by
  have hD : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hd := (ShadowGaps.delta_pos hk).le
  have hdu := ShadowGaps.delta_le_quarter hk
  have hexp : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have heps : 0 ≤ ShadowGaps.delta k * (omega / 2) :=
    mul_nonneg hd (div_nonneg hw.1 (by norm_num))
  have heps1 : ShadowGaps.delta k * (omega / 2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hw.2 hd
    nlinarith
  have hsmall : a * (ShadowGaps.delta k * (omega / 2)) / (2 * (1 + a) * (3 : ℝ) ^ k) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + a) * (3 : ℝ) ^ k)).mpr
    have hh := mul_le_mul_of_nonneg_left heps1 ha
    nlinarith [mul_nonneg (show 0 ≤ 1 + a by linarith) (sub_nonneg.mpr hD)]
  have hh := ColumnExit.log_base_lower ha ha1 heps (show 0 < (3 : ℝ) ^ k by positivity) hsmall
  unfold SparseGrowth.base
  convert hh using 1; first | rfl | ring

lemma growth (S R a pc omega : ℝ) (k : ℕ) (hS : 16777216 ≤ S) (hk : 1 ≤ k)
    (hkS : (k : ℝ) ≤ S) (hDS : (3 : ℝ) ^ k ≤ S)
    (hR : 0 ≤ R) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hpc : 1 / S ≤ pc) (hw : 1 / S ≤ omega) (hw1 : omega ≤ 1)
    (hRa : R * a = pc * S ^ 10) :
    Real.log (8 * (3 : ℝ) ^ k) + 1 ≤ R * Real.log (SparseGrowth.base k a omega) := by
  have hSp : 0 < S := by linarith
  have hwp : 0 < omega := (div_pos (by norm_num) hSp).trans_le hw
  have hd := delta_lower S hS k hk hkS
  have hd0 : 0 ≤ ShadowGaps.delta k := (ShadowGaps.delta_pos hk).le
  have hprod := mul_le_mul hd hw (by positivity : (0 : ℝ) ≤ 1 / S) hd0
  have hpc10 := mul_le_mul_of_nonneg_right hpc (show 0 ≤ S ^ 10 by positivity)
  have hnum := mul_le_mul hpc10 hprod (by positivity : (0 : ℝ) ≤ 1 / S ^ 4 * (1 / S))
    (show 0 ≤ pc * S ^ 10 by have hpc0 : 0 ≤ pc := (by positivity : (0 : ℝ) ≤ 1 / S).trans hpc; positivity)
  have hnum' : S ^ 4 ≤ pc * S ^ 10 * (ShadowGaps.delta k * omega) := by
    convert hnum using 1 <;> first | rfl | field_simp
  have hdiv := div_le_div_of_nonneg_left (show 0 ≤ S ^ 4 by positivity)
    (show 0 < 16 * (3 : ℝ) ^ k by positivity) (mul_le_mul_of_nonneg_left hDS (show (0 : ℝ) ≤ 16 by norm_num))
  have hdiv2 := div_le_div_of_nonneg_right hnum' (show 0 ≤ 16 * (3 : ℝ) ^ k by positivity)
  have hl := mul_le_mul_of_nonneg_left (log_lower k hk a omega ha ha1 ⟨hwp.le, hw1⟩) hR
  have hgrowth : S ^ 3 / 16 ≤ R * Real.log (SparseGrowth.base k a omega) := by
    have hh := hdiv.trans (hdiv2.trans (show pc * S ^ 10 * (ShadowGaps.delta k * omega) / (16 * (3 : ℝ) ^ k) ≤
        R * Real.log (SparseGrowth.base k a omega) by
      rw [← hRa]
      convert hl using 1 <;> first | rfl | ring))
    convert hh using 1 <;> first | rfl | field_simp
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 8 * (3 : ℝ) ^ k by positivity)
  have hS2 : (128 : ℝ) ≤ S ^ 2 := by nlinarith
  have h8 : 8 * S ≤ S ^ 3 / 16 := by
    have hh := mul_le_mul_of_nonneg_left hS2 hSp.le
    nlinarith
  have hh : Real.log (8 * (3 : ℝ) ^ k) + 1 ≤ 8 * S := by linarith
  exact hh.trans (h8.trans hgrowth)

end
end Lax343628Proofs.GrowthParameters
