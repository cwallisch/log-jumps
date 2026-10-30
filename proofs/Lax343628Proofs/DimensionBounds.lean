import Lax343628Proofs.BlockParameterBounds

namespace Lax343628Proofs.DimensionBounds

open Lax343628Proofs.BlockParameterBounds
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma dimension (S n A : ℝ) (_hS : 1 ≤ S) (hn : 0 < n) (hA : A ≤ 1) (hsize : S ^ 40 ≤ n * A) :
    S ^ 40 ≤ n := by
  exact hsize.trans (by nlinarith)

lemma immigration (S n A : ℝ) (hS : 1 ≤ S) (hn : 0 < n) (hsize : S ^ 40 ≤ n * A) : 1 / n ≤ A := by
  apply (div_le_iff₀ hn).mpr
  have hh : 1 ≤ S ^ 40 := one_le_pow₀ hS
  nlinarith

lemma drift (S n A u D K : ℝ) (hS : 16777216 ≤ S) (hn : 0 < n) (hA : 0 < A)
    (hu : S ^ 40 ≤ u) (hsize : S ^ 40 ≤ n * A) (_hD : 0 ≤ D) (hDS : D ≤ S)
    (hK : 0 ≤ K) (hKS : K ≤ S) :
    S ^ 12 * D / u + S ^ 12 * D * (K + 2) / (n * A) ≤ 1 / 32 := by
  have hS1 : 1 ≤ S := by linarith
  have hSp : 0 < S := by linarith
  have hup : 0 < u := (pow_pos hSp 40).trans_le hu
  have h1 : S ^ 12 * D / u ≤ S ^ 13 / u := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDS (show 0 ≤ S ^ 12 by positivity)) hup.le
    convert hh using 1 <;> rfl
  have h2 : S ^ 12 * D * (K + 2) / (n * A) ≤ 3 * S ^ 14 / (n * A) := by
    have hK2 : K + 2 ≤ 3 * S := by linarith
    have hh := mul_le_mul hDS hK2 (show 0 ≤ K + 2 by linarith) hSp.le
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (show 0 ≤ S ^ 12 by positivity)) (mul_pos hn hA).le
    convert hm using 1 <;> first | rfl | ring
  have hd1 := denominator S u 1 13 40 1 hS1 (by norm_num) hu (by norm_num)
  have hd2 := denominator S (n * A) 3 14 40 1 hS1 (by norm_num) hsize (by norm_num)
  norm_num only [one_mul, pow_one] at hd1 hd2
  have hh : S ^ 12 * D / u + S ^ 12 * D * (K + 2) / (n * A) ≤ 4 / S := by
    linear_combination h1 + h2 + hd1 + hd2
  apply hh.trans
  apply (div_le_iff₀ hSp).mpr
  linarith

lemma bias (S n D K : ℝ) (hS : 16777216 ≤ S) (hn : S ^ 40 ≤ n)
    (_hD : 0 ≤ D) (hDS : D ≤ S) (hK : 0 ≤ K) (hKS : K ≤ S) : D * (K + 1) / n ≤ 1 := by
  have hS1 : 1 ≤ S := by linarith
  have hSp : 0 < S := by linarith
  have hnp : 0 < n := (pow_pos hSp 40).trans_le hn
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul hDS (show K + 1 ≤ 2 * S by linarith) (by linarith : 0 ≤ K + 1) hSp.le) hnp.le
  have h1 : D * (K + 1) / n ≤ 2 * S ^ 2 / n := by
    convert hh using 1 <;> first | rfl | ring
  have h2 := denominator S n 2 2 40 1 hS1 (by norm_num) hn (by norm_num)
  norm_num only [pow_one] at h2
  apply h1.trans (h2.trans _)
  apply (div_le_iff₀ hSp).mpr
  linarith

lemma horizon_error (S n D K t : ℝ) (hS : 16777216 ≤ S) (hn : S ^ 40 ≤ n)
    (hD : 0 ≤ D) (hDS : D ≤ S) (hK : 0 ≤ K) (hKS : K ≤ S)
    (_ht : 0 ≤ t) (htS : t ≤ S ^ 12) : t * (512 * D * K ^ 2 / n) ≤ 1 := by
  have hS1 : 1 ≤ S := by linarith
  have hSp : 0 < S := by linarith
  have hnp : 0 < n := (pow_pos hSp 40).trans_le hn
  have hDK := mul_le_mul hDS (pow_le_pow_left₀ hK hKS 2) (sq_nonneg K) hSp.le
  have hh := mul_le_mul htS hDK (mul_nonneg hD (sq_nonneg K)) (show 0 ≤ S ^ 12 by positivity)
  have h1 : t * (512 * D * K ^ 2 / n) ≤ 512 * S ^ 15 / n := by
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 512 by norm_num)) hnp.le
    convert hm using 1 <;> first | rfl | ring
  have h2 := denominator S n 512 15 40 1 hS1 (by norm_num) hn (by norm_num)
  norm_num only [pow_one] at h2
  apply h1.trans (h2.trans _)
  apply (div_le_iff₀ hSp).mpr
  linarith

lemma shadow_error (S n D K a : ℝ) (hS : 16777216 ≤ S) (hn : S ^ 40 ≤ n)
    (hD : 0 ≤ D) (hDS : D ≤ S) (hK : 0 ≤ K) (hKS : K ≤ S)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : a * (128 * K ^ 2 / n) * D ≤ 1 := by
  have hS1 : 1 ≤ S := by linarith
  have hpow : 1 ≤ S ^ 12 := one_le_pow₀ hS1
  have hh := horizon_error S n D K (a / 4) hS hn hD hDS hK hKS
    (by positivity) (by linarith)
  convert hh using 1; first | rfl | ring

lemma shadow_dimension (S n D K delta omega : ℝ) (hS : 16777216 ≤ S) (hn : S ^ 40 ≤ n)
    (hD : 0 ≤ D) (hDS : D ≤ S) (hK : 0 ≤ K) (hKS : K ≤ S)
    (hdelta : 1 / S ^ 4 ≤ delta) (homega : 1 / S ≤ omega) :
    (128 * K ^ 2 / n) * D * (1 + D) ≤ delta * (omega / 2) / 2 := by
  have hS1 : 1 ≤ S := by linarith
  have hSp : 0 < S := by linarith
  have hnp : 0 < n := (pow_pos hSp 40).trans_le hn
  have hdelta0 : 0 ≤ delta := (by positivity : (0 : ℝ) ≤ 1 / S ^ 4).trans hdelta
  have h1D : 1 + D ≤ 2 * S := by linarith
  have hDK := mul_le_mul hDS h1D (by linarith : 0 ≤ 1 + D) hSp.le
  have hh := mul_le_mul (pow_le_pow_left₀ hK hKS 2) hDK
    (mul_nonneg hD (by linarith : 0 ≤ 1 + D)) (show 0 ≤ S ^ 2 by positivity)
  have h1 : (128 * K ^ 2 / n) * D * (1 + D) ≤ 256 * S ^ 4 / n := by
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 128 by norm_num)) hnp.le
    convert hm using 1 <;> first | rfl | ring
  have h2 := denominator S n 256 4 40 36 hS1 (by norm_num) hn (by norm_num)
  have hS31 : 1024 ≤ S ^ 31 := by
    have hh : S ^ 1 ≤ S ^ 31 := pow_le_pow_right₀ hS1 (by norm_num)
    norm_num only [pow_one] at hh
    linarith
  have h3 : 256 / S ^ 36 ≤ 1 / (4 * S ^ 5) := by
    apply (div_le_div_iff₀ (pow_pos hSp 36) (by positivity : 0 < 4 * S ^ 5)).mpr
    have hm := mul_le_mul_of_nonneg_left hS31 (show 0 ≤ S ^ 5 by positivity)
    have heq : S ^ 36 = S ^ 5 * S ^ 31 := by rw [← pow_add]
    rw [heq]
    nlinarith
  have h4 := mul_le_mul hdelta homega (by positivity : (0 : ℝ) ≤ 1 / S) hdelta0
  have h4' : 1 / (4 * S ^ 5) ≤ delta * (omega / 2) / 2 := by
    have hm := div_le_div_of_nonneg_right h4 (show (0 : ℝ) ≤ 4 by norm_num)
    convert hm using 1 <;> first | rfl | (field_simp <;> ring)
  exact h1.trans (h2.trans (h3.trans h4'))

end
end Lax343628Proofs.DimensionBounds
