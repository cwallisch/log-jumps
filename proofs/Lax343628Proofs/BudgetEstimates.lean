import Lax343628Proofs.ColumnBudget

namespace Lax343628Proofs.BudgetEstimates

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma physical_bias (S n A : ℝ) (hS : 0 ≤ S) (hn : 0 < n) (hA : 0 < A) (hA1 : A ≤ 1) :
    (S + 1 / A) / n ≤ (S + 1) / (n * A) := by
  apply (div_le_div_iff₀ hn (mul_pos hn hA)).mpr
  have hs := mul_le_mul_of_nonneg_left hA1 hS
  field_simp at *
  nlinarith

lemma time_ratio (T u H : ℝ) (hT : T ≤ u * H) (hu : 0 < u) (hH : 0 ≤ H) :
    T / (u + 1) ≤ H := by
  apply (div_le_iff₀ (by linarith : 0 < u + 1)).mpr
  nlinarith

lemma drift (T u H a D S n A : ℝ) (_hT : 0 ≤ T) (hTime : T ≤ u * H)
    (hu : 0 < u) (hH : 0 ≤ H) (ha : 0 ≤ a) (ha1 : a ≤ 1 / u)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hn : 0 < n) (hA : 0 < A) (hA1 : A ≤ 1) :
    T * ((a * D + D * (S + 1 / A) / n) / (u + 1)) ≤
      H * D / u + H * D * (S + 1) / (n * A) := by
  have ht := time_ratio T u H hTime hu hH
  have hn0 : 0 ≤ a * D + D * (S + 1 / A) / n := by positivity
  have h1 := mul_le_mul_of_nonneg_right ht hn0
  have h2 := mul_le_mul_of_nonneg_left ha1 hD
  have h3 := mul_le_mul_of_nonneg_left (physical_bias S n A hS hn hA hA1) hD
  have h4 : a * D + D * (S + 1 / A) / n ≤ D / u + D * (S + 1) / (n * A) := by
    have h2' : a * D ≤ D / u := by convert h2 using 1 <;> first | rfl | ring
    have h3' : D * (S + 1 / A) / n ≤ D * (S + 1) / (n * A) := by
      convert h3 using 1 <;> first | rfl | ring
    exact add_le_add h2' h3'
  have hh := h1.trans (mul_le_mul_of_nonneg_left h4 hH)
  convert hh using 1 <;> first | rfl | ring

lemma mismatch (mu ell : ℕ) (a D zeta : ℝ) (hmu : 0 < (mu : ℝ))
    (ha : a ≤ 1 / (mu : ℝ)) (hD : 1 ≤ D) (hzeta : (ell : ℝ) / mu ≤ zeta) :
    MismatchTotals.cost mu ell a D ≤ 5 * zeta * D ^ 2 := by
  have hD0 : 0 ≤ D := by linarith
  have hD2 : D ≤ D ^ 2 := by nlinarith
  have hz0 : 0 ≤ zeta := (div_nonneg (Nat.cast_nonneg _) hmu.le).trans hzeta
  have he := mul_le_mul_of_nonneg_left ha (show (0 : ℝ) ≤ ell by positivity)
  have he' : (ell : ℝ) * a ≤ zeta := by
    have hh : (ell : ℝ) * (1 / mu) = (ell : ℝ) / mu := by ring
    rw [hh] at he
    exact he.trans hzeta
  have h1 := mul_le_mul_of_nonneg_right hzeta hD0
  have h2 := mul_le_mul_of_nonneg_right he' hD0
  have h3 := mul_le_mul_of_nonneg_right he' (sq_nonneg D)
  have h4 := mul_le_mul_of_nonneg_left hD2 hz0
  unfold MismatchTotals.cost
  nlinarith

lemma square_rate (T u H b C : ℝ) (_hT : 0 ≤ T) (hTime : T ≤ u * H)
    (hu : 0 < u) (hH : 0 ≤ H) (hb : 0 ≤ b) (hC : 0 ≤ C) (hbound : b ≤ C / u) :
    T * b ^ 2 ≤ H * C ^ 2 / u := by
  have hs := (sq_le_sq₀ hb (div_nonneg hC hu.le)).mpr hbound
  have hh := mul_le_mul hTime hs (sq_nonneg b) (mul_nonneg hu.le hH)
  have heq : u * H * (C / u) ^ 2 = H * C ^ 2 / u := by field_simp
  rwa [heq] at hh

lemma square_sum (T R u H a D f F Q L : ℝ) (hT : 0 ≤ T) (hTR : T ≤ R)
    (hR : R ≤ u * H) (hu : 0 < u) (hH : 0 ≤ H)
    (ha : 0 ≤ a) (ha1 : a ≤ 1 / u) (hD : 1 ≤ D) (hf : 0 < f)
    (hF : 0 ≤ F) (_hQ : 0 ≤ Q) (hFQ : F ≤ Q * f) :
    3 * (T * (2 / (u + 1)) ^ 2 + T * (a * D) ^ 2 +
      2 * (D / (u * f)) ^ 2 * (6 * R * F + 2 * L) +
      18 * T * (D / u) ^ 2) ≤
      69 * H * D ^ 2 / u + 36 * H * D ^ 2 * Q / (u * f) + 12 * D ^ 2 * L / (u * f) ^ 2 := by
  have hD0 : 0 ≤ D := by linarith
  have hTime := hTR.trans hR
  have hfirst := square_rate T u H (2 / (u + 1)) 2 hT hTime hu hH (by positivity) (by norm_num)
    (div_le_div_of_nonneg_left (by norm_num) hu (by linarith))
  have hsecond := square_rate T u H (a * D) D hT hTime hu hH (mul_nonneg ha hD0) hD0
    (by
      have hh := mul_le_mul_of_nonneg_right ha1 hD0
      convert hh using 1 <;> first | rfl | ring)
  have hthird := square_rate T u H (D / u) D hT hTime hu hH (div_nonneg hD0 hu.le) hD0 le_rfl
  have hRF : R * F ≤ u * H * (Q * f) :=
    mul_le_mul hR hFQ hF (mul_nonneg hu.le hH)
  have hc := mul_le_mul_of_nonneg_left
    (show 6 * R * F + 2 * L ≤ 6 * (u * H * (Q * f)) + 2 * L by linarith)
    (show 0 ≤ 2 * (D / (u * f)) ^ 2 by positivity)
  have heq : 2 * (D / (u * f)) ^ 2 * (6 * (u * H * (Q * f)) + 2 * L) =
      12 * H * D ^ 2 * Q / (u * f) + 4 * D ^ 2 * L / (u * f) ^ 2 := by
    field_simp; ring
  rw [heq] at hc
  have hlarge : 12 * H / u ≤ 12 * H * D ^ 2 / u := by
    apply div_le_div_of_nonneg_right _ hu.le
    have hD2 : 1 ≤ D ^ 2 := by nlinarith
    nlinarith [mul_nonneg hH (sub_nonneg.mpr hD2)]
  linear_combination 3 * hfirst + 3 * hsecond + 54 * hthird + 3 * hc + hlarge

lemma mass_square (u H D f Q L M : ℝ) (hM : 1 ≤ M) (hmu : M ≤ u) (hmf : M ≤ u * f)
    (hH : 1 ≤ H) (_hD : 0 ≤ D) (hQ : 1 ≤ Q) (hL : 1 ≤ L) :
    69 * H * D ^ 2 / u + 36 * H * D ^ 2 * Q / (u * f) + 12 * D ^ 2 * L / (u * f) ^ 2 ≤
      117 * H * D ^ 2 * Q * L / M := by
  have hMp : 0 < M := by linarith
  have hup : 0 < u := hMp.trans_le hmu
  have hufp : 0 < u * f := hMp.trans_le hmf
  have hHp : 0 ≤ H := by linarith
  have hQp : 0 ≤ Q := by linarith
  have hLp : 0 ≤ L := by linarith
  have hHQ : (1 : ℝ) ≤ H * Q := by
    simpa only [one_mul] using mul_le_mul hH hQ (by norm_num : (0 : ℝ) ≤ 1) hHp
  have hQL : (1 : ℝ) ≤ Q * L := by
    simpa only [one_mul] using mul_le_mul hQ hL (by norm_num : (0 : ℝ) ≤ 1) hQp
  have h1a := div_le_div_of_nonneg_left (show 0 ≤ 69 * H * D ^ 2 by positivity) hMp hmu
  have h1b := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hQL (show 0 ≤ 69 * H * D ^ 2 by positivity)) hMp.le
  have h1 : 69 * H * D ^ 2 / u ≤ 69 * H * D ^ 2 * Q * L / M := by
    apply h1a.trans
    convert h1b using 1 <;> first | rfl | ring
  have h2a := div_le_div_of_nonneg_left (show 0 ≤ 36 * H * D ^ 2 * Q by positivity) hMp hmf
  have h2b := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hL (show 0 ≤ 36 * H * D ^ 2 * Q by positivity)) hMp.le
  have h2 : 36 * H * D ^ 2 * Q / (u * f) ≤ 36 * H * D ^ 2 * Q * L / M := by
    apply h2a.trans
    simpa only [mul_one] using h2b
  have hsquare : M ≤ (u * f) ^ 2 := by
    have hh : 1 ≤ u * f := hM.trans hmf
    nlinarith [sq_nonneg (u * f - 1)]
  have h3a := div_le_div_of_nonneg_left (show 0 ≤ 12 * D ^ 2 * L by positivity) hMp hsquare
  have h3b := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hHQ (show 0 ≤ 12 * D ^ 2 * L by positivity)) hMp.le
  have h3 : 12 * D ^ 2 * L / (u * f) ^ 2 ≤ 12 * H * D ^ 2 * Q * L / M := by
    apply h3a.trans
    convert h3b using 1 <;> first | rfl | ring
  linear_combination h1 + h2 + h3

end
end Lax343628Proofs.BudgetEstimates
