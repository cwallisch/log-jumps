import Lax343628Proofs.SparseGrowth

namespace Lax343628Proofs.ColumnExit

noncomputable section

lemma log_four_gt : (1 / 4 : ℝ) < Real.log 4 := by
  have hh := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)
  norm_num only [show (1 : ℝ) + 3 = 4 by norm_num, show (3 : ℝ) + 2 = 5 by norm_num] at hh
  linarith

lemma prevents_lower {O0 Oend D lambda : ℝ} (hO0 : 0 < O0) (hOend : 0 < Oend)
    (hD : 0 < D) (hlambda : 1 ≤ lambda) (T : ℕ)
    (hgrowth : Real.log O0 + T * Real.log lambda - Real.log D - 1 / 4 ≤ Real.log Oend) :
    O0 / (4 * D) < Oend := by
  by_contra hn
  have hlow : Oend ≤ O0 / (4 * D) := le_of_not_gt hn
  have hl := Real.log_le_log hOend hlow
  rw [Real.log_div hO0.ne' (mul_pos (by norm_num : (0 : ℝ) < 4) hD).ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hD.ne'] at hl
  have hnon := mul_nonneg (Nat.cast_nonneg T) (Real.log_nonneg hlambda)
  linarith [log_four_gt]

lemma upper_at_horizon {O0 Oend D B lambda : ℝ} (hO0 : 0 < O0) (hOend : 0 < Oend)
    (hD : 0 < D) (hB : 0 < B) (T : ℕ)
    (htime : Real.log (B * D) + 1 ≤ T * Real.log lambda)
    (hgrowth : Real.log O0 + T * Real.log lambda - Real.log D - 1 / 4 ≤ Real.log Oend) :
    B * O0 < Oend := by
  have hlog : Real.log (B * O0) < Real.log Oend := by
    rw [Real.log_mul hB.ne' hO0.ne']
    rw [Real.log_mul hB.ne' hD.ne'] at htime
    linarith
  exact (Real.log_lt_log_iff (mul_pos hB hO0) hOend).mp hlog

lemma log_base_lower {a eps D : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (heps : 0 ≤ eps) (hD : 0 < D)
    (hsmall : a * eps / (2 * (1 + a) * D) ≤ 1) :
    a * eps / (8 * D) ≤ Real.log (1 + a * eps / (2 * (1 + a) * D)) := by
  let u := a * eps / (2 * (1 + a) * D)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hl := Real.le_log_one_add_of_nonneg hu
  have hhalf : u / 2 ≤ 2 * u / (u + 2) := by
    apply (le_div_iff₀ (by positivity : 0 < u + 2)).mpr
    dsimp [u] at hsmall ⊢
    nlinarith [mul_nonneg hu (show 0 ≤ 1 - u by dsimp [u]; linarith)]
  have hden : 2 * (1 + a) * D ≤ 4 * D := by nlinarith
  have hratio : a * eps / (4 * D) ≤ u := by
    dsimp [u]
    exact div_le_div_of_nonneg_left (mul_nonneg ha heps) (by positivity) hden
  have hh : a * eps / (8 * D) ≤ u / 2 := by
    have heq : a * eps / (8 * D) = (a * eps / (4 * D)) / 2 := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hratio (by norm_num)
  exact hh.trans (hhalf.trans hl)

end
end Lax343628Proofs.ColumnExit
