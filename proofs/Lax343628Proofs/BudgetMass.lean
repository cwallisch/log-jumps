import Lax343628Proofs.BudgetEstimates

namespace Lax343628Proofs.BudgetMass

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma step (c u f M : ℝ) (hc : 0 ≤ c) (hM : 0 < M) (hmf : M ≤ u * f) :
    c / (u * f) ≤ c / M := div_le_div_of_nonneg_left hc hM hmf

lemma variance (c R u H f M : ℝ) (hc : 0 ≤ c) (hu : 0 < u)
    (hH : 0 ≤ H) (hM : 0 < M) (hmf : M ≤ u * f) (hR : R ≤ u * H) :
    c * R / (u ^ 2 * f) ≤ c * H / M := by
  have huf : 0 < u * f := hM.trans_le hmf
  have ht : R / u ≤ H := (div_le_iff₀ hu).mpr (by nlinarith)
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc) huf.le
  have heq : c * R / (u ^ 2 * f) = (c * (R / u)) / (u * f) := by field_simp
  rw [heq]
  exact hh.trans (div_le_div_of_nonneg_left (mul_nonneg hc hH) hM hmf)

lemma dominance (H D Q L : ℝ) (hH : 1 ≤ H) (hD : 1 ≤ D) (hQ : 1 ≤ Q) (hL : 0 ≤ L) :
    D ^ 2 * L ≤ H * D ^ 4 * Q * L := by
  have hD2 : 1 ≤ D ^ 2 := by nlinarith
  have hD4 : D ^ 2 ≤ D ^ 4 := by nlinarith [sq_nonneg (D ^ 2 - 1)]
  have hHp : 0 ≤ H := by linarith
  have hHQ : 1 ≤ H * Q := by
    simpa only [one_mul] using mul_le_mul hH hQ (by norm_num : (0 : ℝ) ≤ 1) hHp
  have h1 := mul_le_mul_of_nonneg_right hD4 hL
  have h2 := mul_le_mul_of_nonneg_right hHQ (show 0 ≤ D ^ 4 * L by positivity)
  nlinarith

lemma noise_step (c u f H D Q L M : ℝ) (hc : 0 ≤ c) (hM : 0 < M) (hmf : M ≤ u * f)
    (hH : 1 ≤ H) (hD : 1 ≤ D) (hQ : 1 ≤ Q) (hL : 0 ≤ L) :
    c * D ^ 2 * L / (u * f) ≤ c * H * D ^ 4 * Q * L / M := by
  have h1 := step (c * D ^ 2 * L) u f M (by positivity) hM hmf
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (dominance H D Q L hH hD hQ hL) hc) hM.le
  apply h1.trans
  convert h2 using 1 <;> first | rfl | ring

lemma noise_var (c R u f H D Q L M : ℝ) (hc : 0 ≤ c) (hu : 0 < u) (hM : 0 < M)
    (hmf : M ≤ u * f) (hR : R ≤ u * H) (hH : 0 ≤ H) (hQ : 1 ≤ Q) (hL : 0 ≤ L) :
    c * R * D ^ 4 * L / (u ^ 2 * f) ≤ c * H * D ^ 4 * Q * L / M := by
  have h1 := variance (c * D ^ 4 * L) R u H f M (by positivity) hu hH hM hmf hR
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hQ (show 0 ≤ c * H * D ^ 4 * L by positivity)) hM.le
  have hh : c * R * D ^ 4 * L / (u ^ 2 * f) ≤ c * H * D ^ 4 * L / M := by
    convert h1 using 1 <;> first | rfl | ring
  apply hh.trans
  convert h2 using 1 <;> first | rfl | ring

end
end Lax343628Proofs.BudgetMass
