import Lax343628Proofs.BudgetMass

namespace Lax343628Proofs.TrackingMass

noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Bounds (R u a D f A F L : ℝ) : Prop where
  small : 2 / (u + 1) + a * D + (D / (u * f) + 3 * D / u) ≤ 1 / 2
  square : ∀ T : ℝ, 0 ≤ T → T ≤ R →
    3 * (T * (2 / (u + 1)) ^ 2 + T * (a * D) ^ 2 +
      2 * (D / (u * f)) ^ 2 * (6 * R * F + 2 * L) + 18 * T * (D / u) ^ 2) ≤ 1 / 64
  stepM : 2 * (4 * D ^ 2 / (u * f)) * L ≤ 1 / 64
  varM : 4 * R * (3 * D ^ 4 / (u ^ 2 * f)) * L ≤ (1 / 64) ^ 2
  stepR : 2 * (5 * D ^ 2 / (u * A)) * L ≤ 1 / 64
  varR : 4 * R * (4 * D ^ 4 / (u ^ 2 * A)) * L ≤ (1 / 64) ^ 2

lemma of_mass (R u a D f A F L H Q M : ℝ)
    (hM : 1 ≤ M) (hmu : M ≤ u) (hmf : M ≤ u * f) (hma : M ≤ u * A)
    (hR : R ≤ u * H) (_hR0 : 0 ≤ R) (hH : 1 ≤ H) (hD : 1 ≤ D) (hQ : 1 ≤ Q) (hL : 1 ≤ L)
    (ha : 0 ≤ a) (ha1 : a ≤ 1 / u) (hF : 0 ≤ F) (hFQ : F ≤ Q * f)
    (hbig : H * D ^ 4 * Q * L / M ≤ 1 / 16777216) : Bounds R u a D f A F L := by
  have hMp : 0 < M := by linarith
  have hup : 0 < u := hMp.trans_le hmu
  have hufp : 0 < u * f := hMp.trans_le hmf
  have hfp : 0 < f := ((mul_pos_iff.mp hufp).resolve_right (by rintro ⟨hneg, _⟩; linarith)).2
  have hHp : 0 ≤ H := by linarith
  have hDp : 0 ≤ D := by linarith
  have hQp : 0 ≤ Q := by linarith
  have hLp : 0 ≤ L := by linarith
  let X := H * D ^ 4 * Q * L / M
  have hD2 : D ≤ D ^ 2 := by nlinarith
  have hD4 : D ^ 2 ≤ D ^ 4 := by
    have hh : 1 ≤ D ^ 2 := by nlinarith
    nlinarith [sq_nonneg (D ^ 2 - 1)]
  have hdom : D / M ≤ X := by
    have h1 := BudgetMass.dominance H D Q L hH hD hQ hLp
    have h2 := mul_le_mul_of_nonneg_left hL (sq_nonneg D)
    apply div_le_div_of_nonneg_right _ hMp.le
    nlinarith
  have hs1 : 2 / (u + 1) ≤ 2 / M :=
    div_le_div_of_nonneg_left (by norm_num) hMp (by linarith)
  have hs2 : a * D ≤ D / M := by
    have hh := mul_le_mul_of_nonneg_right ha1 hDp
    have hh' : a * D ≤ D / u := by convert hh using 1 <;> first | rfl | ring
    exact hh'.trans (div_le_div_of_nonneg_left hDp hMp hmu)
  have hs3 := BudgetMass.step D u f M hDp hMp hmf
  have hs4 := div_le_div_of_nonneg_left (show 0 ≤ 3 * D by positivity) hMp hmu
  have hsmall : 2 / (u + 1) + a * D + (D / (u * f) + 3 * D / u) ≤ 7 * X := by
    have hh : 2 / M ≤ 2 * D / M := div_le_div_of_nonneg_right (by linarith) hMp.le
    linear_combination hs1 + hs2 + hs3 + hs4 + hh + 7 * hdom
  have hstepM := BudgetMass.noise_step 8 u f H D Q L M (by norm_num) hMp hmf hH hD hQ hLp
  have hstepR := BudgetMass.noise_step 10 u A H D Q L M (by norm_num) hMp hma hH hD hQ hLp
  have hvarM := BudgetMass.noise_var 12 R u f H D Q L M (by norm_num) hup hMp hmf hR hHp hQ hLp
  have hvarR := BudgetMass.noise_var 16 R u A H D Q L M (by norm_num) hup hMp hma hR hHp hQ hLp
  refine ⟨by dsimp [X] at hsmall; linarith, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT hTR
    have h1 := BudgetEstimates.square_sum T R u H a D f F Q L hT hTR hR hup hHp ha ha1 hD hfp hF hQp hFQ
    have h2 := BudgetEstimates.mass_square u H D f Q L M hM hmu hmf hH hDp hQ hL
    have h3 : 117 * H * D ^ 2 * Q * L / M ≤ 117 * X := by
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hD4 (show 0 ≤ 117 * H * Q * L by positivity)) hMp.le
      convert hh using 1 <;> first | rfl | ring
    have hh := h1.trans (h2.trans h3)
    dsimp [X] at hh
    linarith
  · have hh : 2 * (4 * D ^ 2 / (u * f)) * L ≤ 8 * X := by
      convert hstepM using 1 <;> first | rfl | ring
    dsimp [X] at hh
    linarith
  · have hh : 4 * R * (3 * D ^ 4 / (u ^ 2 * f)) * L ≤ 12 * X := by
      convert hvarM using 1 <;> first | rfl | ring
    dsimp [X] at hh
    norm_num only [one_div, inv_pow]
    linarith
  · have hh : 2 * (5 * D ^ 2 / (u * A)) * L ≤ 10 * X := by
      convert hstepR using 1 <;> first | rfl | ring
    dsimp [X] at hh
    linarith
  · have hh : 4 * R * (4 * D ^ 4 / (u ^ 2 * A)) * L ≤ 16 * X := by
      convert hvarR using 1 <;> first | rfl | ring
    dsimp [X] at hh
    norm_num only [one_div, inv_pow]
    linarith

end
end Lax343628Proofs.TrackingMass
