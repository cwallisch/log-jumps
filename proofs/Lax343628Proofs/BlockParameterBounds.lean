import Lax343628Proofs.BlockParameters

namespace Lax343628Proofs.BlockParameterBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma power_ratio (S : ℝ) (hS : 1 ≤ S) (p q : ℕ) (hpq : p + 1 ≤ q) :
    S ^ p / S ^ q ≤ 1 / S := by
  have hSp : 0 < S := by linarith
  apply (div_le_div_iff₀ (pow_pos hSp q) hSp).mpr
  rw [one_mul, ← pow_succ]
  exact pow_le_pow_right₀ hS hpq

lemma power_gap (S : ℝ) (hS : 1 ≤ S) (p q g : ℕ) (hpq : p + g ≤ q) :
    S ^ p / S ^ q ≤ 1 / S ^ g := by
  have hSp : 0 < S := by linarith
  apply (div_le_div_iff₀ (pow_pos hSp q) (pow_pos hSp g)).mpr
  rw [one_mul, ← pow_add]
  exact pow_le_pow_right₀ hS hpq

lemma denominator (S x c : ℝ) (p q g : ℕ) (hS : 1 ≤ S) (hc : 0 ≤ c)
    (hx : S ^ q ≤ x) (hpq : p + g ≤ q) : c * S ^ p / x ≤ c / S ^ g := by
  have hSp : 0 < S := by linarith
  have h1 := div_le_div_of_nonneg_left (show 0 ≤ c * S ^ p by positivity) (pow_pos hSp q) hx
  have h2 := mul_le_mul_of_nonneg_left (power_gap S hS p q g hpq) hc
  apply h1.trans
  convert h2 using 1 <;> first | rfl | ring

lemma mass (S D Q L : ℝ) (hS : 16777216 ≤ S) (hD : 0 ≤ D) (hDS : D ≤ S)
    (hQ : 0 ≤ Q) (hQS : Q ≤ S ^ 2) (hL : 0 < L) :
    S ^ 12 * D ^ 4 * Q * L / (S ^ 64 * L) ≤ 1 / 16777216 := by
  have hSp : 0 < S := by linarith
  have h1 := mul_le_mul (pow_le_pow_left₀ hD hDS 4) hQS hQ (by positivity : 0 ≤ S ^ 4)
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (show 0 ≤ S ^ 12 by positivity)) hL.le)
    (show 0 ≤ S ^ 64 * L by positivity)
  have hh : S ^ 12 * D ^ 4 * Q * L / (S ^ 64 * L) ≤ S ^ 18 / S ^ 64 := by
    convert h2 using 1 <;> first | rfl | field_simp
  apply hh.trans ((power_ratio S (by linarith) 18 64 (by norm_num)).trans _)
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hS

lemma sampling (S D : ℝ) (hS : 16777216 ≤ S) (hD : 0 ≤ D) (hDS : D ≤ S) :
    10 * S ^ 12 * (1 / S ^ 40) * D ^ 2 + S ^ 12 * D / S ^ 60 ≤ 1 / 32 := by
  have hSp : 0 < S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hDS 2)
    (show 0 ≤ 10 * S ^ 12 * (1 / S ^ 40) by positivity)
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hDS (show 0 ≤ S ^ 12 by positivity)) (show 0 ≤ S ^ 60 by positivity)
  have h1' : 10 * S ^ 12 * (1 / S ^ 40) * D ^ 2 ≤ 10 * (S ^ 14 / S ^ 40) := by
    convert h1 using 1 <;> first | rfl | field_simp
  have h2' : S ^ 12 * D / S ^ 60 ≤ S ^ 13 / S ^ 60 := by
    convert h2 using 1 <;> rfl
  have hp1 := power_ratio S hS1 14 40 (by norm_num)
  have hp2 := power_ratio S hS1 13 60 (by norm_num)
  have hh : 10 * S ^ 12 * (1 / S ^ 40) * D ^ 2 + S ^ 12 * D / S ^ 60 ≤ 11 / S := by
    linear_combination h1' + h2' + 10 * hp1 + hp2
  apply hh.trans
  apply (div_le_iff₀ hSp).mpr
  linarith

lemma lists (S G omega : ℝ) (hS : 16777216 ≤ S) (_hG : 0 ≤ G) (hGS : G ≤ S ^ 54)
    (homega : 1 / S ≤ omega) : G * (4 / (S ^ 120 * omega ^ 2)) ≤ 1 / 8 := by
  have hSp : 0 < S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hw : 0 < omega := (div_pos (by norm_num) hSp).trans_le homega
  have hh : G * (4 / (S ^ 120 * omega ^ 2)) ≤ 4 * (S ^ 56 / S ^ 120) := by
    calc
      _ = (4 * G) / (S ^ 120 * omega ^ 2) := by ring
      _ ≤ (4 * S ^ 54) / (S ^ 120 * (1 / S) ^ 2) := by gcongr
      _ = _ := by field_simp
  apply hh.trans ((mul_le_mul_of_nonneg_left (power_ratio S hS1 56 120 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 4)).trans _)
  have heq : 4 * (1 / S) = 4 / S := by ring
  rw [heq]
  apply (div_le_iff₀ hSp).mpr
  linarith

end
end Lax343628Proofs.BlockParameterBounds
