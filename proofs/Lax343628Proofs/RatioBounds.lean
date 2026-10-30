import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace Lax343628Proofs.RatioBounds

lemma ideal_ratio_drift (p m f Q rho R₂ S₂ S₂' : ℝ)
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hf : 0 ≤ f) (hQ : 0 ≤ Q) (hQmax : Q ≤ 1 / 25)
    (hmass : m + f = Q * p) (hrho : 0 ≤ rho) (hrhomax : rho ≤ m / 4 + 5 / 96 * f)
    (hR : R₂ ≤ rho ^ 2) (hS : 51 / 80 * m ^ 2 + S₂' ≤ S₂) :
    34 / 1000 * p * f + 135 / 1000 * m ^ 2 + S₂' ≤
      1 / 16 * p * f + S₂ - 2 * (m + f) * rho - Q * R₂ := by
  have hrhomaxpos : 0 ≤ m / 4 + 5 / 96 * f := by positivity
  have hsq : rho ^ 2 ≤ (m / 4 + 5 / 96 * f) ^ 2 :=
    (sq_le_sq₀ hrho hrhomaxpos).mpr hrhomax
  have hQR : Q * R₂ ≤ (1 / 25 : ℝ) * (m / 4 + 5 / 96 * f) ^ 2 := by
    calc
      Q * R₂ ≤ Q * rho ^ 2 := mul_le_mul_of_nonneg_left hR hQ
      _ ≤ (1 / 25 : ℝ) * rho ^ 2 := mul_le_mul_of_nonneg_right hQmax (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hrhoL := mul_le_mul_of_nonneg_left hrhomax (show 0 ≤ 2 * (m + f) by positivity)
  have hLoss : 2 * (m + f) * rho + Q * R₂ ≤
      (201 / 400 : ℝ) * m ^ 2 + (5 / 8 : ℝ) * (m + f) * f := by
    nlinarith [mul_nonneg hm hf, sq_nonneg f]
  have hQp := mul_le_mul_of_nonneg_right hQmax hp
  have hfar := mul_le_mul_of_nonneg_right hQp hf
  rw [← hmass] at hfar
  nlinarith [mul_nonneg hp hf]

lemma ideal_ratio_strict_drift (p m f Q : ℝ) (hp : 0 ≤ p) (hm : 0 ≤ m) (hf : 0 ≤ f)
    (hQ : 1 / 50 ≤ Q) (hmass : m + f = Q * p) :
    (337 / 10000 : ℝ) * (1 / 50) * Q * p ^ 2 ≤
      (34 / 1000 : ℝ) * p * f + (135 / 1000 : ℝ) * m ^ 2 := by
  have hQpos : 0 ≤ Q := by linarith
  have hQppos : 0 ≤ Q * p ^ 2 := by positivity
  by_cases hfar : Q * p / 2 ≤ f
  · have h := mul_le_mul_of_nonneg_left hfar hp
    nlinarith [sq_nonneg m]
  · have hmhalf : Q * p / 2 ≤ m := by linarith
    have hmhalfpos : 0 ≤ Q * p / 2 := by positivity
    have hsquare := (sq_le_sq₀ hmhalfpos hm).mpr hmhalf
    have hQs := mul_le_mul_of_nonneg_right hQ (show 0 ≤ Q * p ^ 2 by positivity)
    nlinarith [mul_nonneg hp hf]

lemma ratio_increment_lower (N Q a b : ℝ) (hN : 1 < N) (hQ : 0 ≤ Q)
    (hb : b = -1 ∨ b = 0 ∨ b = 1) (hup : b = 1 → a ≤ 0) (hdown : b = -1 → 0 ≤ a) :
    (a - Q * b) / N ≤ (a - Q * b) / (N + b) := by
  rcases hb with rfl | rfl | rfl
  · apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    have ha := hdown rfl
    nlinarith
  · simp
  · apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    have ha := hup rfl
    nlinarith

lemma ratio_increment_abs (N Q a b : ℝ) (hN : 1 < N) (hQ : 0 ≤ Q)
    (ha : |a| ≤ 5 / 4) (hb : |b| ≤ 1) :
    |(a - Q * b) / (N + b)| ≤ (5 / 4 + Q) / (N - 1) := by
  have hb' := (abs_le.mp hb).1
  have hden : 0 < N + b := by linarith
  rw [abs_div, abs_of_pos hden]
  have hnum : |a - Q * b| ≤ 5 / 4 + Q := by
    calc
      _ ≤ |a| + |Q * b| := abs_sub _ _
      _ = |a| + Q * |b| := by rw [abs_mul, abs_of_nonneg hQ]
      _ ≤ _ := add_le_add ha (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hQ)
  calc
    _ ≤ (5 / 4 + Q) / (N + b) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

end Lax343628Proofs.RatioBounds
