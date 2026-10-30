import Lax343628Proofs.ChannelNoise
import Lax343628Proofs.EmpiricalSampling

namespace Lax343628Proofs.NoiseNormalization

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.ChannelNoise
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

def noise (p : PMF α) (Y : α → ℝ) (mu y : ℝ) (x : α) : ℝ := centered p Y x / (mu * y)

lemma mean_noise (p : PMF α) (Y : α → ℝ) (mu y : ℝ) : mean p (noise p Y mu y) = 0 := by
  have heq : noise p Y mu y = fun x ↦ (mu * y)⁻¹ * centered p Y x := by
    funext x; unfold noise; ring
  rw [heq, mean_mul, mean_centered, mul_zero]

lemma normalized_bounds (p : PMF α) (A : Set α) (Y : α → ℝ)
    (mu y M D gamma f fmin : ℝ) (hmu : 0 < mu) (hy : 0 < y) (hM : 0 ≤ M)
    (hD : 0 ≤ D) (hgamma : 0 ≤ gamma) (hfmin : 0 < fmin) (hflow : fmin ≤ f) (hfhi : f ≤ 1)
    (hMY : M * f ≤ D * y) (hY : ∀ x, |Y x| ≤ M) (hz : ∀ x, x ∉ A → Y x = 0)
    (hp : mean p (fun x ↦ if x ∈ A then 1 else 0) ≤ gamma * f) :
    (∀ x, |noise p Y mu y x| ≤ (1 + gamma) * D / (mu * fmin)) ∧
      mean p (fun x ↦ noise p Y mu y x ^ 2) ≤ gamma * D ^ 2 / (mu ^ 2 * fmin) := by
  have hf : 0 < f := hfmin.trans_le hflow
  have hnorm : M / (mu * y) ≤ D / (mu * f) := by
    apply (div_le_div_iff₀ (mul_pos hmu hy) (mul_pos hmu hf)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hMY hmu.le]
  have hnorm' : M / (mu * y) ≤ D / (mu * fmin) :=
    hnorm.trans (div_le_div_of_nonneg_left hD (mul_pos hmu hfmin)
      (mul_le_mul_of_nonneg_left hflow hmu.le))
  constructor
  · intro x
    have hc := centered_channel_bound p A Y M (gamma * f) hM hY hz hp x
    have hI : (if x ∈ A then (1 : ℝ) else 0) + gamma * f ≤ 1 + gamma := by
      split_ifs <;> nlinarith
    have hIn : 0 ≤ (if x ∈ A then (1 : ℝ) else 0) + gamma * f := by
      split_ifs <;> positivity
    unfold noise
    rw [abs_div, abs_of_pos (mul_pos hmu hy)]
    calc
      _ ≤ M * ((if x ∈ A then 1 else 0) + gamma * f) / (mu * y) :=
        div_le_div_of_nonneg_right hc (mul_pos hmu hy).le
      _ = (M / (mu * y)) * ((if x ∈ A then 1 else 0) + gamma * f) := by ring
      _ ≤ (D / (mu * fmin)) * (1 + gamma) :=
        mul_le_mul hnorm' hI hIn (by positivity)
      _ = _ := by ring
  · have hv := centered_variance_bound p A Y M (gamma * f) hM hY hz hp
    have heq : (fun x ↦ noise p Y mu y x ^ 2) =
        (fun x ↦ centered p Y x ^ 2 * ((mu * y) ^ 2)⁻¹) := by
      funext x
      unfold noise
      ring
    rw [heq, EmpiricalSampling.mean_mul_right]
    have hsq : (M / (mu * y)) ^ 2 ≤ (D / (mu * f)) ^ 2 := by
      have hnon : 0 ≤ M / (mu * y) := by positivity
      nlinarith
    calc
      _ ≤ (M ^ 2 * (gamma * f)) * ((mu * y) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hv (by positivity)
      _ = (gamma * f) * (M / (mu * y)) ^ 2 := by ring
      _ ≤ (gamma * f) * (D / (mu * f)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hgamma hf.le)
      _ = gamma * D ^ 2 / (mu ^ 2 * f) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hgamma (sq_nonneg D))
        (mul_pos (sq_pos_of_pos hmu) hfmin) (mul_le_mul_of_nonneg_left hflow (sq_nonneg mu))

end
end Lax343628Proofs.NoiseNormalization
