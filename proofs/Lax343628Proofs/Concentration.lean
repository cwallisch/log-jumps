import Lax343628Proofs.Barrier

namespace Lax343628Proofs.Concentration

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift Lax343628Proofs.Barrier
open scoped BigOperators ENNReal Classical

noncomputable section

variable {α : Type*} [Fintype α]

lemma centered_exp_bound (p : PMF α) (Δ : α → ℝ) (lam v : ℝ)
    (hsmall : ∀ y ∈ p.support, |lam * Δ y| ≤ 1) (hmean : mean p Δ = 0)
    (hvar : mean p (fun y ↦ Δ y ^ 2) ≤ v) :
    mean p (fun y ↦ Real.exp (lam * Δ y)) ≤ Real.exp (lam ^ 2 * v) := by
  have hquad : mean p (fun y ↦ Real.exp (lam * Δ y)) ≤
      mean p (fun y ↦ (1 + lam * Δ y) + lam ^ 2 * Δ y ^ 2) := by
    apply mean_mono_on_support
    intro y hy
    have h := exp_quadratic (hsmall y hy)
    nlinarith
  rw [mean_add, mean_add, mean_const, mean_mul, mean_mul, hmean, mul_zero, add_zero] at hquad
  have h := mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
  exact (hquad.trans (by linarith)).trans (Real.add_one_le_exp (lam ^ 2 * v))

end
end Lax343628Proofs.Concentration
