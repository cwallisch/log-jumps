import Lax343628Proofs.FiniteEvents

namespace Lax343628Proofs.TwoStage

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*}

lemma split (p : PMF α) (F : α → PMF β) (A : Set β) (B : Set α) (q : ℝ≥0∞)
    (hF : ∀ x ∉ B, (F x).toOuterMeasure A ≤ q) :
    (p.bind F).toOuterMeasure A ≤ p.toOuterMeasure B + q := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' x, (B.indicator p x + p x * q) := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        apply (mul_le_mul' le_rfl (event_le_one (F x) A)).trans
        simp only [mul_one]
        exact le_add_of_nonneg_right zero_le
      · rw [Set.indicator_of_notMem hx, zero_add]
        exact mul_le_mul' le_rfl (hF x hx)
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul, ← PMF.toOuterMeasure_apply]

end
end Lax343628Proofs.TwoStage
