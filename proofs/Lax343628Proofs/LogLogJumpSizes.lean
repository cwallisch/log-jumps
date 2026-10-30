import Lax343628.LogLogJumpSizes
import Lax343628Proofs.LogEnvelope

namespace Lax343628Proofs.LogLogJumpSizes

open Lax343628.Algorithm Lax343628.Runtime Filter
open scoped ENNReal

/--
---
conclusion: Lax343628.LogLogJumpSizes.runtime_bound
---
-/
theorem runtime_bound
    (p_c a : ℝ) (hp_c : 0 < p_c ∧ p_c ≤ 1) (ha : 0 < a) :
    ∃ c C B : ℝ, 0 < c ∧ 0 < C ∧ 0 < B ∧
      ∀ᶠ (n : ℕ) in atTop,
        ∀ (k : ℕ) (μ : ℕ+),
          1 ≤ k → (k : ℝ) ≤ c * Real.log (Real.log (n : ℝ)) →
          C * (k : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (μ : ℕ) →
          (μ : ℕ) ≤ (n : ℝ) ^ a →
          expectedRuntime n k μ p_c ≤
            ENNReal.ofReal (B * (μ : ℕ) * (n : ℝ)) := by
  obtain ⟨c, C, hc, hC, h⟩ := LogEnvelope.doubly_logarithmic p_c a hp_c ha
  have hpp := hp_c.1
  exact ⟨c, C, 268435456 / p_c, hc, hC, by positivity, h⟩

end Lax343628Proofs.LogLogJumpSizes
