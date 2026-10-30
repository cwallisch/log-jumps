import Lax343628.LogJumpSizes
import Lax343628Proofs.LogEnvelope

namespace Lax343628Proofs.LogJumpSizes

open Lax343628.Algorithm Lax343628.Runtime Filter
open scoped ENNReal

/--
---
conclusion: Lax343628.LogJumpSizes.runtime_bound
---
-/
theorem runtime_bound
    (p_c ε a : ℝ) (hp_c : 0 < p_c ∧ p_c ≤ 1) (hε : 0 < ε) (ha : ε ≤ a) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      ∀ᶠ (n : ℕ) in atTop,
        ∀ (k : ℕ) (μ : ℕ+),
          1 ≤ k → (k : ℝ) ≤ c * Real.log (n : ℝ) →
          (n : ℝ) ^ ε ≤ (μ : ℕ) → (μ : ℕ) ≤ (n : ℝ) ^ a →
          expectedRuntime n k μ p_c ≤
            ENNReal.ofReal (B * (μ : ℕ) * (n : ℝ)) := by
  obtain ⟨c, hc, h⟩ := LogEnvelope.logarithmic p_c ε a hp_c hε ha
  have hpp := hp_c.1
  exact ⟨c, 268435456 / p_c, hc, by positivity, h⟩

end Lax343628Proofs.LogJumpSizes
