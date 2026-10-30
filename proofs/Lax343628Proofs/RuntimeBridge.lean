import Lax343628.Runtime
import Lax343628Proofs.FiniteChain
import Lax343628Proofs.Dynamics

namespace Lax343628Proofs.RuntimeBridge

open Lax343628.Algorithm Lax343628.Runtime
open Lax343628Proofs.FiniteChain Lax343628Proofs.Dynamics
open scoped ENNReal Classical BigOperators

noncomputable section

lemma populationLaw_eq (n k : ℕ) (μ : ℕ+) (p_c : ℝ) (t : ℕ) :
    populationLaw n k μ p_c t =
      law (step (jump k) p_c) (PMF.uniformOfFintype (Population n μ)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (populationLaw n k μ p_c t).bind (step (jump k) p_c) = _
    rw [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
lemma tailProbability_eq (n k : ℕ) (μ : ℕ+) (p_c : ℝ) (t : ℕ) :
    tailProbability n k μ p_c t = (populationLaw n k μ p_c t).toOuterMeasure missing := by
  rw [PMF.toOuterMeasure_apply_fintype]
  simp only [tailProbability, missing, Set.indicator, Set.mem_ofPred_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  by_cases h : ∀ i, P i ≠ optimum n
  · simp only [if_pos h]
  · simp only [if_neg h]

lemma expectedRuntime_le_of_block (n k : ℕ) (μ : ℕ+) (p_c : ℝ) (hk : 0 < k)
    (L : ℕ) (hL : 0 < L) (r : ℝ≥0∞)
    (hblock : ∀ P : Population n μ, P ∈ missing →
      (law (step (jump k) p_c) (PMF.pure P) L).toOuterMeasure missing ≤ r) :
    expectedRuntime n k μ p_c ≤ (L : ℝ≥0∞) * (1 - r)⁻¹ := by
  have heq : expectedRuntime n k μ p_c = ∑' t,
      (law (step (jump k) p_c) (PMF.uniformOfFintype (Population n μ)) t).toOuterMeasure
        missing := by
    simp only [expectedRuntime, tailProbability_eq, populationLaw_eq]
  rw [heq]
  exact runtime_le_of_block _ _ missing (step_missing_eq_zero hk p_c) L hL r hblock

end
end Lax343628Proofs.RuntimeBridge
