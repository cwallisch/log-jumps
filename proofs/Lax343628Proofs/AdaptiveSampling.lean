import Lax343628Proofs.FiniteConditioning

namespace Lax343628Proofs.AdaptiveSampling

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.FiniteProduct Lax343628Proofs.FiniteConditioning
open Lax343628Proofs.EmpiricalSampling
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma adaptive_sample_error (p : ι → PMF α) (j : ι) {r : ℕ} (hr : 1 ≤ r)
    (f : ({k : ι // k ≠ j} → Fin r → α) → α → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ rest x, 0 ≤ f rest x ∧ f rest x ≤ M) :
    mean (distribution (fun k ↦ samples (p k) r)) (fun env ↦
      |sampleMean (f (fun k ↦ env k.val)) (env j) - mean (p j) (f (fun k ↦ env k.val))|) ≤
        M / (2 * Real.sqrt r) := by
  apply conditional_bound _ j _ _
  intro rest
  have hpoint (xs : Fin r → α) :
      (fun k : {k : ι // k ≠ j} ↦ fill j rest xs k.val) = rest := by
    funext k
    simp only [fill, dif_neg k.property]
  have hj (xs : Fin r → α) : fill j rest xs j = xs := by simp [fill]
  simp_rw [hpoint, hj]
  exact sample_error (p j) (f rest) M hM (hf rest) hr

lemma mean_sum {β γ : Type*} [Fintype β] [Fintype γ] (p : PMF β) (f : γ → β → ℝ) :
    mean p (fun x ↦ ∑ j, f j x) = ∑ j, mean p (f j) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq α] in
lemma adaptive_total_error (p : ι → PMF α) {r : ℕ} (hr : 1 ≤ r)
    (f : (j : ι) → ({k : ι // k ≠ j} → Fin r → α) → α → ℝ)
    (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hf : ∀ j rest x, 0 ≤ f j rest x ∧ f j rest x ≤ M j) :
    mean (distribution (fun k ↦ samples (p k) r)) (fun env ↦ ∑ j,
      |sampleMean (f j (fun k ↦ env k.val)) (env j) - mean (p j) (f j (fun k ↦ env k.val))|) ≤
        (∑ j, M j) / (2 * Real.sqrt r) := by
  rw [mean_sum]
  calc
    _ ≤ ∑ j, M j / (2 * Real.sqrt r) := Finset.sum_le_sum
      (fun j _ ↦ adaptive_sample_error p j hr (f j) (M j) (hM j) (hf j))
    _ = _ := (Finset.sum_div _ _ _).symm

end
end Lax343628Proofs.AdaptiveSampling
