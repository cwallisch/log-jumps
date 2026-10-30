import Lax343628Proofs.RisingDrift

namespace Lax343628Proofs.SeedWait

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.RisingDrift
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

lemma runtime_from_drift (K : α → PMF α) (A : Set α) (X : α → ℝ)
    (M mu beta root : ℝ) (hM : 0 ≤ M) (hmu : 0 < mu) (hbeta : 0 < beta) (hroot : 0 < root)
    (hX : ∀ x, 0 ≤ X x) (hdiscrete : ∀ x ∈ A, X x = 0 ∨ 1 ≤ X x)
    (hactive : ∀ x ∈ A, X x ≤ M) (hnext : ∀ x ∈ A, ∀ y ∈ (K x).support, X y ≤ M)
    (hzero : ∀ x ∈ A, X x = 0 → root ≤ mean (K x) (fun y ↦ X y - X x))
    (hpositive : ∀ x ∈ A, 1 ≤ X x → beta * X x / mu ≤ mean (K x) (fun y ↦ X y - X x))
    (p : PMF α) :
    (∑' t, (law (stopped K A) p t).toOuterMeasure A) ≤ ENNReal.ofReal (M / root + mu * M / beta) := by
  let delta := min root (beta / mu)
  have hdelta : 0 < delta := lt_min hroot (div_pos hbeta hmu)
  have hdrift (x : α) (hx : x ∈ A) : delta ≤ mean (K x) (fun y ↦ X y - X x) := by
    rcases hdiscrete x hx with hz | hp
    · exact (min_le_left _ _).trans (hzero x hx hz)
    · have hh : beta / mu ≤ beta * X x / mu := by
        have hh := mul_le_mul_of_nonneg_left hp (div_nonneg hbeta.le hmu.le)
        convert hh using 1 <;> first | rfl | ring
      exact (min_le_right _ _).trans (hh.trans (hpositive x hx hp))
  have ht := stopped_runtime_le K A (remaining X M) delta hdelta (remaining_nonneg X M)
    (remaining_drift K A X M delta hactive hnext hdrift) p
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  have hmean : mean p (remaining X M) ≤ M :=
    (mean_mono p (remaining_le X M hM hX)).trans_eq (mean_const p M)
  apply (div_le_div_of_nonneg_right hmean hdelta.le).trans
  by_cases hr : root ≤ beta / mu
  · dsimp [delta]
    rw [min_eq_left hr]
    have hnon : 0 ≤ mu * M / beta := by positivity
    linarith
  · dsimp [delta]
    rw [min_eq_right (le_of_not_ge hr)]
    have heq : M / (beta / mu) = mu * M / beta := by field_simp
    rw [heq]
    have hnon : 0 ≤ M / root := by positivity
    linarith

end
end Lax343628Proofs.SeedWait
