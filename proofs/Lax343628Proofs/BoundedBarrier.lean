import Lax343628Proofs.Barrier
import Lax343628Proofs.Trajectories

namespace Lax343628Proofs.BoundedBarrier

open Lax343628Proofs.Barrier Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain
open Lax343628Proofs.Trajectories
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

lemma bounded_second_moment (p : PMF α) (Δ : α → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ y ∈ p.support, |Δ y| ≤ b) : mean p (fun y ↦ Δ y ^ 2) ≤ b ^ 2 := by
  have hm := mean_mono_on_support p (fun y hy ↦
    (show Δ y ^ 2 ≤ b ^ 2 by
      have hsq := (sq_le_sq₀ (abs_nonneg (Δ y)) hb).mpr (h y hy)
      simpa only [sq_abs] using hsq))
  rwa [mean_const] at hm

lemma bounded_lower_barrier (K : α → PMF α) (A : Set α) (X : α → ℝ)
    (b δ lam : ℝ) (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hsmall : lam * b ≤ 1)
    (hvariance : lam * b ^ 2 ≤ δ)
    (hstep : ∀ x ∈ A, ∀ y ∈ (K x).support, |X y - X x| ≤ b)
    (hdrift : ∀ x ∈ A, δ ≤ mean (K x) (fun y ↦ X y - X x))
    (x : α) (level : ℝ) (t : ℕ) :
    (law (stopped K A) (PMF.pure x) t).toOuterMeasure {y | X y < level} ≤
      ENNReal.ofReal (Real.exp (-lam * (X x - level))) := by
  apply stopped_lower_barrier K A X lam lam hlam le_rfl
  · intro x hx y hy
    rw [abs_mul, abs_of_nonneg hlam]
    exact (mul_le_mul_of_nonneg_left (hstep x hx y hy) hlam).trans hsmall
  · intro x hx
    exact (mul_le_mul_of_nonneg_left
      (bounded_second_moment (K x) (fun y ↦ X y - X x) b hb (hstep x hx)) hlam).trans
        (hvariance.trans (hdrift x hx))

lemma bounded_path_barrier (K : α → PMF α) (A : Set α) (X : α → ℝ)
    (b δ lam : ℝ) (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hsmall : lam * b ≤ 1)
    (hvariance : lam * b ^ 2 ≤ δ)
    (hstep : ∀ x ∈ A, ∀ y ∈ (K x).support, |X y - X x| ≤ b)
    (hdrift : ∀ x ∈ A, δ ≤ mean (K x) (fun y ↦ X y - X x))
    (x : α) (level : ℝ) (t : ℕ) :
    (pathLaw K (PMF.pure x) t).toOuterMeasure {h | X (frozen A h) < level} ≤
      ENNReal.ofReal (Real.exp (-lam * (X x - level))) := by
  have h := bounded_lower_barrier K A X b δ lam hb hlam hsmall hvariance hstep hdrift x level t
  rw [← frozen_pathLaw, PMF.toOuterMeasure_map_apply] at h
  exact h

lemma bounded_positive_barrier (K : α → PMF α) (A : Set α) (X : α → ℝ)
    (b δ : ℝ) (hb : 0 < b) (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (hstep : ∀ x ∈ A, ∀ y ∈ (K x).support, |X y - X x| ≤ b)
    (hdrift : ∀ x ∈ A, δ ≤ mean (K x) (fun y ↦ X y - X x))
    (x : α) (level : ℝ) (t : ℕ) :
    (pathLaw K (PMF.pure x) t).toOuterMeasure {h | X (frozen A h) < level} ≤
      ENNReal.ofReal (Real.exp (-(δ / b ^ 2) * (X x - level))) := by
  apply bounded_path_barrier K A X b δ (δ / b ^ 2) hb.le (by positivity) _ _ hstep hdrift
  · have heq : (δ / b ^ 2) * b = δ / b := by field_simp
    rw [heq]
    exact (div_le_one hb).mpr hδb
  · rw [div_mul_cancel₀ _ (pow_ne_zero _ hb.ne')]

end
end Lax343628Proofs.BoundedBarrier
