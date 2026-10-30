import Lax343628Proofs.FiniteDrift
import Mathlib.Analysis.Complex.Exponential

namespace Lax343628Proofs.Barrier

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift
open scoped BigOperators ENNReal Classical

noncomputable section

variable {α : Type*} [Fintype α]

lemma exp_quadratic {u : ℝ} (hu : |u| ≤ 1) : Real.exp u ≤ 1 + u + u ^ 2 := by
  have h := (le_abs_self (Real.exp u - 1 - u)).trans (Real.abs_exp_sub_one_sub_id_le hu)
  linarith

lemma mean_exp_increment (p : PMF α) (Δ : α → ℝ) (θ lam : ℝ)
    (hlam : 0 ≤ lam) (hlamθ : lam ≤ θ)
    (hsmall : ∀ y ∈ p.support, |lam * Δ y| ≤ 1)
    (hdrift : θ * mean p (fun y ↦ Δ y ^ 2) ≤ mean p Δ) :
    mean p (fun y ↦ Real.exp (-lam * Δ y)) ≤ 1 := by
  have hquad : mean p (fun y ↦ Real.exp (-lam * Δ y)) ≤
      mean p (fun y ↦ (1 - lam * Δ y) + lam ^ 2 * Δ y ^ 2) := by
    apply mean_mono_on_support
    intro y hy
    have hb : |-lam * Δ y| ≤ 1 := by simpa only [neg_mul, abs_neg] using hsmall y hy
    have h := exp_quadratic hb
    nlinarith
  rw [mean_add, mean_sub, mean_const, mean_mul, mean_mul] at hquad
  have hs : 0 ≤ mean p (fun y ↦ Δ y ^ 2) := mean_nonneg _ (fun _ ↦ sq_nonneg _)
  have hθ := mul_le_mul_of_nonneg_left hdrift hlam
  have hlamθ' := mul_le_mul_of_nonneg_right hlamθ (mul_nonneg hlam hs)
  nlinarith

lemma exp_potential_drift (K : α → PMF α) (X : α → ℝ) (θ lam : ℝ)
    (hlam : 0 ≤ lam) (hlamθ : lam ≤ θ) (x : α)
    (hsmall : ∀ y ∈ (K x).support, |lam * (X y - X x)| ≤ 1)
    (hdrift : θ * mean (K x) (fun y ↦ (X y - X x) ^ 2) ≤
      mean (K x) (fun y ↦ X y - X x)) :
    mean (K x) (fun y ↦ Real.exp (-lam * X y)) ≤ Real.exp (-lam * X x) := by
  have h := mean_exp_increment (K x) (fun y ↦ X y - X x) θ lam hlam hlamθ hsmall hdrift
  have heq : (fun y ↦ Real.exp (-lam * X y)) =
      (fun y ↦ Real.exp (-lam * X x) * Real.exp (-lam * (X y - X x))) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, mean_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

lemma stopped_exp_drift (K : α → PMF α) (A : Set α) (X : α → ℝ) (θ lam : ℝ)
    (hlam : 0 ≤ lam) (hlamθ : lam ≤ θ)
    (hsmall : ∀ x ∈ A, ∀ y ∈ (K x).support, |lam * (X y - X x)| ≤ 1)
    (hdrift : ∀ x ∈ A, θ * mean (K x) (fun y ↦ (X y - X x) ^ 2) ≤
      mean (K x) (fun y ↦ X y - X x)) (x : α) :
    mean (stopped K A x) (fun y ↦ Real.exp (-lam * X y)) ≤ Real.exp (-lam * X x) := by
  by_cases hx : x ∈ A
  · rw [stopped, if_pos hx]
    exact exp_potential_drift K X θ lam hlam hlamθ x (hsmall x hx) (hdrift x hx)
  · rw [stopped, if_neg hx, mean_pure]

lemma stopped_lower_barrier (K : α → PMF α) (A : Set α) (X : α → ℝ) (θ lam : ℝ)
    (hlam : 0 ≤ lam) (hlamθ : lam ≤ θ)
    (hsmall : ∀ x ∈ A, ∀ y ∈ (K x).support, |lam * (X y - X x)| ≤ 1)
    (hdrift : ∀ x ∈ A, θ * mean (K x) (fun y ↦ (X y - X x) ^ 2) ≤
      mean (K x) (fun y ↦ X y - X x)) (x : α) (level : ℝ) (t : ℕ) :
    (law (stopped K A) (PMF.pure x) t).toOuterMeasure {y | X y < level} ≤
      ENNReal.ofReal (Real.exp (-lam * (X x - level))) := by
  have hm := mean_law_le (stopped K A) (fun y ↦ Real.exp (-lam * X y))
    (stopped_exp_drift K A X θ lam hlam hlamθ hsmall hdrift) (PMF.pure x) t
  rw [mean_pure] at hm
  have hmarkov := event_markov (law (stopped K A) (PMF.pure x) t)
    (fun y ↦ Real.exp (-lam * X y)) (fun y ↦ (Real.exp_pos _).le)
    {y | X y < level} (Real.exp (-lam * level)) (Real.exp_pos _) (by
      intro y hy
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (le_of_lt hy) (neg_nonpos.mpr hlam))
  have hratio : mean (law (stopped K A) (PMF.pure x) t)
      (fun y ↦ Real.exp (-lam * X y)) / Real.exp (-lam * level) ≤
        Real.exp (-lam * (X x - level)) := by
    calc
      _ ≤ Real.exp (-lam * X x) / Real.exp (-lam * level) :=
        div_le_div_of_nonneg_right hm (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  exact hmarkov.trans (ENNReal.ofReal_le_ofReal hratio)

end
end Lax343628Proofs.Barrier
