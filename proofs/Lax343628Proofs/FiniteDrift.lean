import Lax343628Proofs.FiniteChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Lax343628Proofs.FiniteDrift

open Lax343628Proofs.FiniteChain
open scoped BigOperators ENNReal Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β]

def mean (p : PMF α) (f : α → ℝ) : ℝ := ∑ x, (p x).toReal * f x

lemma sum_mass (p : PMF α) : ∑ x, (p x).toReal = 1 := by
  have h : (∑ x, p x) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have h := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun x _ ↦ p.apply_ne_top x)] at h
  simpa only [ENNReal.toReal_one] using h

lemma mean_const (p : PMF α) (c : ℝ) : mean p (fun _ ↦ c) = c := by
  rw [mean, ← Finset.sum_mul, sum_mass, one_mul]

lemma mean_pure (x : α) (f : α → ℝ) : mean (PMF.pure x) f = f x := by
  unfold mean
  simp [PMF.pure_apply, apply_ite, ite_mul]

lemma mean_mono (p : PMF α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : mean p f ≤ mean p g :=
  Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg

lemma mean_mono_on_support (p : PMF α) {f g : α → ℝ}
    (h : ∀ x ∈ p.support, f x ≤ g x) : mean p f ≤ mean p g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p x = 0
  · simp only [hx, ENNReal.toReal_zero, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h x hx) ENNReal.toReal_nonneg

lemma mean_nonneg (p : PMF α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ mean p f :=
  Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (h x)

lemma mean_add (p : PMF α) (f g : α → ℝ) :
    mean p (fun x ↦ f x + g x) = mean p f + mean p g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (p : PMF α) (f g : α → ℝ) :
    mean p (fun x ↦ f x - g x) = mean p f - mean p g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mul (p : PMF α) (c : ℝ) (f : α → ℝ) :
    mean p (fun x ↦ c * f x) = c * mean p f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma mean_bind (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    mean (p.bind K) f = mean p (fun x ↦ mean (K x) f) := by
  have hmass : ∀ y, ((p.bind K) y).toReal = ∑ x, (p x).toReal * (K x y).toReal := by
    intro y
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
    · intro x _
      exact ENNReal.mul_ne_top (p.apply_ne_top x) ((K x).apply_ne_top y)
  unfold mean
  simp_rw [hmass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma mean_indicator (p : PMF α) (A : Set α) :
    mean p (fun x ↦ if x ∈ A then 1 else 0) = (p.toOuterMeasure A).toReal := by
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · unfold mean
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ A <;> simp [hx]
  · intro x _
    by_cases hx : x ∈ A <;> simp [hx, p.apply_ne_top]

lemma mean_law_le (K : α → PMF α) (V : α → ℝ)
    (h : ∀ x, mean (K x) V ≤ V x) (p : PMF α) (t : ℕ) :
    mean (law K p t) V ≤ mean p V := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [law_succ, mean_bind]
    exact (mean_mono _ h).trans ih

lemma event_markov (p : PMF α) (V : α → ℝ) (hV : ∀ x, 0 ≤ V x)
    (A : Set α) (B : ℝ) (hB : 0 < B) (h : ∀ x ∈ A, B ≤ V x) :
    p.toOuterMeasure A ≤ ENNReal.ofReal (mean p V / B) := by
  have hpoint : ∀ x, B * (if x ∈ A then 1 else 0) ≤ V x := by
    intro x
    by_cases hx : x ∈ A
    · simpa only [if_pos hx, mul_one] using h x hx
    · simpa only [if_neg hx, mul_zero] using hV x
  have hm := mean_mono p hpoint
  rw [mean_mul, mean_indicator] at hm
  have hprob : (p.toOuterMeasure A).toReal ≤ mean p V / B := by
    apply (le_div_iff₀ hB).mpr
    linarith
  have hne := ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) (event_le_one p A)
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hprob

def stopped (K : α → PMF α) (A : Set α) (x : α) : PMF α :=
  if x ∈ A then K x else PMF.pure x

lemma stopped_drift (K : α → PMF α) (A : Set α) (V : α → ℝ) (δ : ℝ)
    (h : ∀ x ∈ A, mean (K x) V ≤ V x - δ) (x : α) :
    mean (stopped K A x) V + δ * (if x ∈ A then 1 else 0) ≤ V x := by
  by_cases hx : x ∈ A
  · simp only [stopped, if_pos hx, mul_one]
    linarith [h x hx]
  · simp only [stopped, if_neg hx, mul_zero, add_zero, mean_pure]
    exact le_rfl

lemma stopped_step (K : α → PMF α) (A : Set α) (V : α → ℝ) (δ : ℝ)
    (h : ∀ x ∈ A, mean (K x) V ≤ V x - δ) (p : PMF α) :
    mean (p.bind (stopped K A)) V + δ * (p.toOuterMeasure A).toReal ≤ mean p V := by
  have hm := mean_mono p (stopped_drift K A V δ h)
  rw [mean_add, mean_mul, mean_indicator, ← mean_bind] at hm
  exact hm

lemma stopped_telescoping (K : α → PMF α) (A : Set α) (V : α → ℝ) (δ : ℝ)
    (h : ∀ x ∈ A, mean (K x) V ≤ V x - δ) (p : PMF α) (t : ℕ) :
    mean (law (stopped K A) p t) V +
      δ * (∑ s ∈ Finset.range t, ((law (stopped K A) p s).toOuterMeasure A).toReal) ≤
        mean p V := by
  induction t with
  | zero => simp only [law_zero, Finset.sum_range_zero, mul_zero, add_zero, le_refl]
  | succ t ih =>
    rw [Finset.sum_range_succ, law_succ]
    have hs := stopped_step K A V δ h (law (stopped K A) p t)
    linarith

lemma stopped_runtime_le (K : α → PMF α) (A : Set α) (V : α → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hV : ∀ x, 0 ≤ V x)
    (h : ∀ x ∈ A, mean (K x) V ≤ V x - δ) (p : PMF α) :
    (∑' t, (law (stopped K A) p t).toOuterMeasure A) ≤ ENNReal.ofReal (mean p V / δ) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro t
  have ht := stopped_telescoping K A V δ h p t
  have hnonneg := mean_nonneg (law (stopped K A) p t) hV
  have hbound : (∑ s ∈ Finset.range t, ((law (stopped K A) p s).toOuterMeasure A).toReal) ≤
      mean p V / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hne : ∀ s ∈ Finset.range t, (law (stopped K A) p s).toOuterMeasure A ≠ ∞ := by
    intro s _
    exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) (event_le_one _ _)
  have heq : ∑ s ∈ Finset.range t, (law (stopped K A) p s).toOuterMeasure A =
      ENNReal.ofReal (∑ s ∈ Finset.range t,
        ((law (stopped K A) p s).toOuterMeasure A).toReal) := by
    rw [← ENNReal.toReal_sum hne, ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr hne)]
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hbound

end
end Lax343628Proofs.FiniteDrift
