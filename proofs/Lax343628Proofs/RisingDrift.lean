import Lax343628Proofs.FiniteDrift

namespace Lax343628Proofs.RisingDrift

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

def remaining (X : α → ℝ) (cap : ℝ) (x : α) : ℝ := cap - min (X x) cap

omit [Fintype α] in
lemma remaining_nonneg (X : α → ℝ) (cap : ℝ) (x : α) : 0 ≤ remaining X cap x :=
  sub_nonneg.mpr (min_le_right _ _)

omit [Fintype α] in
lemma remaining_le (X : α → ℝ) (cap : ℝ) (hcap : 0 ≤ cap) (hX : ∀ x, 0 ≤ X x) (x : α) :
    remaining X cap x ≤ cap := by
  have hmin := le_min (hX x) hcap
  unfold remaining
  linarith

lemma remaining_drift (K : α → PMF α) (A : Set α) (X : α → ℝ) (cap δ : ℝ)
    (hactive : ∀ x ∈ A, X x ≤ cap)
    (hnext : ∀ x ∈ A, ∀ y ∈ (K x).support, X y ≤ cap)
    (hδ : ∀ x ∈ A, δ ≤ mean (K x) (fun y ↦ X y - X x)) :
    ∀ x ∈ A, mean (K x) (remaining X cap) ≤ remaining X cap x - δ := by
  intro x hx
  have heq : mean (K x) (remaining X cap) = mean (K x) (fun y ↦ cap - X y) := by
    apply le_antisymm
    · apply mean_mono_on_support
      intro y hy
      rw [remaining, min_eq_left (hnext x hx y hy)]
    · apply mean_mono_on_support
      intro y hy
      rw [remaining, min_eq_left (hnext x hx y hy)]
  have hdrift := hδ x hx
  rw [mean_sub, mean_const] at hdrift
  rw [heq, mean_sub, mean_const, remaining, min_eq_left (hactive x hx)]
  linarith

lemma stopped_event_bound (K : α → PMF α) (A : Set α) (V : α → ℝ) (cap δ : ℝ)
    (hδ : 0 < δ) (hV : ∀ x, 0 ≤ V x) (hcap : ∀ x, V x ≤ cap)
    (hdrift : ∀ x ∈ A, mean (K x) V ≤ V x - δ) (p : PMF α) (t : ℕ) :
    (law (stopped K A) p t).toOuterMeasure A ≤
      ENNReal.ofReal (cap / (δ * ((t : ℝ) + 1))) := by
  have habs : ∀ x ∉ A, (stopped K A x).toOuterMeasure A = 0 := by
    intro x hx
    simp only [stopped, PMF.toOuterMeasure_pure_apply, if_neg hx]
  have hmono := event_law_antitone (stopped K A) p A habs
  have hne (s : ℕ) : (law (stopped K A) p s).toOuterMeasure A ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (event_le_one _ _)
  have hsum : ((t : ℝ) + 1) * ((law (stopped K A) p t).toOuterMeasure A).toReal ≤
      ∑ s ∈ Finset.range (t + 1), ((law (stopped K A) p s).toOuterMeasure A).toReal := by
    calc
      _ = ∑ _s ∈ Finset.range (t + 1),
          ((law (stopped K A) p t).toOuterMeasure A).toReal := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        exact ENNReal.toReal_mono (hne s) (hmono (by have h := Finset.mem_range.mp hs; omega))
  have ht := stopped_telescoping K A V δ hdrift p (t + 1)
  have hnonneg := mean_nonneg (law (stopped K A) p (t + 1)) hV
  have hcapmean := (mean_mono p hcap).trans_eq (mean_const p cap)
  have hscaled := mul_le_mul_of_nonneg_left hsum hδ.le
  have hprob : ((law (stopped K A) p t).toOuterMeasure A).toReal ≤
      cap / (δ * ((t : ℝ) + 1)) := by
    apply (le_div_iff₀ (by positivity : 0 < δ * ((t : ℝ) + 1))).mpr
    nlinarith
  rw [← ENNReal.ofReal_toReal (hne t)]
  exact ENNReal.ofReal_le_ofReal hprob

lemma rising_event_bound (K : α → PMF α) (A : Set α) (X : α → ℝ) (cap δ : ℝ)
    (hcap : 0 ≤ cap) (hX : ∀ x, 0 ≤ X x) (hδpos : 0 < δ)
    (hactive : ∀ x ∈ A, X x ≤ cap)
    (hnext : ∀ x ∈ A, ∀ y ∈ (K x).support, X y ≤ cap)
    (hδ : ∀ x ∈ A, δ ≤ mean (K x) (fun y ↦ X y - X x)) (p : PMF α) (t : ℕ) :
    (law (stopped K A) p t).toOuterMeasure A ≤
      ENNReal.ofReal (cap / (δ * ((t : ℝ) + 1))) :=
  stopped_event_bound K A (remaining X cap) cap δ hδpos (remaining_nonneg X cap)
    (remaining_le X cap hcap hX) (remaining_drift K A X cap δ hactive hnext hδ) p t

end
end Lax343628Proofs.RisingDrift
