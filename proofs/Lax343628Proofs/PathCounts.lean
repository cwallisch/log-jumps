import Lax343628Proofs.PathNoise
import Lax343628Proofs.ChannelNoise

namespace Lax343628Proofs.PathCounts

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.PathNoise Lax343628Proofs.ChannelNoise Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α]

lemma centered_unit (p : PMF α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (∀ x, |centered p f x| ≤ 1) ∧ mean p (fun x ↦ centered p f x ^ 2) ≤ mean p f := by
  have hm : 0 ≤ mean p f := mean_nonneg p (fun x ↦ (hf x).1)
  have hu : mean p f ≤ 1 := (mean_mono p (fun x ↦ (hf x).2)).trans_eq (mean_const p 1)
  constructor
  · intro x
    unfold centered
    exact abs_le.mpr ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩
  · rw [variance_identity]
    have hh := mean_mono p (fun x ↦ show f x ^ 2 ≤ f x by nlinarith [(hf x).1, (hf x).2])
    nlinarith [sq_nonneg (mean p f)]

def noise (K : α → PMF α) (g : ℕ → α → α → ℝ) (t : ℕ) (x y : α) : ℝ := centered (K x) (g t x) y

lemma comparison (K : α → PMF α) (g : ℕ → α → α → ℝ) (q : ℝ)
    (hmean : ∀ t x, mean (K x) (g t x) ≤ q) (t : ℕ) (h : Fin (t + 1) → α) :
    accumulate g t h ≤ accumulate (noise K g) t h + t * q := by
  induction t with
  | zero => simp only [accumulate, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ t ih =>
    simp only [accumulate, noise, centered, Nat.cast_add, Nat.cast_one]
    have hh := ih (Fin.init h)
    have hm := hmean t (h (Fin.last t).castSucc)
    nlinarith

lemma tail (K : α → PMF α) (p : PMF α) (g : ℕ → α → α → ℝ) (q L : ℝ)
    (hq : 0 ≤ q) (hg : ∀ t x y, 0 ≤ g t x y ∧ g t x y ≤ 1)
    (hmean : ∀ t x, mean (K x) (g t x) ≤ q) (H : ℕ) :
    (pathLaw K p H).toOuterMeasure {h | 2 * H * q + 2 * L ≤ accumulate g H h} ≤
      ENNReal.ofReal (Real.exp (-L)) := by
  have hh := upper_tail K p (noise K g) (1 / 2) q (by norm_num)
    (fun t x y _ ↦ by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hb := (centered_unit (K x) (g t x) (hg t x)).1 y
      change (1 / 2 : ℝ) * |centered (K x) (g t x) y| ≤ 1
      linarith)
    (fun t x ↦ mean_centered (K x) (g t x))
    (fun t x ↦ ((centered_unit (K x) (g t x) (hg t x)).2).trans (hmean t x))
    H (H * q + 2 * L)
  have hm : (pathLaw K p H).toOuterMeasure {h | 2 * H * q + 2 * L ≤ accumulate g H h} ≤
      (pathLaw K p H).toOuterMeasure {h | H * q + 2 * L ≤ accumulate (noise K g) H h} := by
    apply MeasureTheory.measure_mono
    intro h hh
    have hc := comparison K g q hmean H h
    change H * q + 2 * L ≤ accumulate (noise K g) H h
    change 2 * H * q + 2 * L ≤ accumulate g H h at hh
    linarith
  apply hm.trans (hh.trans _)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  nlinarith [mul_nonneg hH hq]

end
end Lax343628Proofs.PathCounts
