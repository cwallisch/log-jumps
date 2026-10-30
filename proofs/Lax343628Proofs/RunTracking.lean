import Lax343628Proofs.StepBudgets
import Lax343628Proofs.TrackingSums

namespace Lax343628Proofs.RunTracking

open Lax343628.Algorithm Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
open Lax343628Proofs.RunLogOdds Lax343628Proofs.SparseDynamics Lax343628Proofs.ClassChannels
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma drift_sum_lower (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (hP : ∀ t, t < sigma.1.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < sigma.1.val → ∀ b : Fin 2, 0 < fraction i b (P t))
    (amin : ℝ) (hamin : 0 < amin) (hres : ∀ t, t < sigma.1.val → amin ≤ fraction i 0 (P t)) :
    -(sigma.1.val : ℝ) * ((a * (3 : ℝ) ^ k + (3 : ℝ) ^ k * (((k : ℝ) + 1) + 1 / amin) / n) /
      ((mu : ℕ) + 1 : ℝ)) ≤
        ∑ t ∈ Finset.range sigma.1.val, (drift sigma pc i 1 a t (P t) - drift sigma pc i 0 a t (P t)) := by
  have hpoint (t : ℕ) (ht : t < sigma.1.val) :
      -((a * (3 : ℝ) ^ k + (3 : ℝ) ^ k * (((k : ℝ) + 1) + 1 / amin) / n) /
        ((mu : ℕ) + 1 : ℝ)) ≤ drift sigma pc i 1 a t (P t) - drift sigma pc i 0 a t (P t) := by
    have hb := DriftCancellation.lower_bound hk hn pc hpc sigma i ha horizon t ht (P t) (hP t ht) (hf t ht)
    have hratio : fraction i 1 (P t) / fraction i 0 (P t) ≤ 1 / amin :=
      (div_le_div_of_nonneg_right (fraction_bounds i 1 (P t)).2 (hf t ht 0).le).trans
        (div_le_div_of_nonneg_left (by norm_num) hamin (hres t ht))
    have hl : (a * (3 : ℝ) ^ k + (3 : ℝ) ^ k * (((k : ℝ) + 1) + fraction i 1 (P t) / fraction i 0 (P t)) / n) /
        ((mu : ℕ) + 1 : ℝ) ≤
      (a * (3 : ℝ) ^ k + (3 : ℝ) ^ k * (((k : ℝ) + 1) + 1 / amin) / n) / ((mu : ℕ) + 1 : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply add_le_add (le_refl _)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact mul_le_mul_of_nonneg_left (by linarith [hratio]) (by positivity)
    rw [neg_div] at hb
    exact (neg_le_neg hl).trans hb
  have hh := Finset.sum_le_sum (s := Finset.range sigma.1.val) (fun t ht ↦ hpoint t (Finset.mem_range.mp ht))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg, neg_mul] using hh

lemma track (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (H : Fin (R + 1)) (env : Lists n k (count R ell) rs) (i : Fin n) {a : ℝ} (ha : 0 ≤ a)
    (halpha : a = pc / ((mu : ℕ) + 1 : ℝ))
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → TaggedDynamics.Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = TaggedDynamics.next k (P t) (E t))
    (hP : ∀ t, t ≤ H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t ≤ H.val → ∀ b : Fin 2, 0 < fraction i b (P t))
    (fmin amin C : ℝ) (hfmin : 0 < fmin) (hamin : 0 < amin)
    (hmut : ∀ t, t < H.val → fmin ≤ fraction i 1 (P t))
    (hres : ∀ t, t < H.val → amin ≤ fraction i 0 (P t))
    (hbias : (3 : ℝ) ^ k * ((k : ℝ) + 1) / n ≤ 1)
    (hsmall : 2 / ((mu : ℕ) + 1 : ℝ) + a * (3 : ℝ) ^ k +
      ((3 : ℝ) ^ k / ((mu : ℕ) * fmin) + 3 * (3 : ℝ) ^ k / (mu : ℕ)) ≤ 1 / 2)
    (hdb : H.val * ((a * (3 : ℝ) ^ k + (3 : ℝ) ^ k * (((k : ℝ) + 1) + 1 / amin) / n) /
      ((mu : ℕ) + 1 : ℝ)) ≤ 1 / 32)
    (hcount : (∑ t ∈ Finset.range H.val, if channel i 1 (P t) (E t) then 1 else 0) ≤ C)
    (hqb : 3 * (H.val * (2 / ((mu : ℕ) + 1 : ℝ)) ^ 2 + H.val * (a * (3 : ℝ) ^ k) ^ 2 +
      2 * ((3 : ℝ) ^ k / ((mu : ℕ) * fmin)) ^ 2 * C + 18 * H.val * ((3 : ℝ) ^ k / (mu : ℕ)) ^ 2) ≤ 1 / 64)
    (hm : MismatchTotals.total H env P i 1 a + MismatchTotals.total H env P i 0 a ≤ 1 / 8)
    (hn1 : |∑ t ∈ Finset.range H.val, SparseNoise.noise (H, env) pc i 1 a t (P t) (E t)| ≤ 1 / 64)
    (hn0 : |∑ t ∈ Finset.range H.val, SparseNoise.noise (H, env) pc i 0 a t (P t) (E t)| ≤ 1 / 64) :
    Real.log (fraction i 1 (P H.val) / fraction i 0 (P H.val)) ≥
      Real.log (weighted (H, env) P i 1 a 0 / weighted (H, env) P i 0 a 0) - 1 / 4 := by
  have hx (t : ℕ) (ht : t < H.val) : |RunLogOdds.step (H, env) pc P E i 1 a t| ≤ 1 / 2 :=
    (StepBudgets.mutant_step_abs hk hn pc hpc (H, env) i ha horizon P E t ht (hP t ht.le) fmin hfmin (hmut t ht) hbias).trans hsmall
  have hd := drift_sum_lower hk hn pc hpc (H, env) i ha horizon P (fun t ht ↦ hP t ht.le)
    (fun t ht ↦ hf t ht.le) amin hamin hres
  have hq := StepBudgets.mutant_square_sum hk hn pc hpc (H, env) i ha horizon P E H.val le_rfl
    (fun t ht ↦ hP t ht.le) fmin hfmin hmut hbias
  have hc := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 2 * ((3 : ℝ) ^ k / ((mu : ℕ) * fmin)) ^ 2 by positivity)
  have hq' : (∑ t ∈ Finset.range H.val, RunLogOdds.step (H, env) pc P E i 1 a t ^ 2) ≤ 1 / 64 := by
    linarith
  have hd' : -(1 / 32 : ℝ) ≤ ∑ t ∈ Finset.range H.val,
      (drift (H, env) pc i 1 a t (P t) - drift (H, env) pc i 0 a t (P t)) := by
    change -(H.val : ℝ) * _ ≤ _ at hd
    linarith
  have ht := TrackingSums.budget (by omega : k ≤ n) pc hpc H env i a ha halpha P E hnext hP hf hx
    (1 / 32) (1 / 8) (1 / 64) (1 / 64) hd' hm hn1 hn0 hq'
  linarith

end
end Lax343628Proofs.RunTracking
