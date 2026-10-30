import Lax343628Proofs.DriftCancellation
import Lax343628Proofs.NoiseSquares

namespace Lax343628Proofs.StepBudgets

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.ClassChannels
open Lax343628Proofs.SparseDynamics Lax343628Proofs.RunLogOdds
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma mismatch_abs (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (t : ℕ) (ht : t < sigma.1.val)
    (hP : ∀ u, (Sampling.zeros (P t u)).card = k) (hf : 0 < fraction i b (P t)) :
    |MismatchTotals.mismatch sigma P i b a t| ≤ a * (3 : ℝ) ^ k := by
  have hy : 0 < average (P t) (liftClass (field sigma i b a t)) := hf.trans_le
    (GroupSampling.average_one_lower (P t) hP _ (field_one sigma i b ha t))
  have hb := AveragedOperators.difference_ratio_bound (P t)
    (mixedKernel (EmpiricalKernels.empirical (P t))) (mixedKernel (path sigma t))
    (field sigma i b a (t + 1)) ((3 : ℝ) ^ k) (by positivity)
    (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i b ha (t + 1) x))
    (field_ratio hk hn sigma i b ha horizon (t + 1))
  have hb' := hb.trans (mul_le_mul_of_nonneg_left (average_field_step (P t) sigma i b ha t ht)
    (by positivity : (0 : ℝ) ≤ 3 ^ k))
  unfold MismatchTotals.mismatch
  rw [abs_div, abs_mul, abs_of_nonneg ha, abs_of_pos hy]
  apply (div_le_iff₀ hy).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb' ha]

lemma mutant_step_abs (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → TaggedDynamics.Event n mu) (t : ℕ) (ht : t < sigma.1.val)
    (hP : ∀ u, (Sampling.zeros (P t u)).card = k) (fmin : ℝ) (hfmin : 0 < fmin)
    (hf : fmin ≤ fraction i 1 (P t)) (hbias : (3 : ℝ) ^ k * ((k : ℝ) + 1) / n ≤ 1) :
    |RunLogOdds.step sigma pc P E i 1 a t| ≤
      2 / ((mu : ℕ) + 1 : ℝ) + a * (3 : ℝ) ^ k +
        ((3 : ℝ) ^ k / ((mu : ℕ) * fmin) + 3 * (3 : ℝ) ^ k / (mu : ℕ)) := by
  have hd := DriftCancellation.mutant_abs hk hn pc hpc sigma i ha horizon t ht (P t) hP (hfmin.trans_le hf) hbias
  have hm := mismatch_abs hk hn sigma i 1 ha horizon P t ht hP (hfmin.trans_le hf)
  have hn' := NoiseSquares.mutant_abs hk hn sigma pc hpc i ha horizon t (P t) hP fmin hfmin hf (E t)
  unfold RunLogOdds.step
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hd hm)) hn')

lemma square_three (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

lemma mutant_square_sum (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → TaggedDynamics.Event n mu) (H : ℕ) (hH : H ≤ sigma.1.val)
    (hP : ∀ t, t < H → ∀ u, (Sampling.zeros (P t u)).card = k) (fmin : ℝ) (hfmin : 0 < fmin)
    (hf : ∀ t, t < H → fmin ≤ fraction i 1 (P t))
    (hbias : (3 : ℝ) ^ k * ((k : ℝ) + 1) / n ≤ 1) :
    (∑ t ∈ Finset.range H, RunLogOdds.step sigma pc P E i 1 a t ^ 2) ≤
      3 * (H * (2 / ((mu : ℕ) + 1 : ℝ)) ^ 2 + H * (a * (3 : ℝ) ^ k) ^ 2 +
        2 * ((3 : ℝ) ^ k / ((mu : ℕ) * fmin)) ^ 2 *
          (∑ t ∈ Finset.range H, if channel i 1 (P t) (E t) then 1 else 0) +
        18 * H * ((3 : ℝ) ^ k / (mu : ℕ)) ^ 2) := by
  have hs := Finset.sum_le_sum (s := Finset.range H) (fun t ht ↦
    square_three (drift sigma pc i 1 a t (P t)) (MismatchTotals.mismatch sigma P i 1 a t)
      (SparseNoise.noise sigma pc i 1 a t (P t) (E t)))
  have hd : (∑ t ∈ Finset.range H, drift sigma pc i 1 a t (P t) ^ 2) ≤ H * (2 / ((mu : ℕ) + 1 : ℝ)) ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.range H) (fun t ht ↦ by
      have htime := Finset.mem_range.mp ht
      have hb := DriftCancellation.mutant_abs hk hn pc hpc sigma i ha horizon t (lt_of_lt_of_le htime hH)
        (P t) (hP t htime) (hfmin.trans_le (hf t htime)) hbias
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb)
    simpa only [sq_abs, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hm : (∑ t ∈ Finset.range H, MismatchTotals.mismatch sigma P i 1 a t ^ 2) ≤ H * (a * (3 : ℝ) ^ k) ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.range H) (fun t ht ↦ by
      have htime := Finset.mem_range.mp ht
      have hb := mismatch_abs hk hn sigma i 1 ha horizon P t (lt_of_lt_of_le htime hH)
        (hP t htime) (hfmin.trans_le (hf t htime))
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb)
    simpa only [sq_abs, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hn' := NoiseSquares.mutant_sum hk hn sigma pc hpc i ha horizon P E H hP fmin hfmin hf
  change (∑ t ∈ Finset.range H, RunLogOdds.step sigma pc P E i 1 a t ^ 2) ≤ _ at hs
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linarith

end
end Lax343628Proofs.StepBudgets
