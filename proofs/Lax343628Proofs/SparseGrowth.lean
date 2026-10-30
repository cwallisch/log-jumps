import Lax343628Proofs.WeightedComparison

namespace Lax343628Proofs.SparseGrowth

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.RunLogOdds Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.ClassChannels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r R ell : ℕ} {mu rs : ℕ+}

def base (k : ℕ) (a omega : ℝ) : ℝ :=
  1 + a * (ShadowGaps.delta k * (omega / 2)) / (2 * (1 + a) * (3 : ℝ) ^ k)

lemma base_one_le {k : ℕ} (hk : 1 ≤ k) {a omega : ℝ} (ha : 0 ≤ a) (homega : 0 ≤ omega) : 1 ≤ base k a omega := by
  unfold base
  have hd := (ShadowGaps.delta_pos hk).le
  have hfrac : 0 ≤ a * (ShadowGaps.delta k * (omega / 2)) / (2 * (1 + a) * (3 : ℝ) ^ k) := by positivity
  linarith

lemma initial_log_bound (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n)
    (H : Fin (R + 1)) (env : Lists n (r + 1) (count R ell) rs) (i : Fin n)
    (omega : ℝ) (homega : 0 ≤ omega)
    (hgood : ∀ j : Fin (count R ell), (group H.val ell j.val).Nonempty →
      ∀ u, EmpiricalCap.frequency (env j) u < 1 - omega / 2)
    {a : ℝ} (ha : 0 ≤ a)
    (horizon : H.val * a * ReproductiveAdmissibility.error n (r + 1) ≤ 1)
    (hsmall : a * (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) ≤ 1)
    (hdim : (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) * (1 + (3 : ℝ) ^ (r + 1)) ≤
      ShadowGaps.delta (r + 1) * (omega / 2) / 2)
    (P : ℕ → Population n mu) (hP : ∀ u, (Sampling.zeros (P 0 u)).card = r + 1)
    (hf : ∀ b : Fin 2, 0 < fraction i b (P 0)) :
    Real.log (fraction i 1 (P 0) / fraction i 0 (P 0)) + H.val * Real.log (base (r + 1) a omega) -
      Real.log ((3 : ℝ) ^ (r + 1)) ≤
        Real.log (weighted (H, env) P i 1 a 0 / weighted (H, env) P i 0 a 0) := by
  have hpoint := SparseComparison.arbitrary_fields hr hn H env i omega homega hgood ha horizon hsmall hdim
  have havg := WeightedComparison.average_compare (P 0) hP (field (H, env) i 1 a 0) (field (H, env) i 0 a 0)
    (base (r + 1) a omega ^ H.val) ((3 : ℝ) ^ (r + 1)) hpoint
  have hbase : 0 < base (r + 1) a omega := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (base_one_le (by omega) ha homega)
  have hy := weighted_pos (H, env) P i 1 ha 0 hP (hf 1)
  have hz := weighted_pos (H, env) P i 0 ha 0 hP (hf 0)
  have hlog := WeightedComparison.log_ratio (hf 1) (hf 0) hy hz (pow_pos hbase H.val)
    (by positivity : (0 : ℝ) < 3 ^ (r + 1)) havg
  rw [Real.log_pow] at hlog
  exact hlog

end
end Lax343628Proofs.SparseGrowth
