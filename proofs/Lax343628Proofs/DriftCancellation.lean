import Lax343628Proofs.BiasNormalization

namespace Lax343628Proofs.DriftCancellation

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseDynamics Lax343628Proofs.SparseEnvironment
open Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassMeanDynamics Lax343628Proofs.ClassChannels
open Lax343628Proofs.FieldDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma scalar_difference {c r s v w delta B m : ℝ} (hm : 0 < m) (hc : |c| ≤ 1)
    (hr : 1 - delta ≤ r ∧ r ≤ 1) (hs : 1 - delta ≤ s ∧ s ≤ 1)
    (hv : 0 ≤ v) (hw : w ≤ B) :
    -(delta + B) / m ≤ (c * r + v) / m - (c * s + w) / m := by
  have hd : 0 ≤ delta := by linarith
  have hrs : |r - s| ≤ delta := abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : |c * (r - s)| ≤ delta := by
    rw [abs_mul]
    exact (mul_le_mul hc hrs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul delta)
  have hl := (abs_le.mp hprod).1
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ hm.le
  nlinarith

lemma drift_eq (sigma : Net n k R (count R ell) rs) (pc : ℝ) (i : Fin n) (b : Fin 2)
    (a : ℝ) (t : ℕ) (P : Population n mu) :
    drift sigma pc i b a t P =
      ((copyWeight n pc - viability k pc P) *
        (average P (liftClass (field sigma i b a (t + 1))) / average P (liftClass (field sigma i b a t))) +
        bias (k := k) pc P i b (liftClass (field sigma i b a (t + 1))) / average P (liftClass (field sigma i b a t))) /
          ((mu : ℕ) + 1 : ℝ) := by
  unfold drift
  rw [div_mul_eq_div_mul_one_div]
  ring

lemma lower_bound (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (t : ℕ) (ht : t < sigma.1.val) (P : Population n mu)
    (hP : ∀ u, (Sampling.zeros (P u)).card = k) (hf : ∀ b : Fin 2, 0 < fraction i b P) :
    -(a * (3 : ℝ) ^ k + (3 : ℝ) ^ k * (((k : ℝ) + 1) + fraction i 1 P / fraction i 0 P) / n) /
      ((mu : ℕ) + 1 : ℝ) ≤ drift sigma pc i 1 a t P - drift sigma pc i 0 a t P := by
  have hn2 : 2 ≤ n := by omega
  have hy (b : Fin 2) : 0 < average P (liftClass (field sigma i b a t)) :=
    (hf b).trans_le (GroupSampling.average_one_lower P hP _ (field_one sigma i b ha t))
  have hr (b : Fin 2) := field_average_ratio hk hn sigma i b ha horizon t ht P (hy b)
  have hb1 := BiasNormalization.mutant_bound hn2 pc hpc P hP i (field sigma i 1 a (t + 1))
    ((3 : ℝ) ^ k) _ (by positivity) (hy 1)
    (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i 1 ha (t + 1) x))
    (field_ratio hk hn sigma i 1 ha horizon (t + 1)) (average_field_step P sigma i 1 ha t ht) (hf 1)
  have hb0 := BiasNormalization.resident_bound hn2 pc hpc P hP i (field sigma i 0 a (t + 1))
    ((3 : ℝ) ^ k) _ (by positivity) (hy 0)
    (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i 0 ha (t + 1) x))
    (field_ratio hk hn sigma i 0 ha horizon (t + 1)) (average_field_step P sigma i 0 ha t ht) (hf 0)
  rw [drift_eq, drift_eq]
  norm_num only [bias, Fin.zero_ne_one, if_false, if_true]
  apply scalar_difference (by positivity) (scalar_bound hn2 pc hpc P)
  · exact ⟨by linarith [(hr 1).2.2], (hr 1).2.1⟩
  · exact ⟨by linarith [(hr 0).2.2], (hr 0).2.1⟩
  · exact hb1.1
  · exact hb0.2

lemma mutant_abs (hk : 2 ≤ k) (hn : 4 * k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (t : ℕ) (ht : t < sigma.1.val) (P : Population n mu)
    (hP : ∀ u, (Sampling.zeros (P u)).card = k) (hf : 0 < fraction i 1 P)
    (hbias : (3 : ℝ) ^ k * ((k : ℝ) + 1) / n ≤ 1) :
    |drift sigma pc i 1 a t P| ≤ 2 / ((mu : ℕ) + 1 : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hy : 0 < average P (liftClass (field sigma i 1 a t)) :=
    hf.trans_le (GroupSampling.average_one_lower P hP _ (field_one sigma i 1 ha t))
  have hr := field_average_ratio hk hn sigma i 1 ha horizon t ht P hy
  have hb := BiasNormalization.mutant_bound hn2 pc hpc P hP i (field sigma i 1 a (t + 1))
    ((3 : ℝ) ^ k) _ (by positivity) hy
    (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i 1 ha (t + 1) x))
    (field_ratio hk hn sigma i 1 ha horizon (t + 1)) (average_field_step P sigma i 1 ha t ht) hf
  have hprod := mul_le_mul (scalar_bound (k := k) hn2 pc hpc P)
    (show |average P (liftClass (field sigma i 1 a (t + 1))) / average P (liftClass (field sigma i 1 a t))| ≤ 1 by
      rw [abs_of_nonneg hr.1]; exact hr.2.1) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [← abs_mul, one_mul] at hprod
  rw [drift_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (mu : ℕ) + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_num only [bias, if_true]
  have habs := abs_add_le ((copyWeight n pc - viability k pc P) *
    (average P (liftClass (field sigma i 1 a (t + 1))) / average P (liftClass (field sigma i 1 a t))))
    (mutantBias pc P i (liftClass (field sigma i 1 a (t + 1))) / average P (liftClass (field sigma i 1 a t)))
  rw [abs_of_nonneg hb.1] at habs
  linarith

end
end Lax343628Proofs.DriftCancellation
