import Lax343628Proofs.RunLogOdds

namespace Lax343628Proofs.FieldDrift

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseDynamics Lax343628Proofs.SparseEnvironment
open Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassMeanDynamics Lax343628Proofs.ClassChannels
open Lax343628Proofs.FiniteDrift Lax343628Proofs.AveragedOperators
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu rs : ℕ+}

lemma scalar_bound (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (P : Population n mu) :
    |copyWeight n pc - viability k pc P| ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) ∧ 1 - 1 / (n : ℝ) ≤ 1 := by
    constructor
    · have hdiv : 1 / (n : ℝ) ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < n)).mpr (by linarith)
      linarith
    · have hh : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
  have hpow : 0 ≤ (1 - 1 / (n : ℝ)) ^ n ∧ (1 - 1 / (n : ℝ)) ^ n ≤ 1 :=
    ⟨pow_nonneg hbase.1 _, pow_le_one₀ hbase.1 hbase.2⟩
  have hcopy : 0 ≤ copyWeight n pc ∧ copyWeight n pc ≤ 1 := by
    unfold copyWeight
    constructor
    · exact mul_nonneg (by linarith) hpow.1
    · nlinarith [mul_nonneg hpc.1 hpow.1]
  have hv : 0 ≤ viability k pc P ∧ viability k pc P ≤ 1 := by
    constructor
    · exact mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num)
    · exact (mean_mono _ (fun _ ↦ by split_ifs <;> norm_num)).trans_eq (mean_const _ 1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma field_average_recurrence (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2)
    (a : ℝ) (t : ℕ) (ht : t < sigma.1.val) (P : Population n mu) :
    average P (liftClass (field sigma i b a t)) =
      average P (liftClass (field sigma i b a (t + 1))) +
        a * fieldAction P (mixedKernel (path sigma t)) (field sigma i b a (t + 1)) := by
  have hfield : field sigma i b a t = (fun x ↦ field sigma i b a (t + 1) x +
      a * ReproductiveValues.action (mixedKernel (path sigma t)) (field sigma i b a (t + 1)) x) :=
    funext (field_step sigma i b a t ht)
  rw [hfield]
  exact average_lift_linear P _ _ a

lemma field_average_ratio (hk : 2 ≤ k) (hn : 4 * k ≤ n)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (t : ℕ) (ht : t < sigma.1.val) (P : Population n mu)
    (hy : 0 < average P (liftClass (field sigma i b a t))) :
    0 ≤ average P (liftClass (field sigma i b a (t + 1))) / average P (liftClass (field sigma i b a t)) ∧
    average P (liftClass (field sigma i b a (t + 1))) / average P (liftClass (field sigma i b a t)) ≤ 1 ∧
    1 - average P (liftClass (field sigma i b a (t + 1))) / average P (liftClass (field sigma i b a t)) ≤ a * (3 : ℝ) ^ k := by
  have hf := average_field_step P sigma i b ha t ht
  have hnon : 0 ≤ average P (liftClass (field sigma i b a (t + 1))) :=
    mean_nonneg _ (fun _ ↦ lift_field_nonneg sigma i b ha (t + 1) _)
  have hb := fieldAction_bound P (mixedKernel (path sigma t)) (field sigma i b a (t + 1)) ((3 : ℝ) ^ k)
    (by positivity) (fun x ↦ le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i b ha (t + 1) x))
    (field_ratio hk hn sigma i b ha horizon (t + 1))
  refine ⟨div_nonneg hnon hy.le, (div_le_one hy).mpr hf, ?_⟩
  have hr := field_average_recurrence sigma i b a t ht P
  have hmul := mul_le_mul_of_nonneg_left hb.2 ha
  have hmul' := mul_le_mul_of_nonneg_left hf (mul_nonneg ha (by positivity : (0 : ℝ) ≤ 3 ^ k))
  have hh : average P (liftClass (field sigma i b a t)) -
      average P (liftClass (field sigma i b a (t + 1))) ≤ a * (3 : ℝ) ^ k * average P (liftClass (field sigma i b a t)) := by
    nlinarith
  have hd := (div_le_iff₀ hy).mpr hh
  simpa only [sub_div, div_self hy.ne'] using hd

end
end Lax343628Proofs.FieldDrift
