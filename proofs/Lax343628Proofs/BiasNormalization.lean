import Lax343628Proofs.FieldDrift

namespace Lax343628Proofs.BiasNormalization

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassBiasBounds Lax343628Proofs.ClassMeanDynamics
open Lax343628Proofs.ClassChannels Lax343628Proofs.WeightedFieldControl
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+} {i : Fin n} {b : Fin 2}

lemma lift_zero (h : ColumnClass n k i b → ℝ) (z : BitString n)
    (hz : (Sampling.zeros z).card ≠ k) : liftClass h z = 0 := by
  unfold liftClass
  rw [dif_neg (by tauto)]

lemma mutant_bound (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k) (i : Fin n)
    (h : ColumnClass n k i 1 → ℝ) (D y : ℝ) (hD : 0 ≤ D) (hy : 0 < y)
    (hh : ∀ x, 0 ≤ h x) (hratio : ∀ x z, h z ≤ D * h x)
    (havg : average P (liftClass h) ≤ y) (hf : 0 < fraction i 1 P) :
    0 ≤ mutantBias pc P i (liftClass h) / y ∧
      mutantBias pc P i (liftClass h) / y ≤ D * ((k : ℝ) + 1) / n := by
  let M := D * y / fraction i 1 P
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound (x : ColumnClass n k i 1) : 0 ≤ h x ∧ h x ≤ M :=
    ⟨hh x, child_bound P hP h D y hD hratio havg hf x⟩
  have hb := mutant_bias_bound hn pc hpc P hP i (liftClass h) M hM
    (ColumnFieldBounds.lift_bounds h M hM hbound) (ColumnFieldBounds.lift_bit h) (lift_zero h)
  refine ⟨div_nonneg hb.1 hy.le, ?_⟩
  have heq : fraction i 1 P * M * ((k : ℝ) + 1) / n / y = D * ((k : ℝ) + 1) / n := by
    dsimp [M]
    field_simp
  exact (div_le_div_of_nonneg_right hb.2 hy.le).trans_eq heq

lemma resident_bound (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k) (i : Fin n)
    (h : ColumnClass n k i 0 → ℝ) (D y : ℝ) (hD : 0 ≤ D) (hy : 0 < y)
    (hh : ∀ x, 0 ≤ h x) (hratio : ∀ x z, h z ≤ D * h x)
    (havg : average P (liftClass h) ≤ y) (hf : 0 < fraction i 0 P) :
    0 ≤ residentBias k pc P i (liftClass h) / y ∧
      residentBias k pc P i (liftClass h) / y ≤
        D * (((k : ℝ) + 1) + fraction i 1 P / fraction i 0 P) / n := by
  let M := D * y / fraction i 0 P
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound (x : ColumnClass n k i 0) : 0 ≤ h x ∧ h x ≤ M :=
    ⟨hh x, child_bound P hP h D y hD hratio havg hf x⟩
  have hb := resident_bias_bound hn pc hpc P hP i (liftClass h) M hM
    (ColumnFieldBounds.lift_bounds h M hM hbound) (ColumnFieldBounds.lift_bit h) (lift_zero h)
  refine ⟨div_nonneg hb.1 hy.le, ?_⟩
  have heq : M * (fraction i 0 P * ((k : ℝ) + 1) + fraction i 1 P) / n / y =
      D * (((k : ℝ) + 1) + fraction i 1 P / fraction i 0 P) / n := by
    dsimp [M]
    field_simp
  exact (div_le_div_of_nonneg_right hb.2 hy.le).trans_eq heq

end
end Lax343628Proofs.BiasNormalization
