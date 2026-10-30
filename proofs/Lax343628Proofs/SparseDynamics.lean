import Lax343628Proofs.SparseNoise
import Lax343628Proofs.MismatchTotals
import Lax343628Proofs.PlateauKernelApproximation

namespace Lax343628Proofs.SparseDynamics

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassMeanDynamics Lax343628Proofs.ClassIncrements
open Lax343628Proofs.FiniteDrift Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.AveragedOperators Lax343628Proofs.ChannelNoise
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {mu : ℕ+} {rs : ℕ+}

def bias (pc : ℝ) (P : Population n mu) (i : Fin n) (b : Fin 2) (psi : BitString n → ℝ) : ℝ :=
  if b = 1 then mutantBias pc P i psi else residentBias k pc P i psi

lemma lift_off_plateau (hkn : k ≤ n) {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (z : BitString n) (hz : ¬ PlateauDynamics.onPlateau k z) :
    liftClass h z = 0 := by
  unfold liftClass
  split_ifs with hclass
  · exact False.elim (hz (PlateauKernelApproximation.plateau_of_zero_card hkn z hclass.1))
  · rfl

lemma mean_formula (hkn : k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (i : Fin n) (b : Fin 2) (h : ColumnClass n k i b → ℝ) :
    ((mu : ℕ) + 1 : ℝ) * mean (eventLaw pc P) (nonImmChange k i (liftClass h) P) =
      (mu : ℕ) * (pc * fieldAction P (mixedKernel (EmpiricalKernels.empirical P)) h +
        (copyWeight n pc - viability k pc P) * average P (liftClass h) + bias (k := k) pc P i b (liftClass h)) := by
  have hplat : PlateauDynamics.plateauPopulation k P := fun u ↦
    PlateauKernelApproximation.plateau_of_zero_card hkn (P u) (hP u)
  rw [actual_fieldAction P hP, ← ClassAverages.ownCross_operator P hP]
  fin_cases b
  · norm_num [bias]
    exact
      resident_mean hkn pc hpc P hplat i (liftClass h) (ColumnFieldBounds.lift_bit h) (lift_off_plateau hkn h)
  · norm_num [bias]
    exact
      mutant_mean hkn pc hpc P hplat i (liftClass h) (ColumnFieldBounds.lift_bit h) (lift_off_plateau hkn h)

def drift (sigma : Net n k R (count R ell) rs) (pc : ℝ) (i : Fin n) (b : Fin 2)
    (a : ℝ) (t : ℕ) (P : Population n mu) : ℝ :=
  ((copyWeight n pc - viability k pc P) * average P (liftClass (field sigma i b a (t + 1))) +
    bias (k := k) pc P i b (liftClass (field sigma i b a (t + 1)))) /
      (((mu : ℕ) + 1 : ℝ) * average P (liftClass (field sigma i b a t)))

def imm (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2)
    (a : ℝ) (t : ℕ) (P : Population n mu) (E : Event n mu) : ℝ :=
  (change k (liftClass (field sigma i b a (t + 1))) P E -
    nonImmChange k i (liftClass (field sigma i b a (t + 1))) P E) /
      ((mu : ℕ) * average P (liftClass (field sigma i b a t)))

lemma normalized_step (hkn : k ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2) (a : ℝ)
    (ha : a = pc / ((mu : ℕ) + 1 : ℝ)) (t : ℕ) (ht : t < sigma.1.val)
    (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k) (E : Event n mu) :
    (average (next k P E) (liftClass (field sigma i b a (t + 1))) -
      average P (liftClass (field sigma i b a t))) / average P (liftClass (field sigma i b a t)) =
        drift sigma pc i b a t P +
        a * difference P (mixedKernel (EmpiricalKernels.empirical P)) (mixedKernel (path sigma t))
          (field sigma i b a (t + 1)) / average P (liftClass (field sigma i b a t)) +
        SparseNoise.noise sigma pc i b a t P E + imm sigma i b a t P E := by
  have hmean := mean_formula hkn pc hpc P hP i b (field sigma i b a (t + 1))
  have hrec : average P (liftClass (field sigma i b a t)) =
      average P (liftClass (field sigma i b a (t + 1))) +
        a * fieldAction P (mixedKernel (path sigma t)) (field sigma i b a (t + 1)) := by
    have hfield : field sigma i b a t = (fun x ↦ field sigma i b a (t + 1) x +
        a * ReproductiveValues.action (mixedKernel (path sigma t)) (field sigma i b a (t + 1)) x) :=
      funext (field_step sigma i b a t ht)
    rw [hfield]
    exact average_lift_linear P _ _ a
  have hchange := average_change (k := k) (liftClass (field sigma i b a (t + 1))) P E
  have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hd : ((mu : ℕ) + 1 : ℝ) ≠ 0 := by positivity
  have hmean' : mean (eventLaw pc P) (nonImmChange k i (liftClass (field sigma i b a (t + 1))) P) =
      (mu : ℕ) * (pc * fieldAction P (mixedKernel (EmpiricalKernels.empirical P)) (field sigma i b a (t + 1)) +
        (copyWeight n pc - viability k pc P) * average P (liftClass (field sigma i b a (t + 1))) +
        bias (k := k) pc P i b (liftClass (field sigma i b a (t + 1)))) / ((mu : ℕ) + 1 : ℝ) := by
    apply (eq_div_iff hd).mpr
    nlinarith [hmean]
  unfold drift imm difference SparseNoise.noise NormalizedClassNoise.fieldNoise NoiseNormalization.noise centered
  rw [if_pos ht, hmean']
  rw [show average (next k P E) (liftClass (field sigma i b a (t + 1))) =
    average P (liftClass (field sigma i b a (t + 1))) + change k (liftClass (field sigma i b a (t + 1))) P E / (mu : ℕ) by linarith [hchange]]
  by_cases hy : average P (liftClass (field sigma i b a t)) = 0
  · simp only [hy, mul_zero, div_zero, add_zero]
  · field_simp [hm.ne', hd, hy]
    rw [hrec, ha]
    field_simp [hd]
    ring

lemma lift_field_nonneg (sigma : Net n k R (count R ell) rs) (i : Fin n) (b : Fin 2)
    {a : ℝ} (ha : 0 ≤ a) (t : ℕ) (z : BitString n) :
    0 ≤ liftClass (field sigma i b a t) z := by
  unfold liftClass
  split_ifs
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (field_one sigma i b ha t _)
  · rfl

lemma imm_mutant_nonneg (sigma : Net n k R (count R ell) rs) (i : Fin n)
    {a : ℝ} (ha : 0 ≤ a) (t : ℕ) (P : Population n mu) (E : Event n mu) (hkn : k ≤ n) :
    0 ≤ imm sigma i 1 a t P E := by
  apply div_nonneg
  · exact ImmigrationMean.mutant_sign i _ (lift_field_nonneg sigma i 1 ha (t + 1))
      (ColumnFieldBounds.lift_bit _) (lift_off_plateau hkn _) P E
  · exact mul_nonneg (Nat.cast_nonneg _) (mean_nonneg _ (fun _ ↦ lift_field_nonneg sigma i 1 ha t _))

lemma imm_resident_nonpos (sigma : Net n k R (count R ell) rs) (i : Fin n)
    {a : ℝ} (ha : 0 ≤ a) (t : ℕ) (P : Population n mu) (E : Event n mu) :
    imm sigma i 0 a t P E ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · exact ImmigrationMean.resident_sign i _ (lift_field_nonneg sigma i 0 ha (t + 1))
      (ColumnFieldBounds.lift_bit _) P E
  · exact mul_nonneg (Nat.cast_nonneg _) (mean_nonneg _ (fun _ ↦ lift_field_nonneg sigma i 0 ha t _))

end
end Lax343628Proofs.SparseDynamics
