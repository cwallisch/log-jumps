import Lax343628Proofs.ClassMeanDynamics

namespace Lax343628Proofs.ClassBiasBounds

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ClassMeanDynamics Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassBirth Lax343628Proofs.ClassChannels
open Lax343628Proofs.ImmigrationMean Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma clone_bias_bound (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k) (i : Fin n) (b : Fin 2)
    (ψ : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ M)
    (hbit : ∀ z, z i ≠ b → ψ z = 0) (hzero : ∀ z, (zeros z).card ≠ k → ψ z = 0) :
    0 ≤ cloneBias pc P i b ψ ∧ cloneBias pc P i b ψ ≤ M * k / n * fraction i b P := by
  have he := own_clone_error hn P hP i b ψ M hM hh hbit hzero
  unfold cloneBias
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hpc.2) he.1
  · nlinarith [mul_nonneg hpc.1 he.1]

lemma mutant_bias_bound (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k) (i : Fin n)
    (ψ : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ M)
    (hbit : ∀ z, z i ≠ 1 → ψ z = 0) (hzero : ∀ z, (zeros z).card ≠ k → ψ z = 0) :
    0 ≤ mutantBias pc P i ψ ∧ mutantBias pc P i ψ ≤ fraction i 1 P * M * ((k : ℝ) + 1) / n := by
  have hc := clone_bias_bound hn pc hpc P hP i 1 ψ M hM hh hbit hzero
  have hG := from_opposite_bound pc hpc P i 1 ψ M hM hh hbit
  have hf := fraction_bounds i 1 P
  have hMdiv : 0 ≤ M / (n : ℝ) := by positivity
  have hG' : fromOpposite pc P i 1 ψ ≤ M / n := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hG' hf.1
  unfold mutantBias
  constructor
  · exact add_nonneg hc.1 (mul_nonneg hf.1 hG.1)
  · have heq : fraction i 1 P * M * ((k : ℝ) + 1) / n =
        M * k / n * fraction i 1 P + fraction i 1 P * (M / n) := by ring
    rw [heq]
    linarith

lemma mutantAccept_bounds (i : Fin n) (z : BitString n) :
    0 ≤ mutantAccept k i z ∧ mutantAccept k i z ≤ 1 := by
  unfold mutantAccept
  split_ifs <;> norm_num

lemma mutantAccept_bit (i : Fin n) (z : BitString n) (hz : z i ≠ 1) : mutantAccept k i z = 0 := by
  simp only [mutantAccept, and_false, hz, if_false]

lemma resident_bias_bound (hn : 2 ≤ n) (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k) (i : Fin n)
    (ψ : BitString n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ M)
    (hbit : ∀ z, z i ≠ 0 → ψ z = 0) (hzero : ∀ z, (zeros z).card ≠ k → ψ z = 0) :
    0 ≤ residentBias k pc P i ψ ∧ residentBias k pc P i ψ ≤
      M * (fraction i 0 P * ((k : ℝ) + 1) + fraction i 1 P) / n := by
  have hc := clone_bias_bound hn pc hpc P hP i 0 ψ M hM hh hbit hzero
  have hG := from_opposite_bound pc hpc P i 0 ψ M hM hh hbit
  have hI := from_opposite_bound pc hpc P i 1 (mutantAccept k i) 1 (by norm_num)
    (mutantAccept_bounds i) (mutantAccept_bit i)
  have hs := fraction_sum i P
  have hA : 0 ≤ average P ψ ∧ average P ψ ≤ M := by
    constructor
    · exact mean_nonneg _ (fun u ↦ (hh _).1)
    · exact (mean_mono _ (fun u ↦ (hh (P u)).2)).trans_eq (mean_const _ M)
  have ha0 : 1 - fraction i 0 P = fraction i 1 P := by linarith
  have ha1 : 1 - fraction i 1 P = fraction i 0 P := by linarith
  have hG' : fromOpposite pc P i 0 ψ ≤ M / n * fraction i 1 P := by simpa only [ha0] using hG.2
  have hI' : fromOpposite pc P i 1 (mutantAccept k i) ≤ fraction i 0 P / n := by
    have heq : (1 / (n : ℝ)) * (1 - fraction i 1 P) = fraction i 0 P / n := by rw [ha1]; ring
    simpa only [heq] using hI.2
  have hprod : fromOpposite pc P i 1 (mutantAccept k i) * average P ψ ≤ fraction i 0 P / n * M :=
    (mul_le_mul_of_nonneg_right hI' hA.1).trans
      (mul_le_mul_of_nonneg_left hA.2 (by have hf := (fraction_bounds i 0 P).1; positivity))
  unfold residentBias
  constructor
  · exact add_nonneg (add_nonneg hc.1 hG.1) (mul_nonneg hI.1 hA.1)
  · have heq : M * (fraction i 0 P * ((k : ℝ) + 1) + fraction i 1 P) / n =
        M * k / n * fraction i 0 P + M / n * fraction i 1 P + fraction i 0 P / n * M := by ring
    rw [heq]
    linarith

end
end Lax343628Proofs.ClassBiasBounds
