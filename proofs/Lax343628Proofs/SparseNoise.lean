import Lax343628Proofs.SparseFields
import Lax343628Proofs.NormalizedClassNoise
import Lax343628Proofs.DrivenNoise

namespace Lax343628Proofs.SparseNoise

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.NormalizedClassNoise Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels Lax343628Proofs.FiniteDrift Lax343628Proofs.TaggedDynamics
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

def noise (sigma : Net n k R (count R ell) rs) (pc : ℝ) (i : Fin n) (b : Fin 2) (a : ℝ)
    (t : ℕ) (P : Population n mu) (E : Event n mu) : ℝ :=
  if t < sigma.1.val then fieldNoise (k := k) pc P i (liftClass (field sigma i b a (t + 1)))
    (average P (liftClass (field sigma i b a t))) E else 0

lemma mean_noise (sigma : Net n k R (count R ell) rs) (pc : ℝ) (i : Fin n) (b : Fin 2) (a : ℝ)
    (t : ℕ) (P : Population n mu) : mean (eventLaw pc P) (noise sigma pc i b a t P) = 0 := by
  change mean _ (fun E ↦ if t < sigma.1.val then fieldNoise (k := k) pc P i
    (liftClass (field sigma i b a (t + 1))) (average P (liftClass (field sigma i b a t))) E else 0) = 0
  by_cases ht : t < sigma.1.val
  · simp only [if_pos ht]
    exact NoiseNormalization.mean_noise _ _ _ _
  · simp only [if_neg ht, mean_const]

lemma mutant_bounds (hk : 2 ≤ k) (hn : 4 * k ≤ n) (sigma : Net n k R (count R ell) rs)
    (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (a : ℝ) (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (ref : ColumnClass n k i 1) (fmin : ℝ) (hfmin : 0 < fmin) (hf : fmin ≤ fraction i 1 P) (t : ℕ) :
    (∀ E, |noise sigma pc i 1 a t P E| ≤ 4 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * fmin)) ∧
      mean (eventLaw pc P) (fun E ↦ noise sigma pc i 1 a t P E ^ 2) ≤
        3 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * fmin) := by
  by_cases ht : t < sigma.1.val
  · have hD : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hbound := mutant_normalized pc hpc P hP (field sigma i 1 a (t + 1)) ref ((3 : ℝ) ^ k) fmin
      (average P (liftClass (field sigma i 1 a t))) hD hfmin hf
      (field_one sigma i 1 ha (t + 1)) (field_ratio hk hn sigma i 1 ha horizon (t + 1))
      (average_field_step P sigma i 1 ha t ht)
    simpa only [noise, if_pos ht] using hbound
  · constructor
    · intro E; simp only [noise, if_neg ht, abs_zero]; positivity
    · simp only [noise, if_neg ht, zero_pow (by decide : (2 : ℕ) ≠ 0), mean_const]; positivity

lemma resident_bounds (hk : 2 ≤ k) (hn : 4 * k ≤ n) (sigma : Net n k R (count R ell) rs)
    (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (a : ℝ) (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (ref : ColumnClass n k i 0) (amin : ℝ) (hamin : 0 < amin) (hf : amin ≤ fraction i 0 P)
    (himm : fraction i 1 P / n ≤ fraction i 0 P) (t : ℕ) :
    (∀ E, |noise sigma pc i 0 a t P E| ≤ 5 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * amin)) ∧
      mean (eventLaw pc P) (fun E ↦ noise sigma pc i 0 a t P E ^ 2) ≤
        4 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * amin) := by
  by_cases ht : t < sigma.1.val
  · have hD : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hbound := resident_normalized pc hpc P hP (field sigma i 0 a (t + 1)) ref ((3 : ℝ) ^ k) amin
      (average P (liftClass (field sigma i 0 a t))) hD hamin hf
      (field_one sigma i 0 ha (t + 1)) (field_ratio hk hn sigma i 0 ha horizon (t + 1))
      (average_field_step P sigma i 0 ha t ht) himm
    simpa only [noise, if_pos ht] using hbound
  · constructor
    · intro E; simp only [noise, if_neg ht, abs_zero]; positivity
    · simp only [noise, if_neg ht, zero_pow (by decide : (2 : ℕ) ≠ 0), mean_const]; positivity

end
end Lax343628Proofs.SparseNoise
