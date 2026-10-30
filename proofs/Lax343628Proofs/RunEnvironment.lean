import Lax343628Proofs.EmpiricalStability
import Lax343628Proofs.SparseKernelSampling

namespace Lax343628Proofs.RunEnvironment

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.Genotypes Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.WeightedKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.EmpiricalStability Lax343628Proofs.SparseGroups
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def groupLaw (G : Finset ℕ) [Nonempty G] (P : ℕ → Population n mu)
    (hP : ∀ t ∈ G, ∀ u, (Sampling.zeros (P t u)).card = k) : PMF (Genotype n k) :=
  (PMF.uniformOfFintype G).bind (fun t ↦ (PMF.uniformOfFintype (Fin (mu : ℕ))).map
    (fun u ↦ ofString (P t.val u) (hP t.val t.property u)))

lemma groupLaw_mean (G : Finset ℕ) [Nonempty G] (P : ℕ → Population n mu)
    (hP : ∀ t ∈ G, ∀ u, (Sampling.zeros (P t u)).card = k) (f : BitString n → ℝ) :
    mean ((groupLaw G P hP).map Genotypes.toString) f =
      mean (PMF.uniformOfFintype G) (fun t ↦ average (P t.val) f) := by
  rw [mean_map, groupLaw, mean_bind]
  simp only [mean_map, toString_ofString]
  rfl

lemma groupLaw_action {i : Fin n} {b : Fin 2} (G : Finset ℕ) [Nonempty G]
    (P : ℕ → Population n mu) (hP : ∀ t ∈ G, ∀ u, (Sampling.zeros (P t u)).card = k)
    (h : ColumnClass n k i b → ℝ) (x : ColumnClass n k i b) :
    ReproductiveValues.action (mixedKernel ((groupLaw G P hP).map Genotypes.toString)) h x =
      mean (PMF.uniformOfFintype G) (fun t ↦ ReproductiveValues.action (mixedKernel (empirical (P t.val))) h x) := by
  rw [mixed_action, groupLaw_mean]
  congr 1
  funext t
  rw [mixed_action, empirical, mean_map]
  rfl

lemma scalar_steps (g : ℕ → ℝ) (C : ℝ) (H s u : ℕ) (hsu : s + u ≤ H)
    (hstep : ∀ t, t < H → |g (t + 1) - g t| ≤ C) : |g (s + u) - g s| ≤ u * C := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hu : s + u ≤ H := by omega
    have hh := abs_sub_le (g (s + (u + 1))) (g (s + u)) (g s)
    have hi := ih hu
    have hs := hstep (s + u) (by omega)
    rw [show s + u + 1 = s + (u + 1) by omega] at hs
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

lemma kernel_steps {i : Fin n} {b : Fin 2} (P : ℕ → Population n mu) (E : ℕ → Event n mu)
    (H : ℕ) (hnext : ∀ t, t < H → P (t + 1) = next k (P t) (E t))
    (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M)
    (s u : ℕ) (hsu : s + u ≤ H) (x : ColumnClass n k i b) :
    |ReproductiveValues.action (mixedKernel (empirical (P (s + u)))) h x -
      ReproductiveValues.action (mixedKernel (empirical (P s))) h x| ≤ u * (M / (mu : ℕ)) := by
  apply scalar_steps (fun t ↦ ReproductiveValues.action (mixedKernel (empirical (P t))) h x)
    (M / (mu : ℕ)) H s u hsu
  intro t ht
  rw [hnext t ht]
  exact kernel_step_abs (P t) (E t) h M hM hh x

lemma group_kernel_difference {i : Fin n} {b : Fin 2} (P : ℕ → Population n mu) (E : ℕ → Event n mu)
    (H ell j : ℕ) (hell : 1 ≤ ell) [Nonempty (group H ell j)]
    (hnext : ∀ t, t < H → P (t + 1) = next k (P t) (E t))
    (hP : ∀ t ∈ group H ell j, ∀ u, (Sampling.zeros (P t u)).card = k)
    (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M)
    (s : ℕ) (hs : s ∈ group H ell j) (x : ColumnClass n k i b) :
    |ReproductiveValues.action (mixedKernel (empirical (P s))) h x -
      ReproductiveValues.action (mixedKernel ((groupLaw (group H ell j) P hP).map Genotypes.toString)) h x| ≤
        ell * (M / (mu : ℕ)) := by
  have hC : 0 ≤ M / (mu : ℕ) := by positivity
  have hpoint (t : group H ell j) :
      |ReproductiveValues.action (mixedKernel (empirical (P s))) h x -
        ReproductiveValues.action (mixedKernel (empirical (P t.val))) h x| ≤ ell * (M / (mu : ℕ)) := by
    have hbS := group_member_bounds H ell j s hell hs
    have hbT := group_member_bounds H ell j t.val hell t.property
    have hsH : s ≤ H := by have hh := hbS.1.trans_le hbS.2.1; omega
    have htH : t.val ≤ H := by have hh := hbT.1.trans_le hbT.2.1; omega
    by_cases hst : s ≤ t.val
    · have hdiff : t.val - s ≤ ell := by omega
      have hl := kernel_steps P E H hnext h M hM hh s (t.val - s) (by omega) x
      rw [Nat.add_sub_of_le hst, abs_sub_comm] at hl
      exact hl.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hdiff) hC)
    · have hts : t.val ≤ s := by omega
      have hdiff : s - t.val ≤ ell := by omega
      have hl := kernel_steps P E H hnext h M hM hh t.val (s - t.val) (by omega) x
      rw [Nat.add_sub_of_le hts] at hl
      exact hl.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hdiff) hC)
  rw [groupLaw_action]
  have heq : ReproductiveValues.action (mixedKernel (empirical (P s))) h x -
      mean (PMF.uniformOfFintype (group H ell j))
        (fun t ↦ ReproductiveValues.action (mixedKernel (empirical (P t.val))) h x) =
      mean (PMF.uniformOfFintype (group H ell j)) (fun t ↦
        ReproductiveValues.action (mixedKernel (empirical (P s))) h x -
          ReproductiveValues.action (mixedKernel (empirical (P t.val))) h x) := by
    rw [mean_sub, mean_const]
  rw [heq]
  exact (abs_mean_le _ _).trans ((mean_mono _ hpoint).trans_eq (mean_const _ _))

end
end Lax343628Proofs.RunEnvironment
