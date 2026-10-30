import Lax343628Proofs.RunMismatch
import Lax343628Proofs.RunPartnerLaws

namespace Lax343628Proofs.MismatchTotals

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels Lax343628Proofs.SparseEnvironment
open Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields Lax343628Proofs.SparseSampling
open Lax343628Proofs.SparseKernelSampling Lax343628Proofs.RunPartnerLaws
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.AveragedOperators
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.TaggedDynamics
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

def cost (mu ell : ℕ) (a D : ℝ) : ℝ := (ell : ℝ) / mu * D + (2 * ell * a) * D + (2 * ell * a) * D ^ 2

def mismatch (sigma : Net n k R (count R ell) rs) (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2)
    (a : ℝ) (t : ℕ) : ℝ := a * difference (P t) (mixedKernel (empirical (P t)))
      (mixedKernel (path sigma t)) (field sigma i b a (t + 1)) /
        average (P t) (liftClass (field sigma i b a t))

def total (H : Fin (R + 1)) (env : Lists n k (count R ell) rs) (P : ℕ → Population n mu)
    (i : Fin n) (b : Fin 2) (a : ℝ) : ℝ := ∑ j : Fin (count R ell),
  |∑ t ∈ group H.val ell j.val, mismatch (H, env) P i b a t|

lemma group_bound [Nonempty (Genotypes.Genotype n k)]
    (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (env : Lists n k (count R ell) rs) (i : Fin n) (b : Fin 2)
    {a : ℝ} (ha : 0 ≤ a) (hcell : (ell : ℝ) * a ≤ 1)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = next k (P t) (E t))
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < H.val → 0 < fraction i b (P t)) (j : Fin (count R ell)) :
    |∑ t ∈ group H.val ell j.val, mismatch (H, env) P i b a t| ≤
      a * (group H.val ell j.val).card * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
        |samplingError H P i b a (laws H P hP) env j| := by
  by_cases hG : (group H.val ell j.val).Nonempty
  · let : Nonempty (group H.val ell j.val) := ⟨⟨Classical.choose hG, Classical.choose_spec hG⟩⟩
    let hPG : ∀ s ∈ group H.val ell j.val, ∀ u, (Sampling.zeros (P s u)).card = k :=
      fun s hs u ↦ hP s (member_time hs) u
    have hlaws := laws_nonempty H P hP j
    have hstep (t : ℕ) (ht : t ∈ group H.val ell j.val) :
        |mismatch (H, env) P i b a t + a *
          ((fieldAction (P t) (mixedKernel (partnerLaw (env j))) (terminalFields H i b a j env) -
            fieldAction (P t) (mixedKernel (((laws H P hP) j).map Genotypes.toString)) (terminalFields H i b a j env)) /
              average (P t) (liftClass (terminalFields H i b a j env)))| ≤
          a * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) := by
      have hp := RunMismatch.point_bound hk hn hell H env i b ha hcell horizon P E hnext j hPG t ht (hf t (member_time ht))
      have heq : mismatch (H, env) P i b a t + a *
          ((fieldAction (P t) (mixedKernel (partnerLaw (env j))) (terminalFields H i b a j env) -
            fieldAction (P t) (mixedKernel (((laws H P hP) j).map Genotypes.toString)) (terminalFields H i b a j env)) /
              average (P t) (liftClass (terminalFields H i b a j env))) = a *
          (difference (P t) (mixedKernel (empirical (P t))) (mixedKernel (partnerLaw (env j)))
              (field (H, env) i b a (t + 1)) / average (P t) (liftClass (field (H, env) i b a t)) -
            difference (P t) (mixedKernel ((RunEnvironment.groupLaw (group H.val ell j.val) P hPG).map Genotypes.toString))
              (mixedKernel (partnerLaw (env j))) (terminalFields H i b a j env) /
                average (P t) (liftClass (terminalFields H i b a j env))) := by
        rw [mismatch, path_group H env j t ht, hlaws]
        unfold difference
        ring
      rw [heq, abs_mul, abs_of_nonneg ha]
      exact mul_le_mul_of_nonneg_left hp ha
    have hgroup : |(∑ t ∈ group H.val ell j.val, mismatch (H, env) P i b a t) +
        samplingError H P i b a (laws H P hP) env j| ≤
        a * (group H.val ell j.val).card * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) := by
      unfold samplingError
      calc
        _ = |∑ t ∈ group H.val ell j.val, (mismatch (H, env) P i b a t + a *
            ((fieldAction (P t) (mixedKernel (partnerLaw (env j))) (terminalFields H i b a j env) -
              fieldAction (P t) (mixedKernel (((laws H P hP) j).map Genotypes.toString)) (terminalFields H i b a j env)) /
                average (P t) (liftClass (terminalFields H i b a j env))))| := by
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t ∈ group H.val ell j.val, a * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) :=
          Finset.sum_le_sum hstep
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    have hs := abs_sub ((∑ t ∈ group H.val ell j.val, mismatch (H, env) P i b a t) +
      samplingError H P i b a (laws H P hP) env j) (samplingError H P i b a (laws H P hP) env j)
    have heq : ((∑ t ∈ group H.val ell j.val, mismatch (H, env) P i b a t) +
      samplingError H P i b a (laws H P hP) env j) - samplingError H P i b a (laws H P hP) env j =
        ∑ t ∈ group H.val ell j.val, mismatch (H, env) P i b a t := by ring
    rw [heq] at hs
    linarith
  · have hG0 : group H.val ell j.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    simp only [hG0, Finset.sum_empty, abs_zero, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul,
      samplingError, add_zero, le_refl]

lemma total_bound [Nonempty (Genotypes.Genotype n k)]
    (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (env : Lists n k (count R ell) rs) (i : Fin n) (b : Fin 2)
    {a : ℝ} (ha : 0 ≤ a) (hcell : (ell : ℝ) * a ≤ 1)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = next k (P t) (E t))
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < H.val → 0 < fraction i b (P t)) :
    total H env P i b a ≤ a * H.val * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
      ∑ j, |samplingError H P i b a (laws H P hP) env j| := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    group_bound hk hn hell H env i b ha hcell horizon P E hnext hP hf j)
  have hcard : (∑ j : Fin (count R ell), ((group H.val ell j.val).card : ℝ)) = H.val := by
    exact_mod_cast total_group_card R H.val ell (by have := H.isLt; omega)
  unfold total
  calc
    _ ≤ ∑ j : Fin (count R ell), (a * (group H.val ell j.val).card *
        cost (mu : ℕ) ell a ((3 : ℝ) ^ k) + |samplingError H P i b a (laws H P hP) env j|) := hh
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp_rw [mul_assoc, mul_comm _ (cost (mu : ℕ) ell a ((3 : ℝ) ^ k)), ← mul_assoc]
      rw [← Finset.mul_sum, hcard]

lemma expected_total [Nonempty (Genotypes.Genotype n k)]
    (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (i : Fin n) (b : Fin 2)
    {a : ℝ} (ha : 0 ≤ a) (hcell : (ell : ℝ) * a ≤ 1)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (P : ℕ → Population n mu) (E : ℕ → Event n mu)
    (hnext : ∀ t, t < H.val → P (t + 1) = next k (P t) (E t))
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < H.val → 0 < fraction i b (P t)) :
    mean (FiniteProduct.distribution (fun j : Fin (count R ell) ↦ EmpiricalSampling.samples (laws H P hP j) (rs : ℕ)))
      (fun env ↦ total H env P i b a) ≤
        a * H.val * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
          (a * H.val * (3 : ℝ) ^ k) / (2 * Real.sqrt (rs : ℕ)) := by
  have hs := expected_kernel_sampling (rs := rs) hk hn hell H P i b ha horizon hP hf (laws H P hP)
  calc
    _ ≤ mean (FiniteProduct.distribution (fun j : Fin (count R ell) ↦ EmpiricalSampling.samples (laws H P hP j) (rs : ℕ)))
      (fun env ↦ a * H.val * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
        ∑ j, |samplingError H P i b a (laws H P hP) env j|) :=
      mean_mono _ (fun env ↦ total_bound hk hn hell H env i b ha hcell horizon P E hnext hP hf)
    _ = a * H.val * cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
      mean (FiniteProduct.distribution (fun j : Fin (count R ell) ↦ EmpiricalSampling.samples (laws H P hP j) (rs : ℕ)))
        (fun env ↦ ∑ j, |samplingError H P i b a (laws H P hP) env j|) := by
      rw [mean_add, mean_const]
    _ ≤ _ := add_le_add_right hs _

end
end Lax343628Proofs.MismatchTotals
