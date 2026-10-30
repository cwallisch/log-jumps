import Lax343628Proofs.SparseSampling
import Lax343628Proofs.GroupKernelSampling

namespace Lax343628Proofs.SparseKernelSampling

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.SparseSampling Lax343628Proofs.GroupKernelSampling
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteProduct Lax343628Proofs.EmpiricalSampling
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

lemma path_group (H : Fin (R + 1)) (env : Lists n k (count R ell) rs)
    (j : Fin (count R ell)) (t : ℕ) (ht : t ∈ group H.val ell j.val) :
    path (H, env) t = partnerLaw (env j) := by
  unfold path
  congr 1
  apply congrArg env
  apply Fin.ext
  exact (Finset.mem_filter.mp ht).2

def samplingError (H : Fin (R + 1)) (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2) (a : ℝ)
    (p : Fin (count R ell) → PMF (Genotypes.Genotype n k))
    (env : Lists n k (count R ell) rs) (j : Fin (count R ell)) : ℝ := a * ∑ t ∈ group H.val ell j.val,
  (fieldAction (P t) (mixedKernel (partnerLaw (env j))) (terminalFields H i b a j env) -
    fieldAction (P t) (mixedKernel ((p j).map Genotypes.toString)) (terminalFields H i b a j env)) /
      average (P t) (liftClass (terminalFields H i b a j env))

lemma test_error (H : Fin (R + 1)) (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2) (a : ℝ)
    (p : Fin (count R ell) → PMF (Genotypes.Genotype n k))
    (env : Lists n k (count R ell) rs) (j : Fin (count R ell)) :
    sampleMean (terminalTest H P i b a j env) (env j) - mean (p j) (terminalTest H P i b a j env) =
      samplingError H P i b a p env j := by
  exact sampling_difference a (fun j : Fin (count R ell) ↦ group H.val ell j.val) P
    (terminalFields H i b a) j env (env j) (p j)

lemma expected_kernel_sampling (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < H.val → 0 < ClassChannels.fraction i b (P t))
    (p : Fin (count R ell) → PMF (Genotypes.Genotype n k)) :
    mean (distribution (fun j ↦ samples (p j) (rs : ℕ)))
      (fun env ↦ ∑ j, |samplingError H P i b a p env j|) ≤
        (a * H.val * (3 : ℝ) ^ k) / (2 * Real.sqrt (rs : ℕ)) := by
  have ht := expected_sampling (rs := rs) hk hn hell H P i b ha horizon hP hf p
  have heq : (fun env : Lists n k (count R ell) rs ↦ ∑ j, |sampleMean (terminalTest H P i b a j env) (env j) -
      mean (p j) (terminalTest H P i b a j env)|) =
      (fun env ↦ ∑ j, |samplingError H P i b a p env j|) := by
    funext env
    apply Finset.sum_congr rfl
    intro j _
    rw [test_error]
  rw [heq] at ht
  exact ht

end
end Lax343628Proofs.SparseKernelSampling
