import Lax343628Proofs.GroupSampling
import Lax343628Proofs.SparseFields

namespace Lax343628Proofs.SparseSampling

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups Lax343628Proofs.SparseFields
open Lax343628Proofs.GroupSampling Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteProduct Lax343628Proofs.EmpiricalSampling
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k R ell : ℕ} {rs mu : ℕ+}

def terminalFields (H : Fin (R + 1)) (i : Fin n) (b : Fin 2) (a : ℝ)
    (j : Fin (count R ell)) (env : Lists n k (count R ell) rs) : ColumnClass n k i b → ℝ :=
  field (H, env) i b a (groupEnd H.val ell j.val)

def terminalTest (H : Fin (R + 1)) (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2) (a : ℝ)
    (j : Fin (count R ell)) (env : Lists n k (count R ell) rs) (u : Genotypes.Genotype n k) : ℝ :=
  test a (fun j : Fin (count R ell) ↦ group H.val ell j.val) P (terminalFields H i b a) j env u

lemma expected_sampling (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hell : 1 ≤ ell)
    (H : Fin (R + 1)) (P : ℕ → Population n mu) (i : Fin n) (b : Fin 2) {a : ℝ} (ha : 0 ≤ a)
    (horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1)
    (hP : ∀ t, t < H.val → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ t, t < H.val → 0 < ClassChannels.fraction i b (P t))
    (p : Fin (count R ell) → PMF (Genotypes.Genotype n k)) :
    mean (distribution (fun j ↦ samples (p j) (rs : ℕ))) (fun env ↦ ∑ j,
      |sampleMean (terminalTest H P i b a j env) (env j) - mean (p j) (terminalTest H P i b a j env)|) ≤
        (a * H.val * (3 : ℝ) ^ k) / (2 * Real.sqrt (rs : ℕ)) := by
  let : Nonempty (Genotypes.Genotype n k) := genotype_nonempty (by omega)
  have htime (j : Fin (count R ell)) (t : ℕ) (ht : t ∈ group H.val ell j.val) : t < H.val :=
    Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  have hD : (0 : ℝ) ≤ (3 : ℝ) ^ k := by positivity
  have ht := GroupSampling.expected_error (rs := rs) a ha (fun j : Fin (count R ell) ↦ group H.val ell j.val) P
    (fun j t hmem ↦ hP t (htime j t hmem)) (fun j t hmem ↦ hf t (htime j t hmem))
    (terminalFields H i b a) (fun j env z ↦ field_one (H, env) i b ha _ z)
    ((3 : ℝ) ^ k) hD (fun j env x z ↦ field_ratio hk hn (H, env) i b ha horizon _ x z)
    (fun j rest xs ys ↦ field_end_independent H j rest xs ys hell i b a) p
  have hsum : (∑ j : Fin (count R ell), ((group H.val ell j.val).card : ℝ)) = H.val := by
    exact_mod_cast total_group_card R H.val ell (by have := H.isLt; omega)
  rw [hsum] at ht
  exact ht

end
end Lax343628Proofs.SparseSampling
