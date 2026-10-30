import Lax343628Proofs.GroupSampling

namespace Lax343628Proofs.GroupKernelSampling

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.WeightedKernels
open Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.GroupSampling
open Lax343628Proofs.EmpiricalSampling Lax343628Proofs.SparseEnvironment
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu rs : ℕ+} {i : Fin n} {b : Fin 2}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mean_finset_sum {α β : Type*} [Fintype α] (p : PMF α) (S : Finset β) (f : β → α → ℝ) :
    mean p (fun x ↦ ∑ j ∈ S, f j x) = ∑ j ∈ S, mean p (f j) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mean_div (p : PMF (Genotypes.Genotype n k)) (f : Genotypes.Genotype n k → ℝ) (c : ℝ) :
    mean p (fun x ↦ f x / c) = mean p f / c := by
  have heq : (fun x ↦ f x / c) = (fun x ↦ c⁻¹ * f x) := by funext x; ring
  rw [heq, mean_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma mean_test (a : ℝ) (G : ι → Finset ℕ) (P : ℕ → Population n mu)
    (F : ι → (ι → Fin (rs : ℕ) → Genotypes.Genotype n k) → ColumnClass n k i b → ℝ)
    (j : ι) (env : ι → Fin (rs : ℕ) → Genotypes.Genotype n k) (q : PMF (Genotypes.Genotype n k)) :
    mean q (test a G P F j env) = a * ∑ t ∈ G j,
      fieldAction (P t) (mixedKernel (q.map Genotypes.toString)) (F j env) /
        average (P t) (liftClass (F j env)) := by
  change mean q (fun u ↦ a * ∑ t ∈ G j,
    partnerAverage (P t) (F j env) (Genotypes.toString u) / average (P t) (liftClass (F j env))) = _
  rw [mean_mul, mean_finset_sum]
  simp_rw [mean_div]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [fieldAction_mean, mean_map]

omit [Fintype ι] [DecidableEq ι] in
lemma sample_test (a : ℝ) (G : ι → Finset ℕ) (P : ℕ → Population n mu)
    (F : ι → (ι → Fin (rs : ℕ) → Genotypes.Genotype n k) → ColumnClass n k i b → ℝ)
    (j : ι) (env : ι → Fin (rs : ℕ) → Genotypes.Genotype n k)
    (xs : Fin (rs : ℕ) → Genotypes.Genotype n k) :
    sampleMean (test a G P F j env) xs = a * ∑ t ∈ G j,
      fieldAction (P t) (mixedKernel (partnerLaw xs)) (F j env) /
        average (P t) (liftClass (F j env)) := by
  let q := (PMF.uniformOfFintype (Fin (rs : ℕ))).map xs
  have hm := mean_test a G P F j env q
  have hl : mean q (test a G P F j env) = sampleMean (test a G P F j env) xs := by
    dsimp only [q]
    rw [mean_map, mean_uniform, Fintype.card_fin]
    unfold sampleMean sampleSum
    ring
  have hq : q.map Genotypes.toString = partnerLaw xs := by
    dsimp only [q]
    rw [PMF.map_comp]
    rfl
  rw [hl, hq] at hm
  exact hm

omit [Fintype ι] [DecidableEq ι] in
lemma sampling_difference (a : ℝ) (G : ι → Finset ℕ) (P : ℕ → Population n mu)
    (F : ι → (ι → Fin (rs : ℕ) → Genotypes.Genotype n k) → ColumnClass n k i b → ℝ)
    (j : ι) (env : ι → Fin (rs : ℕ) → Genotypes.Genotype n k)
    (xs : Fin (rs : ℕ) → Genotypes.Genotype n k) (q : PMF (Genotypes.Genotype n k)) :
    sampleMean (test a G P F j env) xs - mean q (test a G P F j env) = a * ∑ t ∈ G j,
      (fieldAction (P t) (mixedKernel (partnerLaw xs)) (F j env) -
        fieldAction (P t) (mixedKernel (q.map Genotypes.toString)) (F j env)) /
          average (P t) (liftClass (F j env)) := by
  rw [sample_test, mean_test, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end Lax343628Proofs.GroupKernelSampling
