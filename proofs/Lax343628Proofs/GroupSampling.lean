import Lax343628Proofs.WeightedKernels
import Lax343628Proofs.AdaptiveSampling

namespace Lax343628Proofs.GroupSampling

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.WeightedKernels Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.FiniteProduct
open Lax343628Proofs.EmpiricalSampling Lax343628Proofs.FiniteConditioning
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu rs : ℕ+} {i : Fin n} {b : Fin 2}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma average_one_lower (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) (hone : ∀ z, 1 ≤ h z) : fraction i b P ≤ average P (liftClass h) := by
  have ht := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦
    show (if P u i = b then (1 : ℝ) else 0) ≤ liftClass h (P u) by
      by_cases hb : P u i = b
      · simpa only [liftClass, dif_pos (And.intro (hP u) hb), if_pos hb] using hone ⟨P u, hP u, hb⟩
      · simp only [liftClass, dif_neg (by tauto : ¬((Sampling.zeros (P u)).card = k ∧ P u i = b)), if_neg hb, le_refl])
  exact ht

lemma partner_ratio_bound (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) (hone : ∀ z, 1 ≤ h z) (D : ℝ) (hD : 0 ≤ D)
    (hratio : ∀ x z, h z ≤ D * h x) (hf : 0 < fraction i b P) (u : BitString n) :
    0 ≤ partnerAverage P h u / average P (liftClass h) ∧
      partnerAverage P h u / average P (liftClass h) ≤ D := by
  have hy : 0 < average P (liftClass h) := hf.trans_le (average_one_lower P hP h hone)
  have hp := partner_bound P h D hD (fun z ↦ le_trans (by norm_num) (hone z)) hratio u
  exact ⟨div_nonneg hp.1 hy.le, (div_le_iff₀ hy).mpr (by nlinarith [hp.2])⟩

def test (a : ℝ) (G : ι → Finset ℕ) (P : ℕ → Population n mu)
    (F : ι → (ι → Fin (rs : ℕ) → Genotypes.Genotype n k) → ColumnClass n k i b → ℝ)
    (j : ι) (env : ι → Fin (rs : ℕ) → Genotypes.Genotype n k) (u : Genotypes.Genotype n k) : ℝ :=
  a * ∑ t ∈ G j, partnerAverage (P t) (F j env) (Genotypes.toString u) / average (P t) (liftClass (F j env))

omit [Fintype ι] [DecidableEq ι] in
lemma test_bound (a : ℝ) (ha : 0 ≤ a) (G : ι → Finset ℕ) (P : ℕ → Population n mu)
    (hP : ∀ j t, t ∈ G j → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ j t, t ∈ G j → 0 < fraction i b (P t))
    (F : ι → (ι → Fin (rs : ℕ) → Genotypes.Genotype n k) → ColumnClass n k i b → ℝ)
    (hone : ∀ j env z, 1 ≤ F j env z) (D : ℝ) (hD : 0 ≤ D)
    (hratio : ∀ j env x z, F j env z ≤ D * F j env x)
    (j : ι) (env : ι → Fin (rs : ℕ) → Genotypes.Genotype n k) (u : Genotypes.Genotype n k) :
    0 ≤ test a G P F j env u ∧ test a G P F j env u ≤ a * (G j).card * D := by
  have hp (t : ℕ) (ht : t ∈ G j) :=
    partner_ratio_bound (P t) (hP j t ht) (F j env) (hone j env) D hD (hratio j env) (hf j t ht) (Genotypes.toString u)
  have hlo : 0 ≤ ∑ t ∈ G j, partnerAverage (P t) (F j env) (Genotypes.toString u) /
      average (P t) (liftClass (F j env)) := Finset.sum_nonneg (fun t ht ↦ (hp t ht).1)
  have hhi : (∑ t ∈ G j, partnerAverage (P t) (F j env) (Genotypes.toString u) /
      average (P t) (liftClass (F j env))) ≤ (G j).card * D := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun t ht ↦ (hp t ht).2)
  unfold test
  constructor
  · exact mul_nonneg ha hlo
  · nlinarith [mul_le_mul_of_nonneg_left hhi ha]

lemma expected_error [Nonempty (Genotypes.Genotype n k)] (a : ℝ) (ha : 0 ≤ a)
    (G : ι → Finset ℕ) (P : ℕ → Population n mu)
    (hP : ∀ j t, t ∈ G j → ∀ u, (Sampling.zeros (P t u)).card = k)
    (hf : ∀ j t, t ∈ G j → 0 < fraction i b (P t))
    (F : ι → (ι → Fin (rs : ℕ) → Genotypes.Genotype n k) → ColumnClass n k i b → ℝ)
    (hone : ∀ j env z, 1 ≤ F j env z) (D : ℝ) (hD : 0 ≤ D)
    (hratio : ∀ j env x z, F j env z ≤ D * F j env x)
    (hind : ∀ j rest xs ys, F j (fill j rest xs) = F j (fill j rest ys))
    (p : ι → PMF (Genotypes.Genotype n k)) :
    mean (distribution (fun j ↦ samples (p j) (rs : ℕ))) (fun env ↦ ∑ j,
      |sampleMean (test a G P F j env) (env j) - mean (p j) (test a G P F j env)|) ≤
        (a * (∑ j, ((G j).card : ℝ)) * D) / (2 * Real.sqrt (rs : ℕ)) := by
  let base : Fin (rs : ℕ) → Genotypes.Genotype n k := fun _ ↦ Classical.choice inferInstance
  let f := fun j rest ↦ test a G P F j (fill j rest base)
  have hf' : ∀ j rest u, 0 ≤ f j rest u ∧ f j rest u ≤ a * (G j).card * D := by
    intro j rest u
    exact test_bound a ha G P hP hf F hone D hD hratio j _ u
  have ht := AdaptiveSampling.adaptive_total_error p rs.pos f
    (fun j ↦ a * (G j).card * D) (fun j ↦ by positivity) hf'
  have hfill (env : ι → Fin (rs : ℕ) → Genotypes.Genotype n k) (j : ι) :
      fill j (fun z ↦ env z.val) (env j) = env := by
    funext z
    by_cases hz : z = j
    · subst z; simp [fill]
    · simp [fill, hz]
  have htest (env : ι → Fin (rs : ℕ) → Genotypes.Genotype n k) (j : ι) :
      f j (fun z ↦ env z.val) = test a G P F j env := by
    have hh := hind j (fun z ↦ env z.val) base (env j)
    rw [hfill] at hh
    unfold f test
    rw [hh]
  simp_rw [htest] at ht
  have hsum : (∑ j, a * ((G j).card : ℝ) * D) = a * (∑ j, ((G j).card : ℝ)) * D := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simpa only [hsum] using ht

end
end Lax343628Proofs.GroupSampling
