import Lax343628Proofs.SuppressedRegions
import Lax343628Proofs.PhysicalApproximation

namespace Lax343628Proofs.CountStatistics

open Lax343628.Algorithm Lax343628Proofs.OffspringRegions
open Lax343628Proofs.RegionGeometry Lax343628Proofs.SuppressedRegions
open Lax343628Proofs.MutationCoupling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.FiniteComparison Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteProduct Lax343628Proofs.MaskCounts
open Lax343628Proofs.PhysicalApproximation Lax343628Proofs.BinomialApproximation
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma mean_distribution_empty {γ : Fin 0 → Type*} [∀ i, Fintype (γ i)]
    (p : ∀ i, PMF (γ i)) (f : (∀ i, γ i) → ℝ) :
    mean (distribution p) f = f (fun i ↦ Fin.elim0 i) := by
  have hf : f = fun _ ↦ f (fun i ↦ Fin.elim0 i) := by
    funext x
    congr 1
    funext i
    exact Fin.elim0 i
  rw [hf, mean_const]

def countMean (N : ℕ) (p : ℝ) (f : ℕ → ℝ) : ℝ :=
  mean (weightLaw N p) (fun w ↦ f w.val)

lemma countMean_formula (N : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : ℕ → ℝ) :
    countMean N p f = ∑ w ∈ Finset.range (N + 1),
      (N.choose w : ℝ) * p ^ w * (1 - p) ^ (N - w) * f w := by
  unfold countMean mean
  simp_rw [weightLaw_apply, independentBits_count_real N _ p hp]
  exact Fin.sum_univ_eq_sum_range
    (fun w : ℕ ↦ (N.choose w : ℝ) * p ^ w * (1 - p) ^ (N - w) * f w) (N + 1)

lemma countMean_mono (N : ℕ) (p : ℝ) {f g : ℕ → ℝ} (h : ∀ w ≤ N, f w ≤ g w) :
    countMean N p f ≤ countMean N p g :=
  mean_mono _ (fun w ↦ h w.val (Nat.le_of_lt_succ w.isLt))

lemma countMean_const (N : ℕ) (p c : ℝ) : countMean N p (fun _ ↦ c) = c := mean_const _ c

lemma countMean_nonneg (N : ℕ) (p : ℝ) (f : ℕ → ℝ) (hf : ∀ w ≤ N, 0 ≤ f w) :
    0 ≤ countMean N p f := by
  have h := countMean_mono N p hf
  rwa [countMean_const] at h

lemma countMean_abs (N : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    |countMean N p f| ≤ countMean N p (fun w ↦ |f w|) := abs_mean_le _ _

lemma countMean_sub (N : ℕ) (p : ℝ) (f g : ℕ → ℝ) :
    countMean N p (fun w ↦ f w - g w) = countMean N p f - countMean N p g := mean_sub _ _ _

lemma countMean_comparison (N : ℕ) (p : ℝ) (f g : ℕ → ℝ) (E : ℝ)
    (h : ∀ w ≤ N, |f w - g w| ≤ E) :
    |countMean N p f - countMean N p g| ≤ E := by
  rw [← countMean_sub]
  exact (countMean_abs N p _).trans ((countMean_mono N p h).trans_eq (countMean_const N p E))

lemma mutation_countMean {n N : ℕ} (hn : 2 ≤ n) (f : ℕ → ℝ) :
    countMean N (1 / n) f =
      ∑ w ∈ Finset.range (N + 1), binomialTerm n N w * f w := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by linarith : (0 : ℝ) < n)).mpr
      linarith
  rw [countMean_formula N _ hp]
  apply Finset.sum_congr rfl
  intro w _
  unfold binomialTerm
  rw [div_pow, one_pow]
  ring

lemma mutation_truncated_mean {n N k : ℕ} (hn : 2 ≤ n) (hk : k ≤ N)
    (f : ℕ → ℝ) (hf : ∀ w, k < w → f w = 0) :
    countMean N (1 / n) f =
      ∑ w ∈ Finset.range (k + 1), binomialTerm n N w * f w := by
  rw [mutation_countMean hn]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hk 1))
  intro w _ hw
  rw [hf w (by simp only [Finset.mem_range] at hw; omega), mul_zero]

def poissonMean (k : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w ∈ Finset.range (k + 1), Real.exp (-1) / (w.factorial : ℝ) * f w

lemma count_poisson_comparison {n N k : ℕ} (hn : 2 ≤ n) (hN : N ≤ n) (hk : k ≤ N)
    (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ w ≤ k, |f w| ≤ M)
    (hsupport : ∀ w, k < w → f w = 0) :
    |countMean N (1 / n) f - poissonMean k f| ≤
      3 * M * ((k : ℝ) + 2) * (((n - N + k : ℕ) : ℝ) + 1) / n := by
  rw [mutation_truncated_mean hn hk f hsupport, poissonMean]
  have h := weighted_sum_error (Finset.range (k + 1)) (binomialTerm n N)
    (fun w ↦ Real.exp (-1) / (w.factorial : ℝ)) f M
    (fun w hw ↦ hf w (Nat.le_of_lt_succ (Finset.mem_range.mp hw)))
  have hb := mul_le_mul_of_nonneg_left (truncated_error_sum hn hN hk) hM
  exact h.trans (hb.trans_eq (by ring))

lemma six_count_mean (N : Fin 6 → ℕ) (p : ℝ) (f : ℕ → ℕ → ℝ) :
    mean (distribution (fun r ↦ weightLaw (N r) (suppressedRate p r)))
      (fun c ↦ f ((c 0).val + (c 1).val + (c 2).val)
        ((c 3).val + (c 4).val + (c 5).val)) =
      countMean (N 2) (1 / 2) (fun l ↦
        countMean (N 4) p (fun w ↦
          countMean (N 5) (1 / 2) (fun v ↦ f (N 1 + l) (N 3 + w + v)))) := by
  unfold countMean
  rw [mean_distribution_cons]
  simp only [suppressedRate, rate, Fin.isValue, ite_true, weightLaw_zero, mean_pure]
  rw [mean_distribution_cons]
  norm_num only [Fin.succ, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.ext_iff,
    Fin.cons_zero, Fin.cons_succ, suppressedRate, rate, if_true, if_false,
    true_or, false_or, weightLaw_one, mean_pure]
  simp_rw [mean_distribution_cons]
  norm_num [Fin.succ, Fin.ext_iff, suppressedRate, rate, weightLaw_zero, weightLaw_one,
    mean_pure, Fin.cons_zero, Fin.cons_succ, mean_distribution_empty]
  rfl

lemma suppressed_statistic_mean {n : ℕ} (B x y : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (f : ℕ → ℕ → ℝ) :
    mean (suppressedPair (forbidden B x y) x y p)
      (fun child ↦ f (insideCount B child) (outsideCount B child)) =
      countMean (regionSize B x y 2) (1 / 2) (fun l ↦
        countMean (regionSize B x y 4) p (fun w ↦
          countMean (regionSize B x y 5) (1 / 2) (fun v ↦
            f (regionSize B x y 1 + l) (regionSize B x y 3 + w + v)))) := by
  have h := mean_map (suppressedPair (forbidden B x y) x y p) (regionCounts B x y)
    (fun c ↦ f ((c 0).val + (c 1).val + (c 2).val)
      ((c 3).val + (c 4).val + (c 5).val))
  rw [suppressed_count_law B x y p hp] at h
  simp_rw [← inside_region_counts, ← outside_region_counts] at h
  rw [← h, six_count_mean]
  simp_rw [← regionSize_eq_fintype]

end
end Lax343628Proofs.CountStatistics
