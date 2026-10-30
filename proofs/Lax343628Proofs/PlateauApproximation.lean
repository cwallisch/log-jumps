import Lax343628Proofs.CountStatistics

namespace Lax343628Proofs.PlateauApproximation

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.RegionGeometry Lax343628Proofs.SuppressedRegions
open Lax343628Proofs.MutationCoupling Lax343628Proofs.FiniteDrift
open Lax343628Proofs.CountStatistics Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def balanced (ψ : ℕ → ℝ) (a b : ℕ) : ℝ := if a = b then ψ a else 0

lemma balanced_bound (ψ : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) {a k : ℕ}
    (ha : a ≤ k) (hψ : ∀ r ≤ k, |ψ r| ≤ M) (b : ℕ) : |balanced ψ a b| ≤ M := by
  unfold balanced
  split_ifs
  · exact hψ a ha
  · simpa using hM

def idealMean (k A D t u : ℕ) (ψ : ℕ → ℝ) : ℝ :=
  countMean A (1 / 2) (fun l ↦ poissonMean k (fun w ↦
    countMean D (1 / 2) (fun v ↦ balanced ψ (t + l) (u + w + v))))

lemma count_ideal_error {n N k A D t u : ℕ} (hn : 2 ≤ n) (hN : N ≤ n) (hk : k ≤ N)
    (htA : t + A ≤ k) (ψ : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hψ : ∀ r ≤ k, |ψ r| ≤ M) :
    |countMean A (1 / 2) (fun l ↦ countMean N (1 / n) (fun w ↦
        countMean D (1 / 2) (fun v ↦ balanced ψ (t + l) (u + w + v)))) -
      idealMean k A D t u ψ| ≤
        3 * M * ((k : ℝ) + 2) * (((n - N + k : ℕ) : ℝ) + 1) / n := by
  apply countMean_comparison
  intro l hl
  have htl : t + l ≤ k := by omega
  apply count_poisson_comparison hn hN hk _ M hM
  · intro w _
    exact (countMean_abs D (1 / 2) _).trans ((countMean_mono D (1 / 2)
      (fun v _ ↦ balanced_bound ψ M hM htl hψ (u + w + v))).trans_eq
        (countMean_const D (1 / 2) M))
  · intro w hw
    have heq : (fun v ↦ balanced ψ (t + l) (u + w + v)) = fun _ ↦ 0 := by
      funext v
      exact if_neg (by omega : t + l ≠ u + w + v)
    rw [heq, countMean_const]

lemma physical_ideal_error {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B x y : BitString n) (hB : (zeros B).card = k) (hx : (zeros x).card = k)
    (hy : (zeros y).card = k) (ψ : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hψ : ∀ r ≤ k, |ψ r| ≤ M) :
    |mean (pairMutation x y (1 / n)) (fun child ↦
        balanced ψ (insideCount B child) (outsideCount B child)) -
      idealMean k (regionSize B x y 2) (regionSize B x y 5)
        (regionSize B x y 1) (regionSize B x y 3) ψ| ≤
          M * (4 * (k : ℝ) + 3 * ((k : ℝ) + 2) * (4 * (k : ℝ) + 1)) / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1 : ℝ) / n ∧ (1 : ℝ) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by linarith : (0 : ℝ) < n)).mpr
      linarith
  have hb : ∀ child, |balanced ψ (insideCount B child) (outsideCount B child)| ≤ M := by
    intro child
    apply balanced_bound ψ M hM _ hψ
    simpa only [hB] using insideCount_le B child
  have h1 := physical_suppressed_error hn B x y hB hx
    (fun child ↦ balanced ψ (insideCount B child) (outsideCount B child)) M hb
  rw [suppressed_statistic_mean B x y _ hp] at h1
  have hdeficit := fresh_region_deficit B x y hB hx hy
  have hN : regionSize B x y 4 ≤ n := by
    simpa [regionSize] using Finset.card_le_univ (regionSet B x y 4)
  have hkN : k ≤ regionSize B x y 4 := by omega
  have htA : regionSize B x y 1 + regionSize B x y 2 ≤ k := by
    simpa only [hB] using variable_inside_size B x y
  have h2 := count_ideal_error hn hN hkN htA ψ M hM hψ
    (D := regionSize B x y 5) (u := regionSize B x y 3)
  have he : (((n - regionSize B x y 4 + k : ℕ) : ℝ) + 1) ≤ 4 * (k : ℝ) + 1 := by
    exact_mod_cast (show n - regionSize B x y 4 + k + 1 ≤ 4 * k + 1 by omega)
  have h2' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (show 0 ≤ 3 * M * ((k : ℝ) + 2) by positivity))
    (show (0 : ℝ) ≤ n by positivity)
  calc
    _ ≤ _ + _ := abs_sub_le _ _ _
    _ ≤ 4 * M * k / n +
        3 * M * ((k : ℝ) + 2) * (4 * (k : ℝ) + 1) / n :=
      add_le_add h1 (h2.trans h2')
    _ = _ := by ring

end
end Lax343628Proofs.PlateauApproximation
