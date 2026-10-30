import Lax343628Proofs.AnchorMutation
import Lax343628Proofs.MutationApproximation

namespace Lax343628Proofs.MutationDrift

open Lax343628Proofs.Genotypes Lax343628Proofs.Weights
open Lax343628Proofs.Species Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.ActualBirthKernels Lax343628Proofs.AnchorMutation
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.PlateauKernelApproximation
open Lax343628Proofs.MutationApproximation
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma mean_weight_cloud {n k : ℕ} (B : Genotype n k) (p : PMF (Genotype n k)) :
    mean p (fun x ↦ weight (distance B x)) = cloud B (fun x ↦ (p x).toReal) := by
  unfold mean
  rw [sum_split B]
  simp only [distance_self, weight_zero, mul_zero, zero_add]
  rfl

lemma mutation_weight_lower {n k : ℕ} (hk : 1 ≤ k) (hlarge : 2 * k ≤ n)
    (hn : 2 ≤ n) (B : Genotype n k) (p : PMF (Genotype n k)) :
    (1 - 1 / (n : ℝ)) ^ n * cloud B (fun x ↦ (p x).toReal) +
      (p B).toReal * ((k : ℝ) / (16 * n)) ≤ mean p (fun x ↦ weightedBirth B x x) := by
  have h := mean_mono p (weightedBirth_self_with_seed hk hlarge hn B)
  rw [mean_add, mean_mul, mean_weight_cloud, mean_pick] at h
  exact h

lemma mutation_clone_upper {n k : ℕ} (hn : 2 ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) :
    mean p (fun x ↦ cloneBirth B x x) ≤ (1 - 1 / (n : ℝ)) ^ n * (p B).toReal +
      (1 / (n : ℝ)) ^ 2 := by
  have hpoint : ∀ x : Genotype n k, cloneBirth B x x ≤
      (if x = B then (1 - 1 / (n : ℝ)) ^ n else 0) + (1 / (n : ℝ)) ^ 2 := by
    intro x
    by_cases hx : x = B
    · subst x
      rw [cloneBirth_self hn B, if_pos rfl]
      have hpos : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ 2 := by positivity
      linarith
    · rw [if_neg hx, zero_add]
      exact cloneBirth_changed_upper hn B x hx
  have h := mean_mono p hpoint
  rw [mean_add, mean_pick, mean_const] at h
  nlinarith

lemma mutation_ratio_lower {n k : ℕ} (hk : 1 ≤ k) (hlarge : 2 * k ≤ n)
    (hn : 2 ≤ n) (B : Genotype n k) (p : PMF (Genotype n k)) (Q : ℝ) (hQ : 0 ≤ Q)
    (hcancel : cloud B (fun x ↦ (p x).toReal) = Q * (p B).toReal) :
    (p B).toReal * ((k : ℝ) / (16 * n)) - Q * (1 / (n : ℝ)) ^ 2 ≤
      mean p (fun x ↦ weightedBirth B x x) - Q * mean p (fun x ↦ cloneBirth B x x) := by
  have hw := mutation_weight_lower hk hlarge hn B p
  have hc := mul_le_mul_of_nonneg_left (mutation_clone_upper hn B p) hQ
  rw [hcancel] at hw
  nlinarith

lemma crossed_ratio_seed_lower {n k : ℕ} (hk : 1 ≤ k) (hlarge : 4 * k ≤ n)
    (hn : 2 ≤ n) (B : Genotype n k) (p : PMF (Genotype n k)) (Q : ℝ) (hQ : 0 ≤ Q) :
    Real.exp (-1) * (pairValue (fun x ↦ (p x).toReal) (weightedKernel B) -
      Q * pairValue (fun x ↦ (p x).toReal) (cloneKernel B)) +
        (p B).toReal ^ 2 * ((k : ℝ) / (16 * n)) -
          (1 - (p B).toReal ^ 2) * ((5 / 4 + Q) * approximationError n k) ≤
      pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B) := by
  let E : ℝ := (5 / 4 + Q) * approximationError n k
  let g : ℝ := (k : ℝ) / (16 * n)
  have hpoint : ∀ x y : Genotype n k,
      Real.exp (-1) * (weightedKernel B x y - Q * cloneKernel B x y) - E +
        (if x = B ∧ y = B then g + E else 0) ≤ weightedBirth B x y - Q * cloneBirth B x y := by
    intro x y
    by_cases hBB : x = B ∧ y = B
    · rcases hBB with ⟨hx, hy⟩
      subst x
      subst y
      have hgain := weightedBirth_self_gain hk (by omega : 2 * k ≤ n) hn B
      have hclone : cloneBirth B B B ≤ Real.exp (-1) := by
        rw [cloneBirth_self hn B]
        exact (no_mutation_approximation n hn).2
      have hqc := mul_le_mul_of_nonneg_left hclone hQ
      simp only [weightedKernel_anchor_self, cloneKernel_anchor, distance_self, pow_zero,
        and_self, ite_true]
      dsimp [g]
      nlinarith
    · rw [if_neg hBB, add_zero]
      have hw := (abs_le.mp (weightedBirth_error hn hlarge B x y)).1
      have hc := mul_le_mul_of_nonneg_left
        (abs_le.mp (cloneBirth_error hn hlarge B x y)).2 hQ
      dsimp [E]
      nlinarith
  have h := pairMean_mono p hpoint
  simp only [pairMean_add, pairMean_sub, pairMean_mul, pairMean_const, pairMean_anchor] at h
  rw [pairMean_eq_pairValue p (weightedKernel B), pairMean_eq_pairValue p (cloneKernel B)] at h
  dsimp [E, g] at h
  nlinarith

end
end Lax343628Proofs.MutationDrift
