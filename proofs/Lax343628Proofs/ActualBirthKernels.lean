import Lax343628Proofs.EmpiricalKernels
import Lax343628Proofs.PlateauKernelApproximation

namespace Lax343628Proofs.ActualBirthKernels

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.PhysicalOffspring
open Lax343628Proofs.Genotypes Lax343628Proofs.Weights Lax343628Proofs.RegionGeometry
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.PlateauKernelApproximation
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.Species
open Lax343628Proofs.IdealCountKernel
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def acceptedWeight {n k : ℕ} (B : Genotype n k) (child : BitString n) : ℝ :=
  if onPlateau k child then weight (insideCount (toString B) child) else 0

def acceptedClone {n k : ℕ} (B : Genotype n k) (child : BitString n) : ℝ :=
  if onPlateau k child then cloneWeight (insideCount (toString B) child) else 0

def weightedBirth {n k : ℕ} (B x y : Genotype n k) : ℝ :=
  mean (pairMutation (toString x) (toString y) (1 / n)) (acceptedWeight B)

def cloneBirth {n k : ℕ} (B x y : Genotype n k) : ℝ :=
  mean (pairMutation (toString x) (toString y) (1 / n)) (acceptedClone B)

def viableBirth {n k : ℕ} (x y : Genotype n k) : ℝ :=
  mean (pairMutation (toString x) (toString y) (1 / n))
    (fun child ↦ if onPlateau k child then 1 else 0)

lemma acceptedWeight_nonneg {n k : ℕ} (B : Genotype n k) (child : BitString n) :
    0 ≤ acceptedWeight B child := by
  unfold acceptedWeight
  split_ifs
  · exact weight_nonneg _
  · exact le_rfl

lemma toString_onPlateau {n k : ℕ} (x : Genotype n k) : onPlateau k (toString x) := by
  have hkn : k ≤ n := by
    simpa only [x.property, Fintype.card_fin] using Finset.card_le_univ x.val
  exact plateau_of_zero_card hkn (toString x) (by simpa using x.property)

lemma toString_insideCount {n k : ℕ} (B x : Genotype n k) :
    insideCount (toString B) (toString x) = distance B x := by
  rw [← anchor_missing_eq, zeros_toString, zeros_toString]
  rfl

lemma acceptedWeight_toString {n k : ℕ} (B x : Genotype n k) :
    acceptedWeight B (toString x) = weight (distance B x) := by
  rw [acceptedWeight, if_pos (toString_onPlateau x), toString_insideCount]

lemma weightedBirth_error {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B x y : Genotype n k) :
    |weightedBirth B x y - Real.exp (-1) * weightedKernel B x y| ≤
      (5 / 4 : ℝ) * approximationError n k := by
  have h := physical_weighted_kernel hn hlarge (toString B) (toString x) (toString y)
    (by simpa using B.property) (by simpa using x.property) (by simpa using y.property)
  simp only [ofString_toString] at h
  unfold weightedBirth acceptedWeight
  exact h

lemma cloneBirth_error {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B x y : Genotype n k) :
    |cloneBirth B x y - Real.exp (-1) * cloneKernel B x y| ≤ approximationError n k := by
  have h := physical_clone_kernel hn hlarge (toString B) (toString x) (toString y)
    (by simpa using B.property) (by simpa using x.property) (by simpa using y.property)
  simp only [ofString_toString] at h
  unfold cloneBirth acceptedClone
  exact h

lemma viableBirth_error {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (x y : Genotype n k) :
    |viableBirth x y - Real.exp (-1) * Lax343628Proofs.Profiles.viability (distance x y)| ≤
      approximationError n k := by
  simpa only [viableBirth, ofString_toString] using
    physical_viability_kernel hn hlarge (toString x) (toString y)
      (by simpa using x.property) (by simpa using y.property)

lemma offspring_mean {n : ℕ} {μ : ℕ+} (p_c : ℝ) (hp : 0 ≤ p_c ∧ p_c ≤ 1)
    (P : Population n μ) (f : BitString n → ℝ) :
    mean (offspring p_c P) f =
      p_c * mean (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ)))
        (fun uv ↦ mean (pairMutation (P uv.1) (P uv.2) (1 / n)) f) +
      (1 - p_c) * mean (PMF.uniformOfFintype (Fin (μ : ℕ)))
        (fun u ↦ mean (pairMutation (P u) (P u) (1 / n)) f) := by
  rw [offspring_split, mean_bind, mean_coin p_c hp]
  norm_num only [ite_true, show ¬(0 : Fin 2) = 1 by decide, ite_false]
  simp only [mean_bind]

lemma population_weighted_birth_error {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) :
    |pairMean p (weightedBirth B) -
      Real.exp (-1) * pairValue (fun x ↦ (p x).toReal) (weightedKernel B)| ≤
        (5 / 4 : ℝ) * approximationError n k := by
  have h := pairMean_comparison p (weightedBirth B)
    (fun x y ↦ Real.exp (-1) * weightedKernel B x y) _ (weightedBirth_error hn hlarge B)
  rwa [pairMean_mul, pairMean_eq_pairValue p (weightedKernel B)] at h

lemma population_clone_birth_error {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) :
    |pairMean p (cloneBirth B) -
      Real.exp (-1) * pairValue (fun x ↦ (p x).toReal) (cloneKernel B)| ≤
        approximationError n k := by
  have h := pairMean_comparison p (cloneBirth B)
    (fun x y ↦ Real.exp (-1) * cloneKernel B x y) _ (cloneBirth_error hn hlarge B)
  rwa [pairMean_mul, pairMean_eq_pairValue p (cloneKernel B)] at h

lemma crossed_ratio_lower {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) (Q : ℝ) (hQ : 0 ≤ Q) :
    Real.exp (-1) * (pairValue (fun x ↦ (p x).toReal) (weightedKernel B) -
      Q * pairValue (fun x ↦ (p x).toReal) (cloneKernel B)) -
        (5 / 4 + Q) * approximationError n k ≤
      pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B) := by
  have hw := (abs_le.mp (population_weighted_birth_error hn hlarge B p)).1
  have hc := (abs_le.mp (population_clone_birth_error hn hlarge B p)).2
  have hqc := mul_le_mul_of_nonneg_left hc hQ
  nlinarith

lemma crossed_strict_drift {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) (hpB : 0 < (p B).toReal)
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25)
    (hentry : 1 / 50 ≤ cloud B (fun x ↦ (p x).toReal) / (p B).toReal) :
    let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
    Real.exp (-1) * ((337 / 10000 : ℝ) * (1 / 50) * Q * (p B).toReal ^ 2 +
        otherPair B (fun x ↦ (p x).toReal)) -
      (5 / 4 + Q) * approximationError n k ≤
        pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B) := by
  dsimp only
  have hQ : 0 ≤ cloud B (fun x ↦ (p x).toReal) / (p B).toReal := by
    linarith
  have hid := ideal_strict_drift B (fun x ↦ (p x).toReal)
    (fun _ ↦ ENNReal.toReal_nonneg) hpB hiso hentry
  have hmul := mul_le_mul_of_nonneg_left hid (Real.exp_nonneg (-1))
  have hcross := crossed_ratio_lower hn hlarge B p _ hQ
  linarith

lemma crossed_viability_lower {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hlarge : 4 * k ≤ n)
    (p : PMF (Genotype n k)) :
    Real.exp (-1) * (1 / (2 * Real.sqrt k)) - approximationError n k ≤
      pairMean p viableBirth := by
  have hpoint : ∀ x y : Genotype n k,
      Real.exp (-1) * (1 / (2 * Real.sqrt k)) - approximationError n k ≤ viableBirth x y := by
    intro x y
    have herror := (abs_le.mp (viableBirth_error hn hlarge x y)).1
    have hlow := mul_le_mul_of_nonneg_left
      (Lax343628Proofs.Profiles.viability_uniform_lower hk (distance_le x y))
      (Real.exp_nonneg (-1))
    linarith
  unfold pairMean
  have hi : ∀ x, Real.exp (-1) * (1 / (2 * Real.sqrt k)) - approximationError n k ≤
      mean p (viableBirth x) := by
    intro x
    have h := mean_mono p (hpoint x)
    rwa [mean_const] at h
  have h := mean_mono p hi
  rwa [mean_const] at h

lemma empirical_offspring_weight {n k : ℕ} {μ : ℕ+} (p_c : ℝ)
    (hp : 0 ≤ p_c ∧ p_c ≤ 1) (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    mean (offspring p_c (fun u ↦ toString (P u))) (acceptedWeight B) =
      p_c * pairMean (empirical P) (weightedBirth B) +
        (1 - p_c) * mean (empirical P) (fun x ↦ weightedBirth B x x) := by
  rw [offspring_mean p_c hp]
  change p_c * mean (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ)))
      (fun uv ↦ weightedBirth B (P uv.1) (P uv.2)) +
    (1 - p_c) * mean (PMF.uniformOfFintype (Fin (μ : ℕ)))
      (fun u ↦ weightedBirth B (P u) (P u)) = _
  rw [empirical_pairMean]
  have h := mean_map (PMF.uniformOfFintype (Fin (μ : ℕ))) P (fun x ↦ weightedBirth B x x)
  rw [← h]
  rfl

lemma empirical_offspring_clone {n k : ℕ} {μ : ℕ+} (p_c : ℝ)
    (hp : 0 ≤ p_c ∧ p_c ≤ 1) (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    mean (offspring p_c (fun u ↦ toString (P u))) (acceptedClone B) =
      p_c * pairMean (empirical P) (cloneBirth B) +
        (1 - p_c) * mean (empirical P) (fun x ↦ cloneBirth B x x) := by
  rw [offspring_mean p_c hp]
  change p_c * mean (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ)))
      (fun uv ↦ cloneBirth B (P uv.1) (P uv.2)) +
    (1 - p_c) * mean (PMF.uniformOfFintype (Fin (μ : ℕ)))
      (fun u ↦ cloneBirth B (P u) (P u)) = _
  rw [empirical_pairMean]
  have h := mean_map (PMF.uniformOfFintype (Fin (μ : ℕ))) P (fun x ↦ cloneBirth B x x)
  rw [← h]
  rfl

end
end Lax343628Proofs.ActualBirthKernels
