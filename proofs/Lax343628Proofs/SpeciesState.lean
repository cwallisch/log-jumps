import Lax343628Proofs.PopulationRatio
import Lax343628Proofs.EntryBounds

namespace Lax343628Proofs.SpeciesState

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Genotypes
open Lax343628Proofs.Weights Lax343628Proofs.WeightSums Lax343628Proofs.RegionGeometry
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.Deletion
open Lax343628Proofs.PopulationRatio Lax343628Proofs.Species
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.ActualBirthKernels
open Lax343628Proofs.MutationDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def weightFunction {n k : ℕ} (B : Genotype n k) (child : BitString n) : ℝ :=
  weight (insideCount (toString B) child)

lemma weightFunction_anchor {n k : ℕ} (B : Genotype n k) : weightFunction B (toString B) = 0 := by
  simp [weightFunction, Lax343628Proofs.PlateauKernelApproximation.insideCount_self, weight_zero]

lemma weightFunction_bounds {n k : ℕ} (B : Genotype n k) (child : BitString n) :
    0 ≤ weightFunction B child ∧ weightFunction B child ≤ 5 / 4 :=
  ⟨weight_nonneg _, weight_upper _⟩

lemma weightFunction_toString {n k : ℕ} (B x : Genotype n k) :
    weightFunction B (toString x) = weight (distance B x) := by
  rw [weightFunction, toString_insideCount]

def realizePopulation {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) : Population n μ :=
  fun u ↦ toString (P u)

lemma realize_plateau {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) :
    plateauPopulation k (realizePopulation P) := fun u ↦ toString_onPlateau (P u)

lemma count_empirical {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    count (toString B) (realizePopulation P) = (μ : ℕ) * (empirical P B).toReal := by
  have h := mean_pick (empirical P) B 1
  rw [empirical, mean_map, mean_uniform] at h
  simp only [Fintype.card_fin, mul_one] at h
  have hc : count (toString B) (realizePopulation P) =
      ∑ u : Fin (μ : ℕ), if P u = B then (1 : ℝ) else 0 := by
    unfold count total indicator realizePopulation
    simp only [toString_eq_iff]
  rw [← hc] at h
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have h' := congrArg (fun x : ℝ ↦ (μ : ℕ) * x) h
  rw [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul] at h'
  exact h'

lemma total_empirical {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    total (weightFunction B) (realizePopulation P) =
      (μ : ℕ) * cloud B (fun x ↦ (empirical P x).toReal) := by
  have h := mean_weight_cloud B (empirical P)
  rw [empirical, mean_map, mean_uniform] at h
  simp only [Fintype.card_fin] at h
  have hw : total (weightFunction B) (realizePopulation P) =
      ∑ u : Fin (μ : ℕ), weight (distance B (P u)) := by
    unfold total realizePopulation
    simp only [weightFunction_toString]
  rw [← hw] at h
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have h' := congrArg (fun x : ℝ ↦ (μ : ℕ) * x) h
  rw [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul] at h'
  exact h'

lemma ratio_empirical {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    ratio (weightFunction B) (toString B) (realizePopulation P) =
      cloud B (fun x ↦ (empirical P x).toReal) / (empirical P B).toReal := by
  unfold ratio
  rw [total_empirical, count_empirical]
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  rw [mul_div_mul_left _ _ hμ.ne']

lemma accepted_indicator {n k : ℕ} (B : Genotype n k) :
    (fun z ↦ if onPlateau k z then indicator (toString B) z else 0) = acceptedClone B := by
  funext z
  rw [Lax343628Proofs.AnchorMutation.acceptedClone_indicator]
  by_cases hp : onPlateau k z
  · simp [hp, indicator]
  · have hz : z ≠ toString B := by
      intro hz
      rw [hz] at hp
      exact hp (toString_onPlateau B)
    simp [hp, hz]

lemma offspring_contrast {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k)
    (B : Genotype n k) (p_c : ℝ) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) :
    let Q := ratio (weightFunction B) (toString B) (realizePopulation P)
    mean (offspring p_c (realizePopulation P))
      (fun z ↦ if onPlateau k z then weightFunction B z else 0) -
        Q * mean (offspring p_c (realizePopulation P))
          (fun z ↦ if onPlateau k z then indicator (toString B) z else 0) =
      p_c * (pairMean (empirical P) (weightedBirth B) -
        Q * pairMean (empirical P) (cloneBirth B)) +
      (1 - p_c) * (mean (empirical P) (fun x ↦ weightedBirth B x x) -
        Q * mean (empirical P) (fun x ↦ cloneBirth B x x)) := by
  dsimp only
  rw [accepted_indicator]
  change mean (offspring p_c (fun u ↦ toString (P u))) (acceptedWeight B) -
    ratio (weightFunction B) (toString B) (realizePopulation P) *
      mean (offspring p_c (fun u ↦ toString (P u))) (acceptedClone B) = _
  rw [empirical_offspring_weight p_c hp_c P B, empirical_offspring_clone p_c hp_c P B]
  ring

lemma entry_ratio_drift {n k : ℕ} {μ : ℕ+} {p0 : ℝ}
    (hcond : Lax343628Proofs.EntryBounds.Conditions n k p0)
    (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k)
    (p_c : ℝ) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1)
    (hN : 1 < count (toString B) (realizePopulation P))
    (hpmin : p0 ≤ (empirical P B).toReal)
    (hiso : ratio (weightFunction B) (toString B) (realizePopulation P) ≤ 1 / 25) :
    p0 * (k : ℝ) / (64 * n * ((μ : ℕ) + 1)) ≤
      mean (auxiliaryStep k p_c (realizePopulation P)) (fun Q ↦
        ratio (weightFunction B) (toString B) Q -
          ratio (weightFunction B) (toString B) (realizePopulation P)) := by
  have hkn : k ≤ n := by have h := hcond.dimension_four_jump; omega
  have hbirth := Lax343628Proofs.EntryBounds.mixture_entry_lower hcond B (empirical P) hpmin
    (by rwa [← ratio_empirical]) p_c hp_c
  dsimp only at hbirth
  rw [← ratio_empirical, ← offspring_contrast P B p_c hp_c] at hbirth
  have hpoint := auxiliary_ratio_drift_lower hkn (weightFunction B) (toString B)
    (weightFunction_anchor B) (weightFunction_bounds B) p_c (realizePopulation P)
    (realize_plateau P) hN
  have hμplus : (0 : ℝ) < (μ : ℕ) + 1 := by positivity
  have hNpos : 0 < count (toString B) (realizePopulation P) := by linarith
  have hcoef : (1 : ℝ) / ((μ : ℕ) + 1) ≤
      ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ)) / count (toString B) (realizePopulation P) := by
    apply (div_le_div_iff₀ hμplus hNpos).mpr
    rw [div_mul_cancel₀ _ hμplus.ne', one_mul]
    exact count_le_size _ _
  have hdelta : 0 ≤ p0 * (k : ℝ) / (64 * n) := by
    have hp0 := hcond.threshold_pos
    positivity
  have hcoef0 := (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hμplus.le).trans hcoef
  have h1 := mul_le_mul_of_nonneg_left hbirth hcoef0
  have h2 := mul_le_mul_of_nonneg_right hcoef hdelta
  have hfin := h2.trans (h1.trans hpoint)
  convert hfin using 1 <;> first
    | rfl
    | (simp only [div_eq_mul_inv, mul_inv_rev]; ring)

def genotypePopulation {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n)
    (P : Population n μ) (hP : plateauPopulation k P) : Fin (μ : ℕ) → Genotype n k :=
  fun u ↦ ofString (P u) (by
    rw [card_zeros]
    have hu : ones (P u) = n - k := hP u
    rw [hu]
    omega)

lemma realize_genotypePopulation {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n)
    (P : Population n μ) (hP : plateauPopulation k P) :
    realizePopulation (genotypePopulation hkn P hP) = P := by
  funext u
  exact toString_ofString _ _

lemma plateau_entry_ratio_drift {n k : ℕ} {μ : ℕ+} {p0 : ℝ}
    (hcond : Lax343628Proofs.EntryBounds.Conditions n k p0)
    (P : Population n μ) (hP : plateauPopulation k P) (B : Genotype n k)
    (p_c : ℝ) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (hN : 1 < count (toString B) P)
    (hpmin : (μ : ℕ) * p0 ≤ count (toString B) P)
    (hiso : ratio (weightFunction B) (toString B) P ≤ 1 / 25) :
    p0 * (k : ℝ) / (64 * n * ((μ : ℕ) + 1)) ≤
      mean (auxiliaryStep k p_c P) (fun Q ↦
        ratio (weightFunction B) (toString B) Q - ratio (weightFunction B) (toString B) P) := by
  have hkn : k ≤ n := by have h := hcond.dimension_four_jump; omega
  let G := genotypePopulation hkn P hP
  have hG : realizePopulation G = P := realize_genotypePopulation hkn P hP
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hfreq : p0 ≤ (empirical G B).toReal := by
    apply (mul_le_mul_iff_of_pos_left hμ).mp
    rw [← count_empirical G B, hG]
    exact hpmin
  have h := entry_ratio_drift hcond G B p_c hp_c (by simpa only [hG] using hN)
    hfreq (by simpa only [hG] using hiso)
  simpa only [hG] using h

lemma ratio_drift_of_birth {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n)
    (P : Population n μ) (hP : plateauPopulation k P) (B : Genotype n k) (p_c : ℝ)
    (hN : 1 < count (toString B) P) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbirth : δ ≤ mean (offspring p_c P) (acceptedWeight B) -
      ratio (weightFunction B) (toString B) P * mean (offspring p_c P) (acceptedClone B)) :
    δ / ((μ : ℕ) + 1) ≤ mean (auxiliaryStep k p_c P) (fun Q ↦
      ratio (weightFunction B) (toString B) Q - ratio (weightFunction B) (toString B) P) := by
  have hpoint := auxiliary_ratio_drift_lower hkn (weightFunction B) (toString B)
    (weightFunction_anchor B) (weightFunction_bounds B) p_c P hP hN
  rw [accepted_indicator] at hpoint
  change (((μ : ℕ) / ((μ : ℕ) + 1 : ℝ)) / count (toString B) P) *
    (mean (offspring p_c P) (acceptedWeight B) -
      ratio (weightFunction B) (toString B) P * mean (offspring p_c P) (acceptedClone B)) ≤ _ at hpoint
  have hμplus : (0 : ℝ) < (μ : ℕ) + 1 := by positivity
  have hNpos : 0 < count (toString B) P := by linarith
  have hcoef : (1 : ℝ) / ((μ : ℕ) + 1) ≤
      ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ)) / count (toString B) P := by
    apply (div_le_div_iff₀ hμplus hNpos).mpr
    rw [div_mul_cancel₀ _ hμplus.ne', one_mul]
    exact count_le_size _ _
  have hcoef0 := (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hμplus.le).trans hcoef
  have h1 := mul_le_mul_of_nonneg_left hbirth hcoef0
  have h2 := mul_le_mul_of_nonneg_right hcoef hδ
  have hfin := h2.trans (h1.trans hpoint)
  simpa only [one_div_mul_eq_div] using hfin

end
end Lax343628Proofs.SpeciesState
