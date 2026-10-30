import Lax343628Proofs.CloneBirthDrift

namespace Lax343628Proofs.CloneProtection

open Lax343628.Algorithm Lax343628Proofs.Genotypes Lax343628Proofs.Species
open Lax343628Proofs.CloneBirthDrift Lax343628Proofs.EntryBounds
open Lax343628Proofs.SpeciesState Lax343628Proofs.PopulationRatio
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.Deletion Lax343628Proofs.Sampling
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.ActualBirthKernels
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.PlateauKernelApproximation Lax343628Proofs.BoundedBarrier
open Lax343628Proofs.Trajectories
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

structure Conditions (n k : ℕ) (p_c p0 : ℝ) : Prop where
  entry : EntryBounds.Conditions n k p0
  small_frequency : p0 ≤ 1 / (16 * Real.sqrt k)
  approximation : approximationError n k ≤ Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 16
  return_mutation : (1 / (n : ℝ)) ^ 2 ≤ p_c * Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 8

def countDrift (k : ℕ) (p_c p0 : ℝ) : ℝ :=
  p_c * Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 16

def countBand {n k : ℕ} {μ : ℕ+} (B : Genotype n k) (p0 : ℝ) : Set (Population n μ) :=
  {P | plateauPopulation k P ∧ (μ : ℕ) * p0 < count (toString B) P ∧
    count (toString B) P ≤ 2 * (μ : ℕ) * p0 ∧ ratio (weightFunction B) (toString B) P ≤ 1 / 25}

lemma empirical_count_drift {n k : ℕ} {μ : ℕ+} (hkn : k ≤ n)
    (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) (p_c : ℝ) :
    mean (auxiliaryStep k p_c (realizePopulation P))
      (fun Q ↦ count (toString B) Q - count (toString B) (realizePopulation P)) =
      ((μ : ℕ) / ((μ : ℕ) + 1 : ℝ)) *
        (mean (offspring p_c (realizePopulation P)) (acceptedClone B) -
          (empirical P B).toReal * mean (offspring p_c (realizePopulation P))
            (fun z ↦ if onPlateau k z then 1 else 0)) := by
  change mean (auxiliaryStep k p_c (realizePopulation P))
    (fun Q ↦ total (indicator (toString B)) Q - total (indicator (toString B)) (realizePopulation P)) = _
  rw [auxiliary_statistic_drift hkn _ p_c _ (realize_plateau P), accepted_indicator]
  have hc := count_empirical P B
  change total (indicator (toString B)) (realizePopulation P) = _ at hc
  rw [hc]
  ring

lemma count_band_decline {n k : ℕ} {μ : ℕ+} {p0 p_c : ℝ} (hcond : Conditions n k p_c p0)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (B : Genotype n k) (P : Population n μ)
    (hP : P ∈ countBand B p0) :
    mean (auxiliaryStep k p_c P) (fun Q ↦ count (toString B) Q - count (toString B) P) ≤
      -countDrift k p_c p0 := by
  have hkn : k ≤ n := by have h := hcond.entry.dimension_four_jump; omega
  let G := genotypePopulation hkn P hP.1
  have hG : realizePopulation G = P := realize_genotypePopulation hkn P hP.1
  have hμpos : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hcount := count_empirical G B
  rw [hG] at hcount
  have hfreq : p0 ≤ (empirical G B).toReal := by
    apply (mul_le_mul_iff_of_pos_left hμpos).mp
    rw [← hcount]
    exact hP.2.1.le
  have hfreqmax : (empirical G B).toReal ≤ 2 * p0 := by
    apply (mul_le_mul_iff_of_pos_left hμpos).mp
    rw [← hcount]
    nlinarith [hP.2.2.1]
  have hmax : (empirical G B).toReal ≤ 1 / (8 * Real.sqrt k) := by
    have hsmall := hcond.small_frequency
    ring_nf at hsmall ⊢
    nlinarith
  have hmix := mixed_clone_decline hcond.entry.dimension_two hcond.entry.jump_pos
    hcond.entry.dimension_four_jump B (empirical G) p0 p_c hcond.entry.threshold_pos hp_c hfreq hmax
    (by rw [← ratio_empirical, hG]; exact hP.2.2.2) hcond.approximation hcond.return_mutation
  have hbirth : mean (offspring p_c (realizePopulation G)) (acceptedClone B) -
      (empirical G B).toReal * mean (offspring p_c (realizePopulation G))
        (fun z ↦ if onPlateau k z then 1 else 0) ≤
      -(p_c * Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 8) := by
    change mean (offspring p_c (fun u ↦ toString (G u))) (acceptedClone B) -
      (empirical G B).toReal * mean (offspring p_c (fun u ↦ toString (G u)))
        (fun z ↦ if onPlateau k z then 1 else 0) ≤ _
    rw [empirical_offspring_clone p_c hp_c G B, empirical_offspring_viability p_c hp_c G]
    convert hmix using 1; first | rfl | ring
  have hμone : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hfactor : (1 / 2 : ℝ) ≤ (μ : ℕ) / ((μ : ℕ) + 1 : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (μ : ℕ) + 1)).mpr
    nlinarith
  have hnonneg : 0 ≤ p_c * Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 8 := by
    have hpc0 := hp_c.1
    have hp0 := hcond.entry.threshold_pos
    positivity
  have hscale := mul_le_mul_of_nonneg_left hbirth
    (show 0 ≤ (μ : ℕ) / ((μ : ℕ) + 1 : ℝ) by positivity)
  have hscale2 := mul_le_mul_of_nonneg_right hfactor hnonneg
  rw [← empirical_count_drift hkn G B p_c, hG] at hscale
  unfold countDrift
  nlinarith

lemma countDrift_bounds {n k : ℕ} {p0 p_c : ℝ} (hcond : Conditions n k p_c p0)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) : 0 ≤ countDrift k p_c p0 ∧ countDrift k p_c p0 ≤ 1 := by
  have hp0 := hcond.entry.threshold_pos
  have hpc := hp_c.1
  have hexp : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt k := by
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast hcond.entry.jump_pos
    simpa using Real.sqrt_le_sqrt hk
  have hV : (1 : ℝ) / (2 * Real.sqrt k) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * Real.sqrt k)).mpr
    linarith
  have h1 : p_c * Real.exp (-1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hexp hpc).trans (by simpa using hp_c.2)
  have h2 : p_c * Real.exp (-1) * p0 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hcond.entry.threshold_le_one
      (show 0 ≤ p_c * Real.exp (-1) by positivity)
    nlinarith
  have h3 : p_c * Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hV
      (show 0 ≤ p_c * Real.exp (-1) * p0 by positivity)
    nlinarith
  unfold countDrift
  constructor
  · positivity
  · linarith

lemma count_band_rising {n k : ℕ} {μ : ℕ+} {p0 p_c : ℝ} (hcond : Conditions n k p_c p0)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (B : Genotype n k) (P : Population n μ)
    (hP : P ∈ countBand B p0) :
    countDrift k p_c p0 ≤ mean (auxiliaryStep k p_c P)
      (fun Q ↦ -count (toString B) Q - -count (toString B) P) := by
  have hfun : (fun Q : Population n μ ↦ -count (toString B) Q - -count (toString B) P) =
      (fun Q ↦ (-1 : ℝ) * (count (toString B) Q - count (toString B) P)) := by funext Q; ring
  rw [hfun, mean_mul]
  nlinarith [count_band_decline hcond hp_c B P hP]

lemma count_path_barrier {n k : ℕ} {μ : ℕ+} {p0 p_c : ℝ} (hcond : Conditions n k p_c p0)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (B : Genotype n k) (P : Population n μ) (t : ℕ) :
    (pathLaw (auxiliaryStep k p_c) (PMF.pure P) t).toOuterMeasure
      {h | 2 * (μ : ℕ) * p0 < count (toString B) (frozen (countBand B p0) h)} ≤
      ENNReal.ofReal (Real.exp (-countDrift k p_c p0 *
        (2 * (μ : ℕ) * p0 - count (toString B) P))) := by
  have hδ := countDrift_bounds hcond hp_c
  have hstep : ∀ X : Population n μ, X ∈ countBand B p0 → ∀ Y ∈ (auxiliaryStep k p_c X).support,
      |(-count (toString B) Y) - (-count (toString B) X)| ≤ 1 := by
    intro X _ Y hY
    rw [show -count (toString B) Y - -count (toString B) X =
      -(count (toString B) Y - count (toString B) X) by ring, abs_neg]
    exact auxiliary_count_abs _ p_c X Y hY
  have h := bounded_positive_barrier (auxiliaryStep k p_c) (countBand B p0)
    (fun X ↦ -count (toString B) X) 1 (countDrift k p_c p0) (by norm_num) hδ.1 hδ.2
    hstep (count_band_rising hcond hp_c B) P (-(2 * (μ : ℕ) * p0)) t
  simpa only [one_pow, div_one, neg_lt_neg_iff, neg_sub_neg] using h

end
end Lax343628Proofs.CloneProtection
