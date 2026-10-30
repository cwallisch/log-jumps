import Lax343628Proofs.SpeciesEntry
import Lax343628Proofs.BoundedBarrier
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Lax343628Proofs.SpeciesProtection

open Lax343628.Algorithm Lax343628Proofs.Genotypes Lax343628Proofs.Species
open Lax343628Proofs.ActualBirthKernels Lax343628Proofs.EmpiricalKernels
open Lax343628Proofs.SpeciesEnvelope Lax343628Proofs.PlateauKernelApproximation
open Lax343628Proofs.EntryBounds Lax343628Proofs.SpeciesState
open Lax343628Proofs.PopulationRatio Lax343628Proofs.PlateauDynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.BoundedBarrier Lax343628Proofs.Trajectories
open Lax343628Proofs.Sampling
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def strictConstant : ℝ := 1 / 1000000

lemma strictConstant_pos : 0 < strictConstant := by norm_num [strictConstant]

lemma strictConstant_le_one : strictConstant ≤ 1 := by norm_num [strictConstant]

lemma strict_crossed_birth {n k : ℕ} {p0 : ℝ} (hcond : Conditions n k p0)
    (herror : (129 / 100 : ℝ) * approximationError n k ≤ strictConstant * p0 ^ 2)
    (B : Genotype n k) (p : PMF (Genotype n k)) (hpmin : p0 ≤ (p B).toReal)
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25)
    (hentry : 1 / 50 ≤ cloud B (fun x ↦ (p x).toReal) / (p B).toReal) :
    let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
    strictConstant * p0 ^ 2 ≤ pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B) := by
  dsimp only
  let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
  have hp0 := hcond.threshold_pos
  have hpB : 0 < (p B).toReal := hp0.trans_le hpmin
  have hactual := crossed_strict_drift hcond.dimension_two hcond.dimension_four_jump
    B p hpB hiso hentry
  dsimp only at hactual
  have hsq : p0 ^ 2 ≤ (p B).toReal ^ 2 := (sq_le_sq₀ hp0.le hpB.le).mpr hpmin
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hprod : (1 / 50 : ℝ) * p0 ^ 2 ≤ Q * (p B).toReal ^ 2 :=
    mul_le_mul hentry hsq (sq_nonneg p0) hQ
  have hscale := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ Real.exp (-1) * (337 / 10000 : ℝ) * (1 / 50) by positivity)
  have hcoefficient : 2 * strictConstant ≤
      Real.exp (-1) * (337 / 10000 : ℝ) * (1 / 50) ^ 2 := by
    unfold strictConstant
    nlinarith [Real.exp_neg_one_gt_d9]
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg p0)
  have hother := mul_nonneg (Real.exp_nonneg (-1))
    (otherPair_nonneg B (fun x ↦ (p x).toReal) (fun _ ↦ ENNReal.toReal_nonneg))
  have herrnonneg : 0 ≤ approximationError n k := by unfold approximationError; positivity
  have herrbound : (5 / 4 + Q) * approximationError n k ≤ strictConstant * p0 ^ 2 := by
    exact (mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) herrnonneg).trans herror
  dsimp only [Q] at *
  nlinarith

lemma strict_mixed_birth {n k : ℕ} {p0 : ℝ} (hcond : Conditions n k p0)
    (herror : (129 / 100 : ℝ) * approximationError n k ≤ strictConstant * p0 ^ 2)
    (B : Genotype n k) (p : PMF (Genotype n k)) (hpmin : p0 ≤ (p B).toReal)
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25)
    (hentry : 1 / 50 ≤ cloud B (fun x ↦ (p x).toReal) / (p B).toReal)
    (p_c : ℝ) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) :
    let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
    p_c * strictConstant * p0 ^ 2 ≤
      p_c * (pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B)) +
        (1 - p_c) * (mean p (fun x ↦ weightedBirth B x x) -
          Q * mean p (fun x ↦ cloneBirth B x x)) := by
  dsimp only
  have hcross := strict_crossed_birth hcond herror B p hpmin hiso hentry
  dsimp only at hcross
  have hmut := mixture_entry_lower hcond B p hpmin hiso 0 (by norm_num)
  dsimp only at hmut
  norm_num only [zero_mul, sub_zero, one_mul, zero_add] at hmut
  have hp0 := hcond.threshold_pos
  have hmut0 := (show 0 ≤ p0 * (k : ℝ) / (64 * n) by positivity).trans hmut
  have h1 := mul_le_mul_of_nonneg_left hcross hp_c.1
  have h2 := mul_nonneg (sub_nonneg.mpr hp_c.2) hmut0
  nlinarith

def ratioBand {n k : ℕ} {μ : ℕ+} (B : Genotype n k) (p0 : ℝ) : Set (Population n μ) :=
  {P | plateauPopulation k P ∧ (μ : ℕ) * p0 < count (toString B) P ∧
    1 / 50 ≤ ratio (weightFunction B) (toString B) P ∧
      ratio (weightFunction B) (toString B) P ≤ 1 / 25}

def ratioDrift (μ : ℕ+) (p_c p0 : ℝ) : ℝ := p_c * strictConstant * p0 ^ 2 / ((μ : ℕ) + 1)

def ratioStep (μ : ℕ+) (p0 : ℝ) : ℝ := 3 / ((μ : ℕ) * p0)

lemma ratio_band_drift {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (hcond : Conditions n k p0)
    (herror : (129 / 100 : ℝ) * approximationError n k ≤ strictConstant * p0 ^ 2)
    (hμ : 200 ≤ (μ : ℕ) * p0) (B : Genotype n k) (p_c : ℝ)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (P : Population n μ) (hP : P ∈ ratioBand B p0) :
    ratioDrift μ p_c p0 ≤ mean (auxiliaryStep k p_c P) (fun Q ↦
      ratio (weightFunction B) (toString B) Q - ratio (weightFunction B) (toString B) P) := by
  have hkn : k ≤ n := by have h := hcond.dimension_four_jump; omega
  let G := genotypePopulation hkn P hP.1
  have hG : realizePopulation G = P := realize_genotypePopulation hkn P hP.1
  have hμpos : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hfreq : p0 ≤ (empirical G B).toReal := by
    apply (mul_le_mul_iff_of_pos_left hμpos).mp
    rw [← count_empirical G B, hG]
    exact hP.2.1.le
  have hmix := strict_mixed_birth hcond herror B (empirical G) hfreq
    (by rw [← ratio_empirical, hG]; exact hP.2.2.2)
    (by rw [← ratio_empirical, hG]; exact hP.2.2.1) p_c hp_c
  dsimp only at hmix
  rw [← ratio_empirical, ← offspring_contrast G B p_c hp_c, hG, accepted_indicator] at hmix
  change p_c * strictConstant * p0 ^ 2 ≤ mean (offspring p_c P) (acceptedWeight B) -
    ratio (weightFunction B) (toString B) P * mean (offspring p_c P) (acceptedClone B) at hmix
  exact ratio_drift_of_birth hkn P hP.1 B p_c (by linarith [hP.2.1])
    (p_c * strictConstant * p0 ^ 2)
    (mul_nonneg (mul_nonneg hp_c.1 strictConstant_pos.le) (sq_nonneg p0)) hmix

lemma ratio_band_step {n k : ℕ} {μ : ℕ+} {p0 : ℝ}
    (hμ : 200 ≤ (μ : ℕ) * p0) (B : Genotype n k) (p_c : ℝ)
    (P : Population n μ) (hP : P ∈ ratioBand B p0) (Q : Population n μ)
    (hQ : Q ∈ (auxiliaryStep k p_c P).support) :
    |ratio (weightFunction B) (toString B) Q - ratio (weightFunction B) (toString B) P| ≤
      ratioStep μ p0 := by
  have hN : 200 < count (toString B) P := lt_of_le_of_lt hμ hP.2.1
  have hstep := auxiliary_ratio_abs (weightFunction B) (toString B) (weightFunction_anchor B)
    (weightFunction_bounds B) p_c P (by linarith) Q hQ
  apply hstep.trans
  unfold ratioStep
  apply (div_le_div_iff₀ (by linarith : 0 < count (toString B) P - 1)
    (by linarith : (0 : ℝ) < (μ : ℕ) * p0)).mpr
  have hQupper := mul_le_mul_of_nonneg_right hP.2.2.2
    (show (0 : ℝ) ≤ (μ : ℕ) * p0 by linarith)
  nlinarith [hP.2.1]

lemma ratio_parameters {μ : ℕ+} {p0 p_c : ℝ} (hp0 : 0 < p0) (hp01 : p0 ≤ 1)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) :
    0 < ratioStep μ p0 ∧ 0 ≤ ratioDrift μ p_c p0 ∧ ratioDrift μ p_c p0 ≤ ratioStep μ p0 := by
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hD := strictConstant_pos
  have hpc0 := hp_c.1
  have hp0sq : p0 ^ 2 ≤ 1 := by nlinarith
  have hpcD : p_c * strictConstant ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hp_c.2 hD.le
    nlinarith [strictConstant_le_one]
  have hcoef : p_c * strictConstant * p0 ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hp0sq (show 0 ≤ p_c * strictConstant by positivity)
    nlinarith
  have hden : (μ : ℕ) * p0 ≤ (μ : ℕ) + (1 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hp01 hμ.le
    nlinarith
  constructor
  · unfold ratioStep
    positivity
  constructor
  · unfold ratioDrift
    positivity
  · unfold ratioDrift ratioStep
    calc
      _ ≤ 1 / ((μ : ℕ) + (1 : ℝ)) := div_le_div_of_nonneg_right hcoef (by positivity)
      _ ≤ 1 / ((μ : ℕ) * p0) := one_div_le_one_div_of_le (by positivity) hden
      _ ≤ 3 / ((μ : ℕ) * p0) := div_le_div_of_nonneg_right (by norm_num) (by positivity)

lemma ratio_path_barrier {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (hcond : Conditions n k p0)
    (herror : (129 / 100 : ℝ) * approximationError n k ≤ strictConstant * p0 ^ 2)
    (hμ : 200 ≤ (μ : ℕ) * p0) (B : Genotype n k) (p_c : ℝ)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (P : Population n μ) (t : ℕ) :
    (pathLaw (auxiliaryStep k p_c) (PMF.pure P) t).toOuterMeasure
      {h | ratio (weightFunction B) (toString B) (frozen (ratioBand B p0) h) < 1 / 50} ≤
      ENNReal.ofReal (Real.exp (-(ratioDrift μ p_c p0 / ratioStep μ p0 ^ 2) *
        (ratio (weightFunction B) (toString B) P - 1 / 50))) := by
  have hpar := ratio_parameters (μ := μ) hcond.threshold_pos hcond.threshold_le_one hp_c
  exact bounded_positive_barrier (auxiliaryStep k p_c) (ratioBand B p0)
    (ratio (weightFunction B) (toString B)) (ratioStep μ p0) (ratioDrift μ p_c p0)
    hpar.1 hpar.2.1 hpar.2.2 (ratio_band_step hμ B p_c)
    (ratio_band_drift hcond herror hμ B p_c hp_c) P (1 / 50) t

end
end Lax343628Proofs.SpeciesProtection
