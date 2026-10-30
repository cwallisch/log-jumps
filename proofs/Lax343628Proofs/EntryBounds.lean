import Lax343628Proofs.SpeciesEnvelope

namespace Lax343628Proofs.EntryBounds

open Lax343628Proofs.Genotypes Lax343628Proofs.Weights Lax343628Proofs.Species
open Lax343628Proofs.SpeciesEnvelope Lax343628Proofs.MutationDrift
open Lax343628Proofs.ActualBirthKernels Lax343628Proofs.EmpiricalKernels
open Lax343628Proofs.PlateauKernelApproximation Lax343628Proofs.FiniteDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma quadratic_seed_gain (A G E p : ℝ) (hA : 0 < A) (hG : 0 ≤ G) (hE : 0 ≤ E)
    (_hp : 0 ≤ p) (hp1 : p ≤ 1) (hAG : 2 * G ≤ A) (hsmall : 8 * E ^ 2 ≤ A * G) :
    G / 4 ≤ A * (1 - p) ^ 2 + G * p ^ 2 - (1 - p ^ 2) * E := by
  have hf : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have henergy : G / 2 ≤ A / 2 * (1 - p) ^ 2 + G * p ^ 2 := by
    have hcoef := mul_le_mul_of_nonneg_right hAG (sq_nonneg (1 - p))
    have hshape := mul_nonneg hG (sq_nonneg (2 * p - 1))
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left henergy hA.le
  have hsquare := sq_nonneg (A * (1 - p) - 2 * E)
  have hprod : A * (G / 4) ≤
      A * (A * (1 - p) ^ 2 + G * p ^ 2 - 2 * (1 - p) * E) := by
    nlinarith
  have hbase := (mul_le_mul_iff_of_pos_left hA).mp hprod
  have hextra := mul_nonneg (sq_nonneg (1 - p)) hE
  nlinarith

lemma crossed_entry_lower {n k : ℕ} (hk : 1 ≤ k) (hlarge : 4 * k ≤ n) (hn : 2 ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) (p0 : ℝ) (hp0 : 0 < p0) (hp01 : p0 ≤ 1)
    (hpmin : p0 ≤ (p B).toReal)
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25)
    (hAG : 2 * ((k : ℝ) / (16 * n)) ≤ Real.exp (-1) * (p0 * (4 : ℝ)⁻¹ ^ k / 100))
    (hsmall : 8 * ((129 / 100 : ℝ) * approximationError n k) ^ 2 ≤
      (Real.exp (-1) * (p0 * (4 : ℝ)⁻¹ ^ k / 100)) * ((k : ℝ) / (16 * n))) :
    let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
    (k : ℝ) / (64 * n) ≤ pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B) := by
  dsimp only
  have hpB : 0 < (p B).toReal := hp0.trans_le hpmin
  let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
  have hQ : 0 ≤ Q := div_nonneg (cloud_nonneg B _ (fun _ ↦ ENNReal.toReal_nonneg)) hpB.le
  have herror : 0 ≤ approximationError n k := by unfold approximationError; positivity
  have hbound : (5 / 4 + Q) * approximationError n k ≤
      (129 / 100 : ℝ) * approximationError n k := by
    exact mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) herror
  have hp1 : (p B).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using p.coe_le_one B)
  have hquad := ideal_quadratic_drift B p p0 hp0.le hp01 hpB hpmin hiso
  have hquad' := mul_le_mul_of_nonneg_left hquad (Real.exp_nonneg (-1))
  have hcross := crossed_ratio_seed_lower hk hlarge hn B p Q hQ
  have herror' := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ 1 - (p B).toReal ^ 2 by nlinarith [ENNReal.toReal_nonneg (a := p B)])
  have hgain := quadratic_seed_gain
    (Real.exp (-1) * (p0 * (4 : ℝ)⁻¹ ^ k / 100))
    ((k : ℝ) / (16 * n)) ((129 / 100 : ℝ) * approximationError n k) (p B).toReal
    (by positivity) (by positivity) (by positivity) ENNReal.toReal_nonneg hp1 hAG hsmall
  have heq : ((k : ℝ) / (16 * n)) / 4 = (k : ℝ) / (64 * n) := by ring
  rw [heq] at hgain
  dsimp only [Q] at hcross herror' hbound hQ
  nlinarith

structure Conditions (n k : ℕ) (p0 : ℝ) : Prop where
  jump_pos : 1 ≤ k
  dimension_two : 2 ≤ n
  dimension_four_jump : 4 * k ≤ n
  threshold_pos : 0 < p0
  threshold_le_one : p0 ≤ 1
  gain_le_quadratic : 2 * ((k : ℝ) / (16 * n)) ≤
    Real.exp (-1) * (p0 * (4 : ℝ)⁻¹ ^ k / 100)
  squared_error : 8 * ((129 / 100 : ℝ) * approximationError n k) ^ 2 ≤
    (Real.exp (-1) * (p0 * (4 : ℝ)⁻¹ ^ k / 100)) * ((k : ℝ) / (16 * n))
  mutation_error : (1 / (n : ℝ)) ^ 2 ≤ p0 * (k : ℝ) / (32 * n)

lemma mixture_entry_lower {n k : ℕ} {p0 : ℝ} (hcond : Conditions n k p0)
    (B : Genotype n k) (p : PMF (Genotype n k)) (hpmin : p0 ≤ (p B).toReal)
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25)
    (p_c : ℝ) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) :
    let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
    p0 * (k : ℝ) / (64 * n) ≤
      p_c * (pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B)) +
        (1 - p_c) * (mean p (fun x ↦ weightedBirth B x x) -
          Q * mean p (fun x ↦ cloneBirth B x x)) := by
  dsimp only
  let Q := cloud B (fun x ↦ (p x).toReal) / (p B).toReal
  have hpB : 0 < (p B).toReal := hcond.threshold_pos.trans_le hpmin
  have hp0 := hcond.threshold_pos
  have hlarge := hcond.dimension_four_jump
  have hQ : 0 ≤ Q := div_nonneg (cloud_nonneg B _ (fun _ ↦ ENNReal.toReal_nonneg)) hpB.le
  have hQ1 : Q ≤ 1 := by dsimp [Q]; linarith
  have hcancel : cloud B (fun x ↦ (p x).toReal) = Q * (p B).toReal := by
    dsimp [Q]
    rw [div_mul_cancel₀ _ hpB.ne']
  have hcross := crossed_entry_lower hcond.jump_pos hcond.dimension_four_jump hcond.dimension_two
    B p p0 hcond.threshold_pos hcond.threshold_le_one hpmin hiso
    hcond.gain_le_quadratic hcond.squared_error
  have hmut := mutation_ratio_lower hcond.jump_pos (by omega : 2 * k ≤ n)
    hcond.dimension_two B p Q hQ hcancel
  have herror := (mul_le_mul_of_nonneg_right hQ1 (sq_nonneg (1 / (n : ℝ)))).trans
    (by simpa only [one_mul] using hcond.mutation_error)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have h := hcond.dimension_two; omega)
  have hscale := mul_le_mul_of_nonneg_right hpmin
    (show (0 : ℝ) ≤ (k : ℝ) / (16 * n) by positivity)
  have hmut' : p0 * (k : ℝ) / (64 * n) ≤
      mean p (fun x ↦ weightedBirth B x x) - Q * mean p (fun x ↦ cloneBirth B x x) := by
    have hpos : 0 ≤ p0 * (k : ℝ) / (64 * n) := by positivity
    ring_nf at hmut herror hscale hpos ⊢
    nlinarith
  have hcross' : p0 * (k : ℝ) / (64 * n) ≤
      pairMean p (weightedBirth B) - Q * pairMean p (cloneBirth B) := by
    have h := mul_le_mul_of_nonneg_right hcond.threshold_le_one
      (show (0 : ℝ) ≤ (k : ℝ) / (64 * n) by positivity)
    have h' : p0 * (k : ℝ) / (64 * n) ≤ (k : ℝ) / (64 * n) := by
      simpa only [mul_div_assoc, one_mul] using h
    exact h'.trans hcross
  have h1 := mul_le_mul_of_nonneg_left hcross' hp_c.1
  have h2 := mul_le_mul_of_nonneg_left hmut' (sub_nonneg.mpr hp_c.2)
  dsimp only [Q] at *
  nlinarith

end
end Lax343628Proofs.EntryBounds
