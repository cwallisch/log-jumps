import Lax343628Proofs.SpeciesProtection

namespace Lax343628Proofs.CloneBirthDrift

open Lax343628.Algorithm Lax343628Proofs.Genotypes Lax343628Proofs.Species
open Lax343628Proofs.Weights Lax343628Proofs.ActualBirthKernels
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.SpeciesEnvelope
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.AnchorMutation Lax343628Proofs.IdealCountKernel
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.PlateauKernelApproximation
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma isolated_clone_kernel_upper {n k : ℕ} (B : Genotype n k) (p : PMF (Genotype n k))
    (hpB : 0 < (p B).toReal)
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25) :
    pairValue (fun x ↦ (p x).toReal) (cloneKernel B) ≤ 2 * (p B).toReal ^ 2 := by
  let f : Genotype n k → ℝ := fun x ↦ (p x).toReal
  have hf : ∀ x, 0 ≤ f x := fun _ ↦ ENNReal.toReal_nonneg
  have hcopy : copyMass B f ≤ cloud B f := by
    unfold copyMass cloud cloudValue
    apply offSum_mono
    intro x hx
    exact mul_le_mul_of_nonneg_left (copy_le_weight (distance_pos B x hx)) (hf x)
  have hcloud : cloud B f ≤ f B / 25 := by
    have h := (div_le_iff₀ hpB).mp hiso
    dsimp [f]
    nlinarith
  have hrho := hcopy.trans hcloud
  have hrho0 := copyMass_nonneg B f hf
  have hrhosq : copyMass B f ^ 2 ≤ (f B / 25) ^ 2 :=
    (sq_le_sq₀ hrho0 (by positivity)).mpr hrho
  have hpair := (copyPair_bound B f hf).trans hrhosq
  have hcross := mul_le_mul_of_nonneg_left hrho (hpB.le)
  rw [clone_pair_value]
  change f B ^ 2 + 2 * f B * copyMass B f + copyPair B f ≤ _
  nlinarith [sq_nonneg (f B)]

lemma crossed_clone_decline {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hlarge : 4 * k ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) (p0 : ℝ) (hp0 : 0 < p0)
    (hpmin : p0 ≤ (p B).toReal)
    (hpmax : (p B).toReal ≤ 1 / (8 * Real.sqrt k))
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25)
    (herror : approximationError n k ≤ Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 16) :
    pairMean p (cloneBirth B) - (p B).toReal * pairMean p viableBirth ≤
      -(Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 4) := by
  have hpB : 0 < (p B).toReal := hp0.trans_le hpmin
  have hp1 : (p B).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using p.coe_le_one B)
  have hclone := (abs_le.mp (population_clone_birth_error hn hlarge B p)).2
  have hideal := mul_le_mul_of_nonneg_left (isolated_clone_kernel_upper B p hpB hiso)
    (Real.exp_nonneg (-1))
  have hv := mul_le_mul_of_nonneg_left (crossed_viability_lower hn hk hlarge p) hpB.le
  have hE : 0 ≤ approximationError n k := by unfold approximationError; positivity
  have hEscale := mul_le_mul_of_nonneg_right hp1 hE
  have hpmax' : 2 * (p B).toReal ≤ (1 / (2 * Real.sqrt k)) / 2 := by
    ring_nf at hpmax ⊢
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hpmax'
    (show 0 ≤ Real.exp (-1) * (p B).toReal by positivity)
  have hp0prod := mul_le_mul_of_nonneg_right hpmin
    (show 0 ≤ Real.exp (-1) * (1 / (2 * Real.sqrt k)) by positivity)
  nlinarith

lemma mutation_viability_lower {n k : ℕ} (hn : 2 ≤ n) (x : Genotype n k) :
    (1 - 1 / (n : ℝ)) ^ n ≤ viableBirth x x := by
  rw [← cloneBirth_self hn x]
  unfold cloneBirth viableBirth
  apply mean_mono
  intro child
  unfold acceptedClone cloneWeight
  split_ifs <;> norm_num

lemma mutation_clone_decline {n k : ℕ} (hn : 2 ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) :
    mean p (fun x ↦ cloneBirth B x x) -
      (p B).toReal * mean p (fun x ↦ viableBirth x x) ≤ (1 / (n : ℝ)) ^ 2 := by
  have hclone := Lax343628Proofs.MutationDrift.mutation_clone_upper hn B p
  have hviable := mean_mono p (mutation_viability_lower hn)
  rw [mean_const] at hviable
  have hscale := mul_le_mul_of_nonneg_left hviable (ENNReal.toReal_nonneg (a := p B))
  nlinarith

lemma mixed_clone_decline {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hlarge : 4 * k ≤ n)
    (B : Genotype n k) (p : PMF (Genotype n k)) (p0 p_c : ℝ) (hp0 : 0 < p0)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (hpmin : p0 ≤ (p B).toReal)
    (hpmax : (p B).toReal ≤ 1 / (8 * Real.sqrt k))
    (hiso : cloud B (fun x ↦ (p x).toReal) / (p B).toReal ≤ 1 / 25)
    (herror : approximationError n k ≤ Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 16)
    (hreturn : (1 / (n : ℝ)) ^ 2 ≤ p_c * Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 8) :
    p_c * (pairMean p (cloneBirth B) - (p B).toReal * pairMean p viableBirth) +
      (1 - p_c) * (mean p (fun x ↦ cloneBirth B x x) -
        (p B).toReal * mean p (fun x ↦ viableBirth x x)) ≤
          -(p_c * Real.exp (-1) * p0 * (1 / (2 * Real.sqrt k)) / 8) := by
  have hcross := mul_le_mul_of_nonneg_left
    (crossed_clone_decline hn hk hlarge B p p0 hp0 hpmin hpmax hiso herror) hp_c.1
  have hmut := mul_le_mul_of_nonneg_left (mutation_clone_decline hn B p) (sub_nonneg.mpr hp_c.2)
  have hreturn' := mul_le_mul_of_nonneg_right (show 1 - p_c ≤ 1 by linarith [hp_c.1])
    (sq_nonneg (1 / (n : ℝ)))
  nlinarith

lemma empirical_offspring_viability {n k : ℕ} {μ : ℕ+} (p_c : ℝ)
    (hp : 0 ≤ p_c ∧ p_c ≤ 1) (P : Fin (μ : ℕ) → Genotype n k) :
    mean (Lax343628Proofs.Sampling.offspring p_c (fun u ↦ toString (P u)))
      (fun z ↦ if onPlateau k z then 1 else 0) =
      p_c * pairMean (empirical P) viableBirth +
        (1 - p_c) * mean (empirical P) (fun x ↦ viableBirth x x) := by
  rw [offspring_mean p_c hp]
  change p_c * mean (PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ)))
      (fun uv ↦ viableBirth (P uv.1) (P uv.2)) +
    (1 - p_c) * mean (PMF.uniformOfFintype (Fin (μ : ℕ)))
      (fun u ↦ viableBirth (P u) (P u)) = _
  rw [empirical_pairMean]
  have h := mean_map (PMF.uniformOfFintype (Fin (μ : ℕ))) P (fun x ↦ viableBirth x x)
  rw [← h]
  rfl

end
end Lax343628Proofs.CloneBirthDrift
