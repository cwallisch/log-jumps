import Lax343628Proofs.SpeciesState
import Lax343628Proofs.RisingDrift
import Lax343628Proofs.Trajectories
import Lax343628Proofs.FiniteEvents

namespace Lax343628Proofs.SpeciesEntry

open Lax343628.Algorithm Lax343628Proofs.Genotypes Lax343628Proofs.SpeciesState
open Lax343628Proofs.PopulationRatio Lax343628Proofs.PlateauDynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.RisingDrift
open Lax343628Proofs.EntryBounds
open Lax343628Proofs.EmpiricalKernels Lax343628Proofs.FiniteEvents Lax343628Proofs.Trajectories
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def badSet {n k : ℕ} {μ : ℕ+} (B : Genotype n k) (p0 : ℝ) : Set (Population n μ) :=
  {P | plateauPopulation k P ∧ (μ : ℕ) * p0 < count (toString B) P ∧
    ratio (weightFunction B) (toString B) P < 1 / 25}

def entryDrift (n k : ℕ) (μ : ℕ+) (p0 : ℝ) : ℝ :=
  p0 * (k : ℝ) / (64 * n * ((μ : ℕ) + 1))

lemma entryDrift_pos {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (hcond : Conditions n k p0) :
    0 < entryDrift n k μ p0 := by
  have hp := hcond.threshold_pos
  have hk : (0 : ℝ) < k := by exact_mod_cast hcond.jump_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have h := hcond.dimension_two; omega)
  unfold entryDrift
  positivity

lemma bad_drift {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (hcond : Conditions n k p0)
    (hμ : 200 ≤ (μ : ℕ) * p0) (B : Genotype n k) (p_c : ℝ)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (P : Population n μ) (hP : P ∈ badSet B p0) :
    entryDrift n k μ p0 ≤ mean (auxiliaryStep k p_c P)
      (fun Q ↦ ratio (weightFunction B) (toString B) Q - ratio (weightFunction B) (toString B) P) := by
  exact plateau_entry_ratio_drift hcond P hP.1 B p_c hp_c
    (by linarith [hP.2.1]) hP.2.1.le hP.2.2.le

lemma bad_next_ratio {n k : ℕ} {μ : ℕ+} {p0 : ℝ}
    (hμ : 200 ≤ (μ : ℕ) * p0) (B : Genotype n k) (p_c : ℝ)
    (P : Population n μ) (hP : P ∈ badSet B p0) (Q : Population n μ)
    (hQ : Q ∈ (auxiliaryStep k p_c P).support) :
    ratio (weightFunction B) (toString B) Q ≤ 1 / 20 := by
  have hN : 200 < count (toString B) P := lt_of_le_of_lt hμ hP.2.1
  have hstep := auxiliary_ratio_abs (weightFunction B) (toString B)
    (weightFunction_anchor B) (weightFunction_bounds B) p_c P (by linarith) Q hQ
  have hfrac : (5 / 4 + ratio (weightFunction B) (toString B) P) /
      (count (toString B) P - 1) ≤ (1 / 100 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < count (toString B) P - 1)).mpr
    linarith [hP.2.2]
  have hbound := (abs_le.mp (hstep.trans hfrac)).2
  linarith [hP.2.2]

lemma stopped_bad_probability {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (hcond : Conditions n k p0)
    (hμ : 200 ≤ (μ : ℕ) * p0) (B : Genotype n k) (p_c : ℝ)
    (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) (initial : PMF (Population n μ)) (t : ℕ) :
    (law (stopped (auxiliaryStep k p_c) (badSet B p0)) initial t).toOuterMeasure (badSet B p0) ≤
      ENNReal.ofReal ((1 / 20 : ℝ) / (entryDrift n k μ p0 * ((t : ℝ) + 1))) := by
  apply rising_event_bound (auxiliaryStep k p_c) (badSet B p0)
    (ratio (weightFunction B) (toString B)) (1 / 20) (entryDrift n k μ p0)
    (by norm_num) (ratio_nonneg _ _ (fun x ↦ (weightFunction_bounds B x).1))
    (entryDrift_pos hcond)
  · intro P hP
    linarith [hP.2.2]
  · exact bad_next_ratio hμ B p_c
  · exact bad_drift hcond hμ B p_c hp_c

def initiallyBad {n k : ℕ} {μ : ℕ+} (P : Population n μ) (p0 : ℝ) : Finset (Genotype n k) :=
  Finset.univ.filter (fun B ↦ P ∈ badSet B p0)

lemma initiallyBad_card {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (hkn : k ≤ n) (hp0 : 0 < p0)
    (P : Population n μ) (hP : plateauPopulation k P) :
    ((initiallyBad (k := k) P p0).card : ℝ) ≤ 1 / p0 := by
  let G := genotypePopulation hkn P hP
  apply large_atoms_card (empirical G) _ p0 hp0
  intro B hB
  have hB' : P ∈ badSet B p0 := (Finset.mem_filter.mp hB).2
  have hcount := count_empirical G B
  rw [realize_genotypePopulation] at hcount
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  apply (mul_le_mul_iff_of_pos_left hμ).mp
  rw [← hcount]
  exact hB'.2.1.le

lemma initial_species_entry {n k : ℕ} {μ : ℕ+} {p0 : ℝ} (hcond : Conditions n k p0)
    (hμ : 200 ≤ (μ : ℕ) * p0) (p_c : ℝ) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1)
    (P : Population n μ) (hP : plateauPopulation k P) (t : ℕ) :
    (pathLaw (auxiliaryStep k p_c) (PMF.pure P) t).toOuterMeasure
      {h | ∃ B ∈ initiallyBad (k := k) P p0, ∀ i, h i ∈ badSet B p0} ≤
        ENNReal.ofReal ((1 / 20 : ℝ) / (p0 * entryDrift n k μ p0 * ((t : ℝ) + 1))) := by
  let bound : ℝ := (1 / 20 : ℝ) / (entryDrift n k μ p0 * ((t : ℝ) + 1))
  have hbound : 0 ≤ bound := by
    have hδ := entryDrift_pos (μ := μ) hcond
    dsimp [bound]
    positivity
  have hunion := finite_union_bound (pathLaw (auxiliaryStep k p_c) (PMF.pure P) t)
    (initiallyBad (k := k) P p0) (fun B ↦ {h | ∀ i, h i ∈ badSet B p0}) bound hbound
    (fun B _ ↦ by
      rw [stay_probability]
      exact stopped_bad_probability hcond hμ B p_c hp_c _ t)
  have hkn : k ≤ n := by have h := hcond.dimension_four_jump; omega
  have hcard := mul_le_mul_of_nonneg_right
    (initiallyBad_card hkn hcond.threshold_pos P hP) hbound
  apply hunion.trans
  apply (ENNReal.ofReal_le_ofReal hcard).trans_eq
  congr 1
  dsimp [bound]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end Lax343628Proofs.SpeciesEntry
