import Lax343628Proofs.PathProjection
import Lax343628Proofs.SpeciesCap
import Lax343628Proofs.CoreSpecies
import Lax343628Proofs.KilledTagged

namespace Lax343628Proofs.SpeciesTagged

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.Sampling Lax343628Proofs.PlateauDynamics Lax343628Proofs.Genotypes
open Lax343628Proofs.FiniteDrift Lax343628Proofs.Trajectories Lax343628Proofs.FiniteComparison
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k H : ℕ} {mu : ℕ+}

lemma invariant (k : ℕ) (pc : ℝ) (p : PMF (State n mu))
    (hp : ∀ T ∈ p.support, plateauPopulation k T.1)
    (h : Fin (H + 1) → State n mu) (hh : h ∈ (pathLaw (driver k pc) p H).support) :
    ∀ j, plateauPopulation k (h j).1 := by
  apply path_invariant (driver k pc) p {T | plateauPopulation k T.1} hp _ h hh
  intro T hT U hU
  obtain ⟨E, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hU
  exact KilledTagged.next_plateau T.1 hT E

lemma path_map (hkn : k ≤ n) (pc : ℝ) (p : PMF (State n mu))
    (hp : ∀ T ∈ p.support, plateauPopulation k T.1) (H : ℕ) :
    (pathLaw (driver k pc) p H).map (fun h ↦ Prod.fst ∘ h) =
      pathLaw (auxiliaryStep k pc) (p.map Prod.fst) H := by
  let A : Set (Population n mu) := {P | plateauPopulation k P}
  have hsource : ∀ T ∈ p.support, T ∈ Prod.fst ⁻¹' A := hp
  have htarget : ∀ P ∈ (p.map Prod.fst).support, P ∈ A := by
    intro P hP
    obtain ⟨T, hT, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hP
    exact hp T hT
  have hi : ∀ T ∈ Prod.fst ⁻¹' A, ∀ U ∈ (driver k pc T).support, U ∈ Prod.fst ⁻¹' A := by
    intro T hT U hU
    obtain ⟨E, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hU
    exact KilledTagged.next_plateau T.1 hT E
  have hj : ∀ P ∈ A, ∀ Q ∈ (auxiliaryStep k pc P).support, Q ∈ A := by
    intro P hP Q hQ
    exact auxiliary_invariant pc P hP Q hQ
  have hh := PathProjection.map (stopped (driver k pc) (Prod.fst ⁻¹' A))
    (stopped (auxiliaryStep k pc) A) Prod.fst
    (KernelProjection.stopped_map (driver k pc) (auxiliaryStep k pc) Prod.fst A
      (fun T hT ↦ driver_population hkn pc T hT)) p H
  rw [PathProjection.stop_invariant _ _ _ hsource hi,
    PathProjection.stop_invariant _ _ _ htarget hj] at hh
  exact hh

lemma count_frequency (P : Population n mu) (z : BitString n) :
    PopulationRatio.count z P = (mu : ℕ) * EmpiricalKernels.frequency P z := by
  rw [CoreSpecies.frequency_mean, mean_uniform, Fintype.card_fin]
  unfold PopulationRatio.count Deletion.total PopulationRatio.indicator
  have hm : ((mu : ℕ) : ℝ) ≠ 0 := by exact_mod_cast mu.ne_zero
  field_simp

lemma cap_failure (hkn : k ≤ n) (P : Population n mu) (hP : plateauPopulation k P)
    (hbad : ¬ColumnBlock.cap (1 / 125) P) :
    ∃ B : Genotype n k, (124 / 125 : ℝ) * (mu : ℕ) < PopulationRatio.count (toString B) P := by
  obtain ⟨z, hz⟩ : ∃ z, (124 / 125 : ℝ) < EmpiricalKernels.frequency P z := by
    simpa only [ColumnBlock.cap, not_forall, not_le, show (1 : ℝ) - 1 / 125 = 124 / 125 by norm_num] using hbad
  have hnonzero : EmpiricalKernels.empirical P z ≠ 0 := by
    intro he
    simp only [EmpiricalKernels.frequency, he, ENNReal.toReal_zero] at hz
    linarith
  obtain ⟨u, _, hu⟩ := (PMF.mem_support_map_iff _ _ _).mp hnonzero
  have hzero : (zeros z).card = k := by
    rw [← hu, card_zeros]
    have hh := hP u
    change ones (P u) = n - k at hh
    omega
  refine ⟨ofString z hzero, ?_⟩
  rw [toString_ofString, count_frequency]
  have hmp : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  nlinarith

lemma bound {p0 pc : ℝ} (hc : CloneProtection.Conditions n k pc p0)
    (he : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ SpeciesProtection.strictConstant * p0 ^ 2)
    (hm : 200 ≤ (mu : ℕ) * p0) (hp0 : p0 ≤ 1 / 8) (hpc : 0 ≤ pc ∧ pc ≤ 1)
    (T : State n mu) (hT : plateauPopulation k T.1) (t0 H : ℕ) (ht : t0 ≤ H) :
    (pathLaw (driver k pc) (PMF.pure T) H).toOuterMeasure
      {h | ∃ t : Fin (H + 1), t0 ≤ t.val ∧ ¬ColumnBlock.cap (1 / 125) (h t).1} ≤
      ENNReal.ofReal ((1 / 20 : ℝ) / (p0 * SpeciesEntry.entryDrift n k mu p0 * ((t0 : ℝ) + 1)) +
        (Fintype.card (Genotype n k) : ℝ) * ((H : ℝ) + 1) ^ 2 *
          (SpeciesReentry.countFailure k mu pc p0 + SpeciesReentry.ratioFailure mu pc p0)) := by
  have hkn : k ≤ n := by have := hc.entry.dimension_four_jump; omega
  have hinit : ∀ U ∈ (PMF.pure T).support, plateauPopulation k U.1 := by
    intro U hU
    have heq := (PMF.mem_support_pure_iff _ _).mp hU
    exact heq ▸ hT
  have hh := SpeciesCap.horizon_cap_bound hc he hm hp0 hpc T.1 hT t0 H ht
  have hmap := path_map hkn pc (PMF.pure T) hinit H
  simp only [PMF.pure_map] at hmap
  rw [← hmap, PMF.toOuterMeasure_map_apply] at hh
  apply le_trans _ hh
  apply FiniteEvents.event_mono_on_support
  intro h hs hbad
  obtain ⟨t, ht, hcap⟩ := hbad
  obtain ⟨B, hB⟩ := cap_failure hkn (h t).1 (invariant k pc (PMF.pure T) hinit h hs t) hcap
  exact ⟨t, ht, B, hB⟩

end
end Lax343628Proofs.SpeciesTagged
