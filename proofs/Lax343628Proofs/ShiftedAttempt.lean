import Lax343628Proofs.AttemptBound
import Lax343628Proofs.SpeciesTagged
import Lax343628Proofs.SamplingBridge

namespace Lax343628Proofs.ShiftedAttempt

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PlateauDynamics Lax343628Proofs.Trajectories Lax343628Proofs.FiniteEvents
open Lax343628Proofs.FiniteChain Lax343628Proofs.AttemptLengths Lax343628Proofs.EntropyLedger
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+}

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hr : 1 ≤ r)
    (hrS : r + 1 ≤ (S : ℕ)) (hD : (3 : ℝ) ^ (r + 1) ≤ (S : ℕ))
    (pc delta : ℝ) (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n)
    (T : State n mu) (hT : plateauPopulation (r + 1) T.1) (hchild : T.2.2.1 ≠ optimum n)
    (t0 : ℕ) (qcap : ℝ≥0∞)
    (hcap : (pathLaw (driver (r + 1) pc) (PMF.pure T) (t0 + (decision S n mu delta + terminal S))).toOuterMeasure
      {h | ∃ t, t0 ≤ t.val ∧ ¬ColumnBlock.cap (1 / 125) (h t).1} ≤ qcap) :
    (law (step (jump (r + 1)) pc) (PMF.pure T.1) (t0 + (decision S n mu delta + terminal S))).toOuterMeasure Dynamics.missing ≤
      qcap + (qcap + ENNReal.ofReal ((n : ℝ) * (((decision S n mu delta + terminal S : ℕ) : ℝ) + 1) * delta) +
        ENNReal.ofReal (1 / 16) + ENNReal.ofReal ((n : ℝ) *
          ((((decision S n mu delta + terminal S : ℕ) : ℝ) + 1) * (((service S mu : ℝ) + 1) * delta)))) +
        ENNReal.ofReal (1 / 64) := by
  let L := decision S n mu delta + terminal S
  let K := driver (r + 1) pc (n := n) (mu := mu)
  let p := law K (PMF.pure T) t0
  have hc := PhaseConditions.of_size S hS n (r + 1) mu delta (by omega) hrS hD hd hmu hn
  have hkn : r + 1 ≤ n := by have := hc.dimension; omega
  have hinit : ∀ U ∈ (PMF.pure T).support, plateauPopulation (r + 1) U.1 := by
    intro U hU
    have heq := (PMF.mem_support_pure_iff _ _).mp hU
    exact heq ▸ hT
  have hnext : ∀ U : State n mu, plateauPopulation (r + 1) U.1 → ∀ V ∈ (K U).support, plateauPopulation (r + 1) V.1 := by
    intro U hU V hV
    obtain ⟨E, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hV
    exact KilledTagged.next_plateau U.1 hU E
  have hpplat := PathProjection.law_invariant K (PMF.pure T) {U | plateauPopulation (r + 1) U.1} hinit hnext t0
  have hp : ∀ U ∈ p.support, ∀ u, (Sampling.zeros (U.1 u)).card = r + 1 := by
    intro U hU u
    rw [Sampling.card_zeros]
    have hh := hpplat U hU u
    change ones (U.1 u) = n - (r + 1) at hh
    omega
  have hmap : (pathLaw K (PMF.pure T) (t0 + L)).map (segment t0 L) = pathLaw K p L := by
    rw [pathLaw_segment, PathProjection.mixture]
  have hcap' : (pathLaw K p L).toOuterMeasure {h | ∃ t, ¬ColumnBlock.cap (1 / 125) (h t).1} ≤ qcap := by
    rw [← hmap, PMF.toOuterMeasure_map_apply]
    apply le_trans _ hcap
    apply (pathLaw K (PMF.pure T) (t0 + L)).toOuterMeasure.mono
    intro h hh
    obtain ⟨t, ht⟩ := hh
    refine ⟨⟨t0 + t.val, by have := t.isLt; omega⟩, by simp, ht⟩
  have hattempt := AttemptBound.bound S hS hr hrS hD pc delta hpc hd hmu hn p hp qcap hcap'
  have hbridge := SamplingBridge.missing_le_noOptimum (by omega : 0 < r + 1) hkn pc T hT hchild (t0 + L)
  apply hbridge.trans
  apply le_trans _ hattempt
  rw [← hmap, PMF.toOuterMeasure_map_apply]
  apply (pathLaw K (PMF.pure T) (t0 + L)).toOuterMeasure.mono
  intro h hh j
  let t : Fin (t0 + L) := ⟨t0 + j.val, by have := j.isLt; omega⟩
  exact hh t

end
end Lax343628Proofs.ShiftedAttempt
