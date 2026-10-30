import Lax343628Proofs.KilledTagged
import Lax343628Proofs.AttemptBound

namespace Lax343628Proofs.SamplingBridge

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise
open Lax343628Proofs.Sampling Lax343628Proofs.PlateauDynamics Lax343628Proofs.Dynamics
open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def present : Set (Option (Population n mu)) := {x | x.isSome}

lemma physical_preimage : KilledSampling.collapse ⁻¹' (present (n := n) (mu := mu)) = missing := by
  ext P
  simp only [Set.mem_preimage, present, Set.mem_ofPred_eq, KilledSampling.collapse]
  split_ifs <;> simp_all

lemma tagged_preimage : KilledTagged.collapse k ⁻¹' (present (n := n) (mu := mu)) = KilledTagged.alive k := by
  ext T
  simp only [Set.mem_preimage, present, Set.mem_ofPred_eq, KilledTagged.collapse]
  split_ifs <;> simp_all

lemma exact_survival (hk : 0 < k) (hkn : k ≤ n) (pc : ℝ) (T : State n mu)
    (hT : T ∈ KilledTagged.alive k) (H : ℕ) :
    (law (step (jump k) pc) (PMF.pure T.1) H).toOuterMeasure missing =
      (pathLaw (driver k pc) (PMF.pure T) H).toOuterMeasure {h | ∀ j, h j ∈ KilledTagged.alive k} := by
  have hmiss := KilledSampling.plateau_missing hk hkn T.1 hT.1
  have hp := KernelProjection.law_map (step (jump k) pc) (KilledSampling.kernel k pc)
    KilledSampling.collapse (KilledSampling.physical_map hk pc) (PMF.pure T.1) H
  have ht := KernelProjection.law_map (stopped (driver k pc) (KilledTagged.alive k)) (KilledSampling.kernel k pc)
    (KilledTagged.collapse k) (KilledTagged.stopped_map hk hkn pc) (PMF.pure T) H
  simp only [PMF.pure_map, KilledSampling.collapse, if_pos hmiss] at hp
  simp only [PMF.pure_map, KilledTagged.collapse, if_pos hT] at ht
  have heq := congrArg (fun p : PMF (Option (Population n mu)) ↦ p.toOuterMeasure present) (hp.trans ht.symm)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply, physical_preimage, tagged_preimage] at heq
  rw [stay_probability]
  exact heq

lemma missing_le_noOptimum (hk : 0 < k) (hkn : k ≤ n) (pc : ℝ) (T : State n mu)
    (hP : plateauPopulation k T.1) (hchild : T.2.2.1 ≠ optimum n) (H : ℕ) :
    (law (step (jump k) pc) (PMF.pure T.1) H).toOuterMeasure missing ≤
      (pathLaw (driver k pc) (PMF.pure T) H).toOuterMeasure (AttemptBound.noOptimum H) := by
  rw [exact_survival hk hkn pc T ⟨hP, hchild⟩ H]
  apply (pathLaw (driver k pc) (PMF.pure T) H).toOuterMeasure.mono
  intro h hh j
  exact (hh j.succ).2

end
end Lax343628Proofs.SamplingBridge
