import Lax343628Proofs.KilledSampling
import Lax343628Proofs.Trajectories

namespace Lax343628Proofs.KilledTagged

open Lax343628.Algorithm Lax343628Proofs.DrivenNoise Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.Sampling Lax343628Proofs.PlateauDynamics Lax343628Proofs.KilledSampling
open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def alive (k : ℕ) : Set (State n mu) :=
  {T | plateauPopulation k T.1 ∧ T.2.2.1 ≠ optimum n}

def collapse (k : ℕ) (T : State n mu) : Option (Population n mu) :=
  if T ∈ alive k then some T.1 else none

lemma next_plateau (P : Population n mu) (hP : plateauPopulation k P) (E : Event n mu) :
    plateauPopulation k (next k P E) := by
  unfold next
  split_ifs with hz
  · exact replace_onPlateau P hP _ hz _
  · exact hP

lemma emitted (hkn : k ≤ n) (P : Population n mu) (hP : plateauPopulation k P)
    (uv : Fin (mu : ℕ) × Fin (mu : ℕ)) (z : BitString n) :
    (PMF.uniformOfFintype (Fin ((mu : ℕ) + 1))).map
      (fun d ↦ collapse k (next k P (uv, z, d), (uv, z, d))) =
      if z = optimum n then PMF.pure none else (auxiliaryInsert k P z).map some := by
  by_cases hz : z = optimum n
  · rw [if_pos hz]
    apply map_pure_on_support
    intro d _
    apply if_neg
    intro hh
    exact hh.2 hz
  · rw [if_neg hz, auxiliaryInsert_uniform hkn P hP z, PMF.map_comp]
    congr 1
    funext d
    exact if_pos ⟨next_plateau P hP (uv, z, d), hz⟩

lemma driver_map (hk : 0 < k) (hkn : k ≤ n) (pc : ℝ) (T : State n mu)
    (hT : plateauPopulation k T.1) :
    (driver k pc T).map (collapse k) = (step (jump k) pc T.1).map KilledSampling.collapse := by
  rw [driver, PMF.map_comp, physical_killed hk hkn pc T.1 hT, ← parentLaw_offspring]
  simp only [eventLaw, Bind.bind, Pure.pure, PMF.map_bind, PMF.pure_map, PMF.bind_bind]
  congr 1
  funext uv
  congr 1
  funext z
  exact emitted hkn T.1 hT uv z

lemma stopped_map (hk : 0 < k) (hkn : k ≤ n) (pc : ℝ) (T : State n mu) :
    (stopped (driver k pc) (alive k) T).map (collapse k) = kernel k pc (collapse k T) := by
  by_cases hT : T ∈ alive k
  · simp only [stopped, if_pos hT, collapse]
    exact driver_map hk hkn pc T hT.1
  · simp only [stopped, PMF.pure_map, collapse, if_neg hT, kernel]

end
end Lax343628Proofs.KilledTagged
