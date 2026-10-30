import Lax343628Proofs.ArrivalTime
import Lax343628Proofs.StoppedSurvival

namespace Lax343628Proofs.ArrivalRuntime

open Lax343628.Algorithm Lax343628Proofs.Sampling Lax343628Proofs.Dynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.ArrivalFitness
open Lax343628Proofs.EntropyLedger Lax343628Proofs.PlateauDynamics
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

lemma active_absorbs (hk : 1 ≤ k) (hkn : k ≤ n) (pc : ℝ) (P : Population n mu) (hP : P ∉ active k)
    (Q : Population n mu) (hQ : Q ∈ (step (jump k) pc P).support) : Q ∉ active k := by
  intro hh
  by_cases hm : P ∈ missing
  · have hp : plateauPopulation k P := by
      by_contra hn
      exact hP ⟨hm, hn⟩
    exact hh.2 (plateau_step_invariant (by omega) hkn pc P hp Q hQ hh.1)
  · exact step_retains_optimum (by omega) pc P hm Q hQ hh.1

lemma bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (hks : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc delta : ℝ)
    (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) (p : PMF (Population n mu)) :
    (∑' t, (law (stopped (step (jump k) pc) (active k)) p t).toOuterMeasure (active k)) ≤
      ENNReal.ofReal ((4096 / pc) * (mu : ℕ) * (n : ℝ)) := by
  have hs : (0 : ℝ) < (S : ℕ) := by exact_mod_cast S.pos
  have hp : 0 < pc := (div_pos (by norm_num) hs).trans_le hpc.1
  have hh := ArrivalRanks.runtime_sum (by omega : 2 ≤ n) hk hkn pc ⟨hp, hpc.2⟩ p
  exact hh.trans (ENNReal.ofReal_le_ofReal (ArrivalTime.sum_costs S hS n k mu pc delta hk hks hD hpc hd hmu hn))

lemma tail (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (hks : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (pc delta : ℝ)
    (hpc : 1 / (S : ℕ) ≤ pc ∧ pc ≤ 1) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) (p : PMF (Population n mu)) (T : ℕ) :
    (law (step (jump k) pc) p T).toOuterMeasure (active k) ≤
      ENNReal.ofReal (((4096 / pc) * (mu : ℕ) * (n : ℝ)) / ((T : ℝ) + 1)) := by
  have hs : (0 : ℝ) < (S : ℕ) := by exact_mod_cast S.pos
  have hp : 0 < pc := (div_pos (by norm_num) hs).trans_le hpc.1
  exact StoppedSurvival.bound _ p (active k) (active_absorbs hk (by omega) pc) _ (by positivity)
    (bound S hS hk hkn hks hD pc delta hpc hd hmu hn p) T

end
end Lax343628Proofs.ArrivalRuntime
