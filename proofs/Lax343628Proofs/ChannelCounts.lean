import Lax343628Proofs.PathCounts
import Lax343628Proofs.DrivenNoise
import Lax343628Proofs.ClassChannels

namespace Lax343628Proofs.ChannelCounts

open Lax343628.Algorithm Lax343628Proofs.ClassChannels Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison Lax343628Proofs.FiniteChain
open Lax343628Proofs.Trajectories Lax343628Proofs.PathNoise Lax343628Proofs.DrivenNoise
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+}

def tick (i : Fin n) (b : Fin 2) (active : Population n mu → Prop) [DecidablePred active]
    (H t : ℕ) (S T : State n mu) : ℝ :=
  if t < H ∧ active S.1 then (if channel i b S.1 T.2 then 1 else 0) else 0

lemma tick_bounds (i : Fin n) (b : Fin 2) (active : Population n mu → Prop) [DecidablePred active]
    (H t : ℕ) (S T : State n mu) : 0 ≤ tick i b active H t S T ∧ tick i b active H t S T ≤ 1 := by
  unfold tick
  split_ifs <;> norm_num

lemma mean_tick (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (b : Fin 2)
    (active : Population n mu → Prop) [DecidablePred active] (fmax : ℝ) (hfmax : 0 ≤ fmax)
    (hf : ∀ P, active P → fraction i b P ≤ fmax) (H t : ℕ) (S : State n mu) :
    mean (stopped (driver k pc) {S | active S.1} S) (tick i b active H t S) ≤ 3 * fmax := by
  by_cases hg : t < H ∧ active S.1
  · rw [stopped]
    simp only [Set.mem_ofPred_eq, if_pos hg.2, driver, mean_map]
    change mean (eventLaw pc S.1) (fun E ↦ if t < H ∧ active S.1 then (if channel i b S.1 E then 1 else 0) else 0) ≤ _
    simp only [if_pos hg]
    exact (channel_bound pc hpc i b S.1).trans (by nlinarith [hf S.1 hg.2])
  · change mean _ (fun T : State n mu ↦ if t < H ∧ active S.1 then (if channel i b S.1 T.2 then 1 else 0) else 0) ≤ _
    simp only [if_neg hg, mean_const]
    positivity

lemma tail (pc : ℝ) (hpc : 0 ≤ pc ∧ pc ≤ 1) (i : Fin n) (b : Fin 2)
    (active : Population n mu → Prop) [DecidablePred active] (fmax : ℝ) (hfmax : 0 ≤ fmax)
    (hf : ∀ P, active P → fraction i b P ≤ fmax) (H : ℕ) (L : ℝ) (p : PMF (State n mu)) :
    (pathLaw (stopped (driver k pc) {S | active S.1}) p H).toOuterMeasure
      {h | 6 * H * fmax + 2 * L ≤ accumulate (tick i b active H) H h} ≤
        ENNReal.ofReal (Real.exp (-L)) := by
  have hh := PathCounts.tail (stopped (driver k pc) {S | active S.1}) p (tick i b active H) (3 * fmax) L
    (by positivity) (tick_bounds i b active H) (mean_tick pc hpc i b active fmax hfmax hf H) H
  convert hh using 1; ring_nf

end
end Lax343628Proofs.ChannelCounts
