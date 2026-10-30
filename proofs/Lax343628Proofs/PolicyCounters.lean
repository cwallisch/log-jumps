import Lax343628Proofs.AttemptPolicy
import Lax343628Proofs.FoldStarts

namespace Lax343628Proofs.PolicyCounters

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

lemma epoch_monotone (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu) :
    q.epoch ≤ (tick astar theta omega M Rw Rs q S).epoch := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false]
  all_goals try split_ifs
  all_goals try simp only [setup_epoch, stop]
  all_goals omega

lemma wait_enter (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu)
    (hstart : isWaitStart (tick astar theta omega M Rw Rs q S)) :
    q.epoch < (tick astar theta omega M Rw Rs q S).epoch := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at hstart ⊢
  all_goals try split_ifs at hstart ⊢
  all_goals simp_all only [setup_epoch, stop, isWaitStart, reduceCtorEq, false_and, and_false]
  all_goals omega

lemma removed (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu) (i : Fin n)
    (hi : i ∈ q.unprocessed) (hnot : i ∉ (tick astar theta omega M Rw Rs q S).unprocessed) :
    ClassChannels.fraction i 0 S.1 ≤ astar := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at hnot
  all_goals try split_ifs at hnot
  all_goals try simp only [setup_unprocessed, stop] at hnot
  all_goals first
    | exact False.elim (hnot hi)
    | exact le_of_not_gt (fun hh ↦ hnot (Finset.mem_filter.mpr ⟨hi, hh⟩))

end
end Lax343628Proofs.PolicyCounters
