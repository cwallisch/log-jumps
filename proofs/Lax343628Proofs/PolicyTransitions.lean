import Lax343628Proofs.PolicyClock

namespace Lax343628Proofs.PolicyTransitions

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PolicyClock
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

def key (q : Config n) := (q.stage, q.unprocessed, q.epoch)

lemma positive_age (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu)
    (ha : active (tick astar theta omega M Rw Rs q S))
    (hage : 0 < (tick astar theta omega M Rw Rs q S).age) :
    key (tick astar theta omega M Rw Rs q S) = key q ∧
      (tick astar theta omega M Rw Rs q S).age = q.age + 1 := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at ha hage ⊢
  all_goals try split_ifs at ha hage ⊢
  all_goals try simp_all only [active, stop, setup_age, reduceCtorEq, exists_false, false_or]
  all_goals try omega
  all_goals simp only [key, hq, and_self]

lemma fresh_service (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu) (i : Fin n)
    (hserve : (tick astar theta omega M Rw Rs q S).stage = Stage.serving i)
    (hage : (tick astar theta omega M Rw Rs q S).age = 0) : M ≤ CoreCounts.missingCount i S.1 := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at hserve hage
  all_goals try split_ifs at hserve hage
  all_goals try simp_all only [stop, reduceCtorEq]
  all_goals first | omega | exact (setup_serving _ _ _ _ _ i hserve).2.2

lemma setup_not_failure (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) :
    (setup astar M P U e).stage ≠ Stage.failure := by
  dsimp only [setup]
  split_ifs <;> intro hh <;> cases hh

lemma failure_cases (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu)
    (hprev : q.stage ≠ Stage.failure) (hfail : (tick astar theta omega M Rw Rs q S).stage = Stage.failure) :
    ¬ColumnBlock.cap omega S.1 ∨
      (∃ i, i ∉ q.unprocessed ∧ theta ≤ ClassChannels.fraction i 0 S.1) ∨
      (q.stage = Stage.waiting ∧ Rw ≤ q.age + 1 ∧ ¬(ready q.unprocessed M S.1).Nonempty ∧
        ColumnBlock.cap omega S.1 ∧ PolicyInvariant.flat theta S.1 q.unprocessed) ∨
      (∃ i, q.stage = Stage.serving i ∧ Rs ≤ q.age + 1 ∧ astar < ClassChannels.fraction i 0 S.1 ∧
        ColumnBlock.cap omega S.1 ∧ PolicyInvariant.flat theta S.1 q.unprocessed) := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at hfail
  all_goals try split_ifs at hfail
  all_goals try simp only [stop, reduceCtorEq] at hfail hprev
  all_goals first
    | exact False.elim (hprev hfail)
    | exact False.elim (hprev hq)
    | exact False.elim (setup_not_failure _ _ _ _ _ hfail)
    | exact Or.inl (by assumption)
    | exact Or.inr (Or.inl (by assumption))
    | (right; right; left
       exact ⟨rfl, by assumption, by assumption, by assumption, PolicyInvariant.safe_flat _ _ _ (by assumption)⟩)
    | (right; right; right
       exact ⟨_, rfl, by assumption, lt_of_not_ge (by assumption), by assumption, PolicyInvariant.safe_flat _ _ _ (by assumption)⟩)

end
end Lax343628Proofs.PolicyTransitions
