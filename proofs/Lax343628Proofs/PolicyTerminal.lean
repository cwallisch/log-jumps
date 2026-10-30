import Lax343628Proofs.PolicyTimeout

namespace Lax343628Proofs.PolicyTerminal

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PolicyPaths Lax343628Proofs.PolicyInvariant
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n H : ℕ} {mu : ℕ+}

lemma failure_monotone (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu) :
    Monotone (fun t ↦ (configuration astar theta omega M Rw Rs h t).stage = Stage.failure) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j hj
  rw [at_succ]
  simp only [tick, if_pos (Or.inr hj)]
  exact hj

lemma setup_not_success (astar : ℝ) (M : ℕ) (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) :
    (setup astar M P U e).stage ≠ Stage.success := by
  dsimp only [setup]
  split_ifs <;> intro hh <;> cases hh

lemma tick_not_success (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (T : State n mu)
    (hprev : q.stage ≠ Stage.success) (hchild : T.2.2.1 ≠ optimum n) :
    (tick astar theta omega M Rw Rs q T).stage ≠ Stage.success := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false, if_neg hchild]
  all_goals try split_ifs
  all_goals first
    | exact setup_not_success _ _ _ _ _
    | exact hprev
    | exact False.elim (hprev hq)
    | (intro hh; cases hh)

lemma no_success (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu)
    (hchild : ∀ j : Fin H, (h j.succ).2.2.1 ≠ optimum n) :
    ∀ t, (configuration astar theta omega M Rw Rs h t).stage ≠ Stage.success := by
  intro t
  refine Fin.induction ?_ (fun j ih ↦ ?_) t
  · exact setup_not_success _ _ _ _ _
  · exact tick_not_success astar theta omega M Rw Rs _ _ ih (hchild j)

lemma flat_after (astar theta omega : ℝ) (M Rw Rs K : ℕ) (hath : astar < theta)
    (hRw : 0 < Rw) (hRs : 0 < Rs) (h : Fin (H + 1) → State n mu)
    (hcap : ColumnBlock.cap omega (h 0).1)
    (hK : (ColumnMarks.refresh Finset.univ astar (h 0).1).card ≤ K)
    (hchild : ∀ j : Fin H, (h j.succ).2.2.1 ≠ optimum n)
    (hfail : (configuration astar theta omega M Rw Rs h (Fin.last H)).stage ≠ Stage.failure)
    (t : Fin (H + 1)) (ht : (2 * K + 2) * (Rw + Rs) ≤ t.val) :
    ∀ i, ClassChannels.fraction i 0 (h t).1 < theta := by
  have hns := no_success astar theta omega M Rw Rs h hchild t
  have hnf : (configuration astar theta omega M Rw Rs h t).stage ≠ Stage.failure :=
    fun hh ↦ hfail (failure_monotone astar theta omega M Rw Rs h (Fin.le_last t) hh)
  have hv := path_valid astar theta omega M Rw Rs hath hRw hRs h hcap t
  have hna : ¬PolicyClock.active (configuration astar theta omega M Rw Rs h t) := by
    intro ha
    have htime := PolicyClock.time_bound astar theta omega M Rw Rs hath hRw hRs h hcap t ha
    have he := epoch_bound astar theta omega M Rw Rs h K hK t
    have hage := PolicyClock.age_bound astar theta omega M Rw Rs _ _ hv ha
    have hm := Nat.mul_le_mul_right (Rw + Rs) he
    nlinarith
  cases hstage : (configuration astar theta omega M Rw Rs h t).stage
  · exact False.elim (hna (Or.inl hstage))
  · exact False.elim (hna (Or.inr ⟨_, hstage⟩))
  · simp only [Valid, hstage] at hv
    intro i
    exact hv.2.2 i (by rw [hv.1]; simp)
  · exact False.elim (hns hstage)
  · exact False.elim (hnf hstage)

end
end Lax343628Proofs.PolicyTerminal
