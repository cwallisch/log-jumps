import Lax343628Proofs.PolicyInvariant

namespace Lax343628Proofs.PolicyClock

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PolicyInvariant Lax343628Proofs.PolicyPaths
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

def active (q : Config n) : Prop := q.stage = Stage.waiting ∨ ∃ i, q.stage = Stage.serving i

lemma age_bound (astar theta omega : ℝ) (M Rw Rs : ℕ) (P : Population n mu) (q : Config n)
    (hv : Valid astar theta omega M Rw Rs P q) (ha : active q) : q.age < Rw + Rs := by
  rcases ha with hw | ⟨i, hs⟩
  · simp only [Valid, hw] at hv
    omega
  · simp only [Valid, hs] at hv
    omega

lemma active_prev (astar theta omega : ℝ) (M Rw Rs : ℕ) (q : Config n) (S : State n mu)
    (ha : active (tick astar theta omega M Rw Rs q S)) : active q := by
  cases hq : q.stage <;> try { simp [active, hq] }
  all_goals simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at ha
  all_goals try split_ifs at ha
  all_goals simp_all only [active, stop, reduceCtorEq, exists_false, false_or]

lemma tick_time (astar theta omega : ℝ) (M Rw Rs : ℕ) (P : Population n mu) (q : Config n) (S : State n mu)
    (hv : Valid astar theta omega M Rw Rs P q) (ha : active (tick astar theta omega M Rw Rs q S)) :
    q.epoch * (Rw + Rs) + q.age + 1 ≤
      (tick astar theta omega M Rw Rs q S).epoch * (Rw + Rs) + (tick astar theta omega M Rw Rs q S).age := by
  have hprev := active_prev astar theta omega M Rw Rs q S ha
  have hage := age_bound astar theta omega M Rw Rs P q hv hprev
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false] at ha ⊢
  all_goals try split_ifs at ha ⊢
  all_goals try simp_all only [active, stop, reduceCtorEq, exists_false, false_or]
  all_goals first
    | omega
    | (rw [setup_epoch, setup_age, Nat.add_mul, one_mul]; omega)

lemma time_bound (astar theta omega : ℝ) (M Rw Rs : ℕ) (hath : astar < theta) (hRw : 0 < Rw) (hRs : 0 < Rs)
    {H : ℕ} (h : Fin (H + 1) → State n mu) (hcap : ColumnBlock.cap omega (h 0).1) :
    ∀ t, active (configuration astar theta omega M Rw Rs h t) →
      t.val ≤ (configuration astar theta omega M Rw Rs h t).epoch * (Rw + Rs) +
        (configuration astar theta omega M Rw Rs h t).age := by
  intro t
  refine Fin.induction ?_ (fun j hj ↦ ?_) t
  · intro _; exact Nat.zero_le _
  · intro ha
    have hnew : active (tick astar theta omega M Rw Rs (configuration astar theta omega M Rw Rs h j.castSucc) (h j.succ)) := ha
    have hprev := active_prev astar theta omega M Rw Rs _ _ hnew
    have htime := tick_time astar theta omega M Rw Rs (h j.castSucc).1 _ _
      (path_valid astar theta omega M Rw Rs hath hRw hRs h hcap j.castSucc) hnew
    have hi := hj hprev
    rw [← PolicyPaths.at_succ] at htime
    have hval : j.succ.val = j.castSucc.val + 1 := rfl
    omega

end
end Lax343628Proofs.PolicyClock
