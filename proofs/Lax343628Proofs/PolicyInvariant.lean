import Lax343628Proofs.PolicyPaths

namespace Lax343628Proofs.PolicyInvariant

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.ClassChannels Lax343628Proofs.ColumnBlock
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {mu : ℕ+}

def flat (theta : ℝ) (P : Population n mu) (U : Finset (Fin n)) : Prop :=
  ∀ i, i ∉ U → fraction i 0 P < theta

def Valid (astar theta omega : ℝ) (M Rw Rs : ℕ) (P : Population n mu) (q : Config n) : Prop :=
  match q.stage with
  | Stage.waiting => q.unprocessed.Nonempty ∧ ¬(ready q.unprocessed M P).Nonempty ∧ q.age < Rw ∧ cap omega P ∧ flat theta P q.unprocessed
  | Stage.serving i => i ∈ q.unprocessed ∧ astar < fraction i 0 P ∧ q.age < Rs ∧ cap omega P ∧ flat theta P q.unprocessed
  | Stage.terminal => q.unprocessed = ∅ ∧ cap omega P ∧ flat theta P q.unprocessed
  | _ => True

lemma refresh_flat (astar theta : ℝ) (hath : astar < theta) (P : Population n mu) (U : Finset (Fin n))
    (hflat : flat theta P U) : flat theta P (ColumnMarks.refresh U astar P) := by
  intro i hi
  by_cases hiU : i ∈ U
  · have hsmall : fraction i 0 P ≤ astar := le_of_not_gt (fun hh ↦ hi (Finset.mem_filter.mpr ⟨hiU, hh⟩))
    exact hsmall.trans_lt hath
  · exact hflat i hiU

lemma safe_flat (theta : ℝ) (P : Population n mu) (U : Finset (Fin n))
    (hsafe : ¬∃ i, i ∉ U ∧ theta ≤ fraction i 0 P) : flat theta P U := by
  intro i hi
  exact lt_of_not_ge (fun hh ↦ hsafe ⟨i, hi, hh⟩)

lemma setup_valid (astar theta omega : ℝ) (M Rw Rs : ℕ) (hath : astar < theta) (hRw : 0 < Rw) (hRs : 0 < Rs)
    (P : Population n mu) (U : Finset (Fin n)) (e : ℕ) (hcap : cap omega P) (hflat : flat theta P U) :
    Valid astar theta omega M Rw Rs P (setup astar M P U e) := by
  have hf := refresh_flat astar theta hath P U hflat
  dsimp only [setup]
  split_ifs with hV hR
  · dsimp only [Valid]
    have hi := Finset.mem_filter.mp (Finset.min'_mem (ready (ColumnMarks.refresh U astar P) M P) hR)
    exact ⟨hi.1, (Finset.mem_filter.mp hi.1).2, hRs, hcap, hf⟩
  · exact ⟨hV, hR, hRw, hcap, hf⟩
  · exact ⟨Finset.not_nonempty_iff_eq_empty.mp hV, hcap, hf⟩

lemma stop_valid (astar theta omega : ℝ) (M Rw Rs : ℕ) (P : Population n mu) (q : Config n) :
    Valid astar theta omega M Rw Rs P (stop q Stage.success) ∧
      Valid astar theta omega M Rw Rs P (stop q Stage.failure) := ⟨trivial, trivial⟩

lemma tick_valid (astar theta omega : ℝ) (M Rw Rs : ℕ) (hath : astar < theta) (hRw : 0 < Rw) (hRs : 0 < Rs)
    (P : Population n mu) (q : Config n) (S : State n mu) (hv : Valid astar theta omega M Rw Rs P q) :
    Valid astar theta omega M Rw Rs S.1 (tick astar theta omega M Rw Rs q S) := by
  cases hq : q.stage <;>
    simp only [tick, hq, reduceCtorEq, or_false, or_true, if_true, if_false]
  all_goals try split_ifs
  all_goals first
    | exact (stop_valid astar theta omega M Rw Rs S.1 q).1
    | exact (stop_valid astar theta omega M Rw Rs S.1 q).2
    | (apply setup_valid astar theta omega M Rw Rs hath hRw hRs
       · assumption
       · apply safe_flat; assumption)
    | (simp only [Valid, hq] at hv ⊢
       exact ⟨hv.1, by assumption, by omega, by assumption, safe_flat _ _ _ (by assumption)⟩)
    | (simp only [Valid, hq] at hv ⊢
       exact ⟨hv.1, lt_of_not_ge (by assumption), by omega, by assumption, safe_flat _ _ _ (by assumption)⟩)
    | (simp only [Valid, hq] at hv ⊢
       exact ⟨hv.1, by assumption, safe_flat _ _ _ (by assumption)⟩)
    | (simp only [Valid, hq])

lemma path_valid (astar theta omega : ℝ) (M Rw Rs : ℕ) (hath : astar < theta) (hRw : 0 < Rw) (hRs : 0 < Rs)
    {H : ℕ} (h : Fin (H + 1) → State n mu) (hcap : cap omega (h 0).1) :
    ∀ t, Valid astar theta omega M Rw Rs (h t).1 (PolicyPaths.configuration astar theta omega M Rw Rs h t) := by
  intro t
  refine Fin.induction ?_ (fun j hj ↦ ?_) t
  · apply setup_valid astar theta omega M Rw Rs hath hRw hRs _ Finset.univ 0 hcap
    intro i hi
    exact False.elim (hi (Finset.mem_univ i))
  · rw [PolicyPaths.at_succ]
    exact tick_valid astar theta omega M Rw Rs hath hRw hRs _ _ _ hj

end
end Lax343628Proofs.PolicyInvariant
