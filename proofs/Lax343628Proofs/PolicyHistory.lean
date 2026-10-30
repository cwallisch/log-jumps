import Lax343628Proofs.PhaseTrace

namespace Lax343628Proofs.PolicyHistory

open Lax343628.Algorithm Lax343628Proofs.AttemptPolicy Lax343628Proofs.DrivenNoise
open Lax343628Proofs.PolicyPaths
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n H : ℕ} {mu : ℕ+}

lemma processed (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu) :
    ∀ t i, i ∉ (configuration astar theta omega M Rw Rs h t).unprocessed →
      ∃ b, b ≤ t ∧ ClassChannels.fraction i 0 (h b).1 ≤ astar := by
  intro t
  refine Fin.induction ?_ (fun j ih ↦ ?_) t
  · intro i hi
    refine ⟨0, le_rfl, ?_⟩
    change i ∉ (setup astar M (h 0).1 Finset.univ 0).unprocessed at hi
    rw [setup_unprocessed] at hi
    exact le_of_not_gt (fun hh ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hh⟩))
  · intro i hi
    by_cases hp : i ∈ (configuration astar theta omega M Rw Rs h j.castSucc).unprocessed
    · exact ⟨j.succ, le_rfl, PolicyCounters.removed astar theta omega M Rw Rs _ _ i hp hi⟩
    · obtain ⟨b, hb, hf⟩ := ih i hp
      exact ⟨b, hb.trans (by exact Fin.le_iff_val_le_val.mpr (by simp)), hf⟩

lemma fresh_service (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu)
    (t : Fin (H + 1)) (i : Fin n)
    (hs : (configuration astar theta omega M Rw Rs h t).stage = Stage.serving i)
    (ha : (configuration astar theta omega M Rw Rs h t).age = 0) :
    M ≤ CoreCounts.missingCount i (h t).1 := by
  refine Fin.cases ?_ (fun j ↦ ?_) t hs ha
  · intro hs _
    exact (setup_serving astar M (h 0).1 Finset.univ 0 i hs).2.2
  · intro hs ha
    exact PolicyTransitions.fresh_service astar theta omega M Rw Rs _ _ i hs ha

lemma key_stage (q v : Config n) (hk : PolicyTransitions.key q = PolicyTransitions.key v) :
    q.stage = v.stage := congrArg Prod.fst hk

lemma key_unprocessed (q v : Config n) (hk : PolicyTransitions.key q = PolicyTransitions.key v) :
    q.unprocessed = v.unprocessed := congrArg (fun x ↦ x.2.1) hk

lemma first_failure (astar theta omega : ℝ) (M Rw Rs : ℕ) (h : Fin (H + 1) → State n mu) :
    ∀ t, (configuration astar theta omega M Rw Rs h t).stage = Stage.failure →
      ∃ j : Fin H, j.succ ≤ t ∧
        (configuration astar theta omega M Rw Rs h j.castSucc).stage ≠ Stage.failure ∧
        (configuration astar theta omega M Rw Rs h j.succ).stage = Stage.failure := by
  intro t
  refine Fin.induction ?_ (fun j ih ↦ ?_) t
  · intro hh
    exact False.elim (PolicyTransitions.setup_not_failure _ _ _ _ _ hh)
  · intro hh
    by_cases hp : (configuration astar theta omega M Rw Rs h j.castSucc).stage = Stage.failure
    · obtain ⟨b, hb, hprev, hfail⟩ := ih hp
      exact ⟨b, hb.trans (Fin.le_iff_val_le_val.mpr (by simp)), hprev, hfail⟩
    · exact ⟨j, le_rfl, hp, hh⟩

end
end Lax343628Proofs.PolicyHistory
