import Lax343628Proofs.RuntimeTail
import Lax343628Proofs.FiniteEvents

namespace Lax343628Proofs.StoppedSurvival

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

lemma final_iff (K : α → PMF α) (p : PMF α) (A : Set α)
    (hK : ∀ x ∉ A, ∀ y ∈ (K x).support, y ∉ A) {T : ℕ}
    (h : Fin (T + 1) → α) (hh : h ∈ (pathLaw K p T).support) :
    (∀ j, h j ∈ A) ↔ h (Fin.last T) ∈ A := by
  constructor
  · exact fun hs ↦ hs _
  · intro hlast
    have hm : Monotone (fun j ↦ h j ∉ A) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro j hj
      exact hK _ hj _ (path_step_support K p h hh j)
    intro j
    by_contra hj
    exact hm (Fin.le_last j) hj hlast

lemma probability (K : α → PMF α) (p : PMF α) (A : Set α)
    (hK : ∀ x ∉ A, ∀ y ∈ (K x).support, y ∉ A) (T : ℕ) :
    (law K p T).toOuterMeasure A = (law (stopped K A) p T).toOuterMeasure A := by
  rw [← pathLaw_last K p T, PMF.toOuterMeasure_map_apply, ← stay_probability K A p T]
  apply le_antisymm
  · apply FiniteEvents.event_mono_on_support
    intro h hh hlast
    exact (final_iff K p A hK h hh).mpr hlast
  · apply (pathLaw K p T).toOuterMeasure.mono
    intro h hh
    exact hh (Fin.last T)

lemma bound (K : α → PMF α) (p : PMF α) (A : Set α)
    (hK : ∀ x ∉ A, ∀ y ∈ (K x).support, y ∉ A) (W : ℝ) (hW : 0 ≤ W)
    (hsum : (∑' t, (law (stopped K A) p t).toOuterMeasure A) ≤ ENNReal.ofReal W) (T : ℕ) :
    (law K p T).toOuterMeasure A ≤ ENNReal.ofReal (W / ((T : ℝ) + 1)) := by
  rw [probability K p A hK T]
  exact RuntimeTail.antitone_tail _ (event_law_antitone (stopped K A) p A (RuntimeTail.stopped_absorbs K A)) W hW hsum T

end
end Lax343628Proofs.StoppedSurvival
