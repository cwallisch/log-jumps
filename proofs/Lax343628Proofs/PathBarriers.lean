import Lax343628Proofs.BoundedBarrier
import Lax343628Proofs.FiniteEvents

namespace Lax343628Proofs.PathBarriers

open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteChain
open Lax343628Proofs.Trajectories Lax343628Proofs.FiniteEvents Lax343628Proofs.BoundedBarrier
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

lemma conditional_path_bound (K : α → PMF α) (p : PMF α) (S : Set α) (t : ℕ)
    (E : Set (Fin (t + 1) → α)) (q : ℝ≥0∞)
    (hE : ∀ x ∈ S, (pathLaw K (PMF.pure x) t).toOuterMeasure E ≤ q) :
    (p.bind (fun x ↦ pathLaw K (PMF.pure x) t)).toOuterMeasure
      {h | h ∈ E ∧ h 0 ∈ S} ≤ q := by
  apply event_bind_bound
  intro x
  by_cases hx : x ∈ S
  · exact ((pathLaw K (PMF.pure x) t).toOuterMeasure.mono
      (fun _ h ↦ h.1)).trans (hE x hx)
  · have hzero := event_zero_of_support (pathLaw K (PMF.pure x) t)
      {h | h ∈ E ∧ h 0 ∈ S} (fun h hh ↦ by
        intro he
        have hs := he.2
        rw [path_pure_start K x h hh] at hs
        exact hx hs)
    rw [hzero]
    exact zero_le

end
end Lax343628Proofs.PathBarriers
