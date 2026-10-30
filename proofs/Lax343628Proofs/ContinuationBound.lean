import Lax343628Proofs.PathContinuation

namespace Lax343628Proofs.ContinuationBound

open Lax343628Proofs.Trajectories Lax343628Proofs.PathContinuation Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*}

lemma bind_restrict (p : PMF α) (K : α → PMF β) (C : Set α) (E : Set β) (q : ℝ≥0∞)
    (hC : ∀ x ∈ C, (K x).toOuterMeasure E ≤ q)
    (hnot : ∀ x ∉ C, (K x).toOuterMeasure E = 0) :
    (p.bind K).toOuterMeasure E ≤ p.toOuterMeasure C * q := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ C
  · simpa only [Set.indicator_of_mem hx] using mul_le_mul' (le_refl (p x)) (hC x hx)
  · simp only [hnot x hx, Set.indicator_of_notMem hx, mul_zero, zero_mul, le_refl]

lemma prefix_bound (K : α → PMF α) (p : PMF α) (s R : ℕ) (C : Set (Fin (s + 1) → α))
    (E : (Fin (s + 1) → α) → Set (Fin (R + 1) → α)) (q : ℝ≥0∞)
    (hE : ∀ h ∈ C, (pathLaw K (PMF.pure (h (Fin.last s))) R).toOuterMeasure (E h) ≤ q) :
    (pathLaw K p (s + R)).toOuterMeasure
      {g | initialSegment s R g ∈ C ∧ segment s R g ∈ E (initialSegment s R g)} ≤
      (pathLaw K p s).toOuterMeasure C * q := by
  rw [PathContinuation.pathLaw_add]
  apply bind_restrict
  · intro h hh
    have hm := hE h hh
    rw [← segment_law K s h R, PMF.toOuterMeasure_map_apply] at hm
    apply le_trans _ hm
    apply event_mono_on_support
    intro g hg hbad
    have hp := prefix_support K s h R g hg
    change segment s R g ∈ E h
    exact hp ▸ hbad.2
  · intro h hh
    apply event_zero_of_support
    intro g hg hbad
    have hp := prefix_support K s h R g hg
    exact hh (hp ▸ hbad.1)

end
end Lax343628Proofs.ContinuationBound
