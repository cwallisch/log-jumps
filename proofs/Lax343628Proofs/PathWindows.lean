import Lax343628Proofs.PathBarriers

namespace Lax343628Proofs.PathWindows

open Lax343628Proofs.Trajectories Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

def window (H R s : ℕ) (hs : s + R ≤ H) (h : Fin (H + 1) → α) : Fin (R + 1) → α :=
  segment s R (before H (s + R) hs h)

lemma window_apply (H R s : ℕ) (hs : s + R ≤ H) (h : Fin (H + 1) → α) (j : Fin (R + 1)) :
    window H R s hs h j = h ⟨s + j.val, by have := j.isLt; omega⟩ := rfl

lemma window_law (K : α → PMF α) (p : PMF α) (H R s : ℕ) (hs : s + R ≤ H) :
    (pathLaw K p H).map (window H R s hs) =
      (law K p s).bind (fun x ↦ pathLaw K (PMF.pure x) R) := by
  change (pathLaw K p H).map (segment s R ∘ before H (s + R) hs) = _
  rw [← PMF.map_comp, pathLaw_before, pathLaw_segment]

lemma dependent_bound (K : α → PMF α) (p : PMF α) (R : ℕ) (S : Set α)
    (E : α → Set (Fin (R + 1) → α)) (q : ℝ≥0∞)
    (hE : ∀ x ∈ S, (pathLaw K (PMF.pure x) R).toOuterMeasure (E x) ≤ q) :
    (p.bind (fun x ↦ pathLaw K (PMF.pure x) R)).toOuterMeasure
      {h | h 0 ∈ S ∧ h ∈ E (h 0)} ≤ q := by
  apply event_bind_bound
  intro x
  by_cases hx : x ∈ S
  · apply le_trans _ (hE x hx)
    apply event_mono_on_support
    intro h hh hbad
    have hs := path_pure_start K x h hh
    exact hs ▸ hbad.2
  · rw [event_zero_of_support (pathLaw K (PMF.pure x) R)
      {h | h 0 ∈ S ∧ h ∈ E (h 0)} (by
        intro h hh hbad
        have hs := path_pure_start K x h hh
        exact hx (hs ▸ hbad.1))]
    exact zero_le

lemma window_dependent_bound (K : α → PMF α) (p : PMF α) (H R s : ℕ) (hs : s + R ≤ H)
    (S : Set α) (E : α → Set (Fin (R + 1) → α)) (q : ℝ≥0∞)
    (hE : ∀ x ∈ S, (pathLaw K (PMF.pure x) R).toOuterMeasure (E x) ≤ q) :
    (pathLaw K p H).toOuterMeasure {h | (window H R s hs h) 0 ∈ S ∧
      window H R s hs h ∈ E ((window H R s hs h) 0)} ≤ q := by
  have hh := dependent_bound K (law K p s) R S E q hE
  rw [← window_law K p H R s hs, PMF.toOuterMeasure_map_apply] at hh
  exact hh

end
end Lax343628Proofs.PathWindows
