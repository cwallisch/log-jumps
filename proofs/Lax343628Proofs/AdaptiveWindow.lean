import Lax343628Proofs.ContinuationBound
import Lax343628Proofs.ExclusiveEvents

namespace Lax343628Proofs.AdaptiveWindow

open Lax343628Proofs.Trajectories Lax343628Proofs.PathWindows
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [Fintype α] {B R : ℕ}

def history (s : Fin (B + 1)) (h : Fin (B + R + 1) → α) : Fin (s.val + 1) → α :=
  before (B + R) s.val (by have := s.isLt; omega) h

def tail (s : Fin (B + 1)) (h : Fin (B + R + 1) → α) : Fin (R + 1) → α :=
  window (B + R) R s.val (by have := s.isLt; omega) h

def start (C : (s : Fin (B + 1)) → Set (Fin (s.val + 1) → α)) (s : Fin (B + 1)) :
    Set (Fin (B + R + 1) → α) := {h | history s h ∈ C s}

def failure (C : (s : Fin (B + 1)) → Set (Fin (s.val + 1) → α))
    (E : (s : Fin (B + 1)) → (Fin (s.val + 1) → α) → Set (Fin (R + 1) → α))
    (s : Fin (B + 1)) : Set (Fin (B + R + 1) → α) :=
  {h | history s h ∈ C s ∧ tail s h ∈ E s (history s h)}

omit [Fintype α] in
lemma each (K : α → PMF α) (p : PMF α)
    (C : (s : Fin (B + 1)) → Set (Fin (s.val + 1) → α))
    (E : (s : Fin (B + 1)) → (Fin (s.val + 1) → α) → Set (Fin (R + 1) → α))
    (q : ℝ≥0∞)
    (hE : ∀ s, ∀ h ∈ C s, (pathLaw K (PMF.pure (h (Fin.last s.val))) R).toOuterMeasure (E s h) ≤ q)
    (s : Fin (B + 1)) :
    (pathLaw K p (B + R)).toOuterMeasure (failure C E s) ≤ (pathLaw K p s.val).toOuterMeasure (C s) * q := by
  have hh := ContinuationBound.prefix_bound K p s.val R (C s) (E s) q (hE s)
  rw [← pathLaw_before K p (B + R) (s.val + R) (by have := s.isLt; omega),
    PMF.toOuterMeasure_map_apply] at hh
  exact hh

lemma start_mass (K : α → PMF α) (p : PMF α)
    (C : (s : Fin (B + 1)) → Set (Fin (s.val + 1) → α))
    (hunique : ∀ h : Fin (B + R + 1) → α, ∀ s t,
      history s h ∈ C s → history t h ∈ C t → s = t) :
    (∑ s : Fin (B + 1), (pathLaw K p s.val).toOuterMeasure (C s)) ≤ 1 := by
  have hh := ExclusiveEvents.sum_le_one (pathLaw K p (B + R)) (start (R := R) C) hunique
  have heq (s : Fin (B + 1)) :
      (pathLaw K p (B + R)).toOuterMeasure (start (R := R) C s) = (pathLaw K p s.val).toOuterMeasure (C s) := by
    rw [← pathLaw_before K p (B + R) s.val (by have := s.isLt; omega), PMF.toOuterMeasure_map_apply]
    rfl
  simpa only [heq] using hh

lemma bound (K : α → PMF α) (p : PMF α)
    (C : (s : Fin (B + 1)) → Set (Fin (s.val + 1) → α))
    (E : (s : Fin (B + 1)) → (Fin (s.val + 1) → α) → Set (Fin (R + 1) → α))
    (q : ℝ≥0∞)
    (hE : ∀ s, ∀ h ∈ C s, (pathLaw K (PMF.pure (h (Fin.last s.val))) R).toOuterMeasure (E s h) ≤ q)
    (hunique : ∀ h : Fin (B + R + 1) → α, ∀ s t,
      history s h ∈ C s → history t h ∈ C t → s = t) :
    (pathLaw K p (B + R)).toOuterMeasure {h | ∃ s, h ∈ failure C E s} ≤ q := by
  have heq : {h | ∃ s, h ∈ failure C E s} = ⋃ s, failure C E s := by ext h; simp
  rw [heq]
  calc
    _ ≤ ∑ s, (pathLaw K p (B + R)).toOuterMeasure (failure C E s) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ s, (pathLaw K p s.val).toOuterMeasure (C s) * q :=
      Finset.sum_le_sum (fun s _ ↦ each K p C E q hE s)
    _ = (∑ s, (pathLaw K p s.val).toOuterMeasure (C s)) * q := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * q := mul_le_mul' (start_mass K p C hunique) le_rfl
    _ = q := one_mul _

end
end Lax343628Proofs.AdaptiveWindow
