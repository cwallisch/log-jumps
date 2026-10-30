import Lax343628Proofs.PathProjection
import Lax343628Proofs.FiniteEvents

namespace Lax343628Proofs.RuntimeInvariant

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift Lax343628Proofs.Trajectories
open Lax343628Proofs.FiniteEvents
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

lemma intersection (p : PMF α) (I A : Set α) (hp : ∀ x ∈ p.support, x ∈ I) :
    p.toOuterMeasure (I ∩ A) = p.toOuterMeasure A := by
  apply le_antisymm (p.toOuterMeasure.mono Set.inter_subset_right)
  apply event_mono_on_support
  intro x hx hA
  exact ⟨hp x hx, hA⟩

lemma stopped_law (K : α → PMF α) (p : PMF α) (I : Set α)
    (hp : ∀ x ∈ p.support, x ∈ I) (hK : ∀ x ∈ I, ∀ y ∈ (K x).support, y ∈ I) (t : ℕ) :
    law (stopped K I) p t = law K p t := by
  have hh := congrArg (fun p : PMF (Fin (t + 1) → α) ↦ p.map (fun h ↦ h (Fin.last t)))
    (PathProjection.stop_invariant K p I hp hK t)
  simpa only [pathLaw_last] using hh

lemma bound (K : α → PMF α) (p : PMF α) (I A : Set α)
    (hp : ∀ x ∈ p.support, x ∈ I) (hK : ∀ x ∈ I, ∀ y ∈ (K x).support, y ∈ I)
    (habs : ∀ x ∉ A, (K x).toOuterMeasure A = 0)
    (L : ℕ) (hL : 0 < L) (q : ℝ≥0∞)
    (hblock : ∀ x ∈ I ∩ A, (law K (PMF.pure x) L).toOuterMeasure A ≤ q) :
    ∑' t, (law K p t).toOuterMeasure A ≤ (L : ℝ≥0∞) * (1 - q)⁻¹ := by
  have hstop : ∀ x ∉ I ∩ A, (stopped K I x).toOuterMeasure (I ∩ A) = 0 := by
    intro x hx
    by_cases hi : x ∈ I
    · have ha : x ∉ A := fun ha ↦ hx ⟨hi, ha⟩
      rw [stopped, if_pos hi]
      apply le_antisymm _ zero_le
      exact ((K x).toOuterMeasure.mono Set.inter_subset_right).trans_eq (habs x ha)
    · simp only [stopped, if_neg hi, PMF.toOuterMeasure_pure_apply, if_neg hx]
  have hblock' : ∀ x ∈ I ∩ A, (law (stopped K I) (PMF.pure x) L).toOuterMeasure (I ∩ A) ≤ q := by
    intro x hx
    have hinit : ∀ y ∈ (PMF.pure x).support, y ∈ I := by
      intro y hy
      have heq := (PMF.mem_support_pure_iff _ _).mp hy
      exact heq ▸ hx.1
    rw [stopped_law K (PMF.pure x) I hinit hK L]
    exact ((law K (PMF.pure x) L).toOuterMeasure.mono Set.inter_subset_right).trans (hblock x hx)
  have hh := runtime_le_of_block (stopped K I) p (I ∩ A) hstop L hL q hblock'
  have heq (t : ℕ) : (law (stopped K I) p t).toOuterMeasure (I ∩ A) = (law K p t).toOuterMeasure A := by
    rw [stopped_law K p I hp hK t]
    exact intersection _ I A (PathProjection.law_invariant K p I hp hK t)
  simpa only [heq] using hh

lemma escape (K : α → PMF α) (p : PMF α) (I A : Set α)
    (hp : ∀ x ∈ p.support, x ∈ I) (hK : ∀ x ∈ I, ∀ y ∈ (K x).support, y ∈ I)
    (habs : ∀ x ∉ A, (K x).toOuterMeasure A = 0) (W : ℝ) (hW : 1 ≤ W)
    (hstep : ∀ x ∈ I ∩ A, (K x).toOuterMeasure A ≤ 1 - ENNReal.ofReal (1 / W)) :
    (∑' t, (law K p t).toOuterMeasure A) ≤ ENNReal.ofReal W := by
  have hWp : 0 < W := by linarith
  have hpW : ENNReal.ofReal (1 / W) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one hWp).mpr hW)
  have hh := bound K p I A hp hK habs 1 (by norm_num) (1 - ENNReal.ofReal (1 / W)) (by
    intro x hx
    simpa only [law_succ, law_zero, PMF.pure_bind] using hstep x hx)
  have heq : (1 : ℝ≥0∞) * (1 - (1 - ENNReal.ofReal (1 / W)))⁻¹ = ENNReal.ofReal W := by
    rw [one_mul, ENNReal.sub_sub_cancel (by simp) hpW, one_div, ENNReal.ofReal_inv_of_pos hWp, inv_inv]
  simpa only [Nat.cast_one, heq] using hh

end
end Lax343628Proofs.RuntimeInvariant
