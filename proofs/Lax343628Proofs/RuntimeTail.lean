import Lax343628Proofs.Trajectories

namespace Lax343628Proofs.RuntimeTail

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift Lax343628Proofs.Trajectories
open scoped Classical BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

lemma stopped_absorbs (K : α → PMF α) (A : Set α) (x : α) (hx : x ∉ A) :
    (stopped K A x).toOuterMeasure A = 0 := by simp only [stopped, PMF.toOuterMeasure_pure_apply, if_neg hx]

lemma antitone_tail (f : ℕ → ℝ≥0∞) (hf : Antitone f) (W : ℝ) (_hW : 0 ≤ W)
    (hsum : (∑' t, f t) ≤ ENNReal.ofReal W) (t : ℕ) :
    f t ≤ ENNReal.ofReal (W / ((t : ℝ) + 1)) := by
  have hsum' : f t * ((t + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal W := by
    calc
      _ = ∑ _s ∈ Finset.range (t + 1), f t := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ s ∈ Finset.range (t + 1), f s := Finset.sum_le_sum (fun s hs ↦ hf (by have := Finset.mem_range.mp hs; omega))
      _ ≤ ∑' s, f s := ENNReal.sum_le_tsum _
      _ ≤ _ := hsum
  have heq : ENNReal.ofReal (W / ((t : ℝ) + 1)) = ENNReal.ofReal W / ((t + 1 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < (t : ℝ) + 1)]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add (Nat.cast_nonneg t) (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast]
  rw [heq]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))).mpr hsum'

lemma stay_le (K : α → PMF α) (A : Set α) (p : PMF α) (W : ℝ) (hW : 0 ≤ W)
    (hsum : (∑' t, (law (stopped K A) p t).toOuterMeasure A) ≤ ENNReal.ofReal W) (t : ℕ) :
    (pathLaw K p t).toOuterMeasure {h | ∀ j, h j ∈ A} ≤ ENNReal.ofReal (W / ((t : ℝ) + 1)) := by
  rw [stay_probability]
  exact antitone_tail _ (event_law_antitone (stopped K A) p A (stopped_absorbs K A)) W hW hsum t

end
end Lax343628Proofs.RuntimeTail
