import Lax343628Proofs.RuntimeTail

namespace Lax343628Proofs.RuntimeEscape

open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift Lax343628Proofs.Trajectories
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type*}

lemma bound (K : α → PMF α) (A : Set α) (p : PMF α) (W : ℝ) (hW : 1 ≤ W)
    (hstep : ∀ x ∈ A, (K x).toOuterMeasure A ≤ 1 - ENNReal.ofReal (1 / W)) (T : ℕ) :
    (pathLaw K p T).toOuterMeasure {h | ∀ j, h j ∈ A} ≤ ENNReal.ofReal (W / ((T : ℝ) + 1)) := by
  have hWp : 0 < W := by linarith
  have hp : ENNReal.ofReal (1 / W) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one hWp).mpr hW)
  have hsum := runtime_le_of_block (stopped K A) p A (RuntimeTail.stopped_absorbs K A)
    1 (by norm_num) (1 - ENNReal.ofReal (1 / W)) (by
      intro x hx
      simpa only [law_succ, law_zero, PMF.pure_bind, stopped, if_pos hx] using hstep x hx)
  have heq : (1 : ℝ≥0∞) * (1 - (1 - ENNReal.ofReal (1 / W)))⁻¹ = ENNReal.ofReal W := by
    rw [one_mul, ENNReal.sub_sub_cancel (by simp) hp, one_div,
      ENNReal.ofReal_inv_of_pos hWp, inv_inv]
  simp only [Nat.cast_one] at hsum
  rw [heq] at hsum
  exact RuntimeTail.stay_le K A p W hWp.le hsum T

end
end Lax343628Proofs.RuntimeEscape
