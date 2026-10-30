import Lax343628Proofs.ClassFields

namespace Lax343628Proofs.ColumnFieldBounds

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+} {i : Fin n} {b : Fin 2}

lemma reference_bounds (P : Population n μ) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) (ref : ColumnClass n k i b) (D : ℝ) (hD : 1 ≤ D)
    (hone : ∀ z, 1 ≤ h z) (hratio : ∀ x y, h y ≤ D * h x) :
    (∀ z, 0 ≤ h z ∧ h z ≤ D * h ref) ∧
      fraction i b P ≤ average P (liftClass h) ∧
      (D * h ref) * fraction i b P ≤ D ^ 2 * average P (liftClass h) := by
  have hDp : 0 < D := by linarith
  have hupper (z : ColumnClass n k i b) : h z ≤ D * h ref := hratio ref z
  have hmin (z : ColumnClass n k i b) : h ref / D ≤ h z := by
    apply (div_le_iff₀ hDp).mpr
    have ht := hratio z ref
    nlinarith
  have hlo := (average_bounds P hP h 1 (D * h ref) (fun z ↦ ⟨hone z, hupper z⟩)).1
  have hlo' := (average_bounds P hP h (h ref / D) (D * h ref) (fun z ↦ ⟨hmin z, hupper z⟩)).1
  have hlow : fraction i b P * h ref ≤ average P (liftClass h) * D := by
    apply (div_le_iff₀ hDp).mp
    convert hlo' using 1 <;> first | rfl | ring
  refine ⟨fun z ↦ ⟨by linarith [hone z], hupper z⟩, by simpa only [mul_one] using hlo, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hlow hDp.le]

lemma lift_bounds (h : ColumnClass n k i b → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M) :
    ∀ z, 0 ≤ liftClass h z ∧ liftClass h z ≤ M := by
  intro z
  unfold liftClass
  split_ifs
  · exact hh _
  · exact ⟨by rfl, hM⟩

lemma lift_bit (h : ColumnClass n k i b → ℝ) (z : BitString n) (hz : z i ≠ b) : liftClass h z = 0 := by
  unfold liftClass
  rw [dif_neg (by tauto)]

end
end Lax343628Proofs.ColumnFieldBounds
