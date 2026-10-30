import Lax343628Proofs.FiniteCoupling
import Lax343628Proofs.BirthGeometry
import Lax343628Proofs.CurveBounds

namespace Lax343628Proofs.QuarterCone

lemma comparison {B b a W rho : ℝ} (hB : 0 ≤ B) (_hb : 0 ≤ b) (ha : 0 ≤ a)
    (hrho : 2 ≤ rho) (hmass_lower : (3 / 4 : ℝ) * B ≤ B / 4 + b)
    (hmass_upper : B / 4 + b ≤ (9 / 8 : ℝ) * B)
    (hupper : W ≤ rho * b * a) (hlower : b * a ≤ rho * W) :
    B / 4 * a + W ≤ rho * (B * a) ∧
      B * a ≤ rho * (B / 4 * a + W) := by
  have hBa : 0 ≤ B * a := mul_nonneg hB ha
  have hscale := mul_nonneg (by linarith : 0 ≤ rho - 2) hBa
  have hmassU := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hmass_upper ha) (show 0 ≤ rho by linarith)
  have hmassL := mul_le_mul_of_nonneg_right hmass_lower ha
  constructor <;> nlinarith


noncomputable section

open Lax343628Proofs.BirthGeometry Lax343628Proofs.CurveBounds
open scoped Classical

lemma asymmetric_masses {α : Type*} [Fintype α] [DecidableEq α] {n j : ℕ}
    (C : Finset (Fin n)) (label : α ⊕ Fin 2 ↪ Fin n) (e : Fin n) (he : e ∉ C)
    (hv : Fintype.card α = 2 * j ∨ Fintype.card α = 2 * j + 1 ∨ Fintype.card α + 1 = 2 * j) :
    (3 / 4 : ℝ) * mass (C.card + j + 1) (insert e C) (Function.Embedding.inl.trans label) ≤
        mass (C.card + j + 1) C label ∧
      mass (C.card + j + 1) C label ≤
        (9 / 8 : ℝ) * mass (C.card + j + 1) (insert e C) (Function.Embedding.inl.trans label) := by
  have h := profile_adjacent hv
  unfold mass
  rw [Fintype.card_sum, Fintype.card_fin, Finset.card_insert_of_notMem he,
    show C.card + j + 1 - (C.card + 1) = j by omega,
    show C.card + j + 1 - C.card = j + 1 by omega]
  constructor
  · have hs := mul_le_mul_of_nonneg_left h.1 (Real.exp_pos (-1)).le
    unfold profile at hs
    convert hs using 1 <;> first | rfl | ring
  · have hs := mul_le_mul_of_nonneg_left h.2 (Real.exp_pos (-1)).le
    unfold profile at hs
    convert hs using 1 <;> first | rfl | ring

end
end Lax343628Proofs.QuarterCone
