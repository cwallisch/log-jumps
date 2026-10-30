import Lax343628Proofs.CoreCounts
import Lax343628Proofs.SeedWaitingBound

namespace Lax343628Proofs.CoreWaitingBound

open Lax343628.Algorithm Lax343628Proofs.SeedGeometry Lax343628Proofs.CoreCounts
open Lax343628Proofs.FiniteChain Lax343628Proofs.FiniteDrift
open scoped Classical ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {mu : ℕ+} {i : Fin n}

lemma bound (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n) (pc : ℝ) (hpc : 0 < pc ∧ pc ≤ 1)
    (C : Finset (Fin n)) (hi : i ∈ C) (hC : C.card ≤ r)
    (M : ℕ) (theta : ℝ) (htheta : 0 ≤ theta)
    (hsmall : (r + 1 : ℝ) * M / (mu : ℕ) ≤ 1 / 4)
    (hcost : 2 * (r + 1 : ℝ) * theta + 2 * ((r + 1 : ℝ) * M / (mu : ℕ)) +
      256 * (r + 1 : ℝ) ^ 2 / n + 1 / n ≤ Real.exp (-1) / (64 * (r + 1 : ℝ) ^ 2))
    (hmutation : (r + 1 : ℝ) / n ≤ pc * Real.exp (-1) / (128 * (r + 1 : ℝ) ^ 2))
    (p : PMF (Population n mu)) :
    (∑' t, (law (stopped (PlateauDynamics.auxiliaryStep (r + 1) pc)
      (waiting r C M theta)) p t).toOuterMeasure (waiting r C M theta)) ≤
      ENNReal.ofReal ((M : ℝ) / (pc * (1 / 4 : ℝ) ^ (r + 1) / (64 * n)) +
        (mu : ℕ) * M / (pc * Real.exp (-1) / (256 * (r + 1 : ℝ) ^ 2))) := by
  have hrho (P : Population n mu) (hP : P ∈ waiting r C M theta) :
      rho C P ≤ (r + 1 : ℝ) * M / (mu : ℕ) := by
    have hc : (C.card : ℝ) ≤ r + 1 := by exact_mod_cast (show C.card ≤ r + 1 by omega)
    have hh := (rho_le C P M hP.2.1).trans
      (mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ M / (mu : ℕ) by positivity))
    convert hh using 1 <;> first | rfl | ring
  apply SeedWaitingBound.bound hr hn pc hpc C hi hC M theta htheta (waiting r C M theta)
    (fun _ hP ↦ hP.1) (fun P hP ↦ (family_le C i P).trans_lt (hP.2.1 i hi))
    (fun _ hP j hj ↦ (hP.2.2 j hj).le) (fun P hP ↦ (hrho P hP).trans hsmall)
  · intro P hP
    linarith [hrho P hP]
  · exact hmutation

end
end Lax343628Proofs.CoreWaitingBound
