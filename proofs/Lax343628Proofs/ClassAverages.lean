import Lax343628Proofs.ClassBirthEstimates
import Lax343628Proofs.PhysicalCone

namespace Lax343628Proofs.ClassAverages

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.ClassBirth
open Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.EmpiricalKernels
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+} {i : Fin n} {b : Fin 2}

def operatorAverage (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ if hb : P u i = b then
    ReproductiveValues.action (mixedKernel (empirical P)) h ⟨P u, hP u, hb⟩ else 0)

lemma ownCross_operator (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) : ownCross P i b (liftClass h) = operatorAverage P hP h := by
  rw [ownCross, ← empirical_pairMean, mean_uniform_pair
    (fun u v ↦ if P u i = b then classFactor i b (P v) * pairTest (liftClass h) (P u) (P v) else 0)]
  unfold operatorAverage
  congr 1
  funext u
  by_cases hb : P u i = b
  · rw [dif_pos hb]
    simp only [if_pos hb]
    rw [mixed_action, empirical, mean_map]
    congr 1
    funext v
    exact (action_eq_mean (P v) h (⟨P u, hP u, hb⟩ : ColumnClass n k i b)).symm
  · rw [dif_neg hb]
    simp only [if_neg hb, mean_const]

end
end Lax343628Proofs.ClassAverages
