import Lax343628Proofs.ClassBiasBounds
import Lax343628Proofs.ChannelNoise
import Lax343628Proofs.ReproductiveAdmissibility

namespace Lax343628Proofs.ClassFields

open Lax343628.Algorithm Lax343628Proofs.Sampling
open Lax343628Proofs.ColumnKernels Lax343628Proofs.ClassAverages
open Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.ClassChannels
open Lax343628Proofs.ClassMeanDynamics Lax343628Proofs.ClassIncrements
open Lax343628Proofs.TaggedDynamics Lax343628Proofs.FiniteDrift
open Lax343628Proofs.FiniteComparison Lax343628Proofs.ChannelNoise
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+} {i : Fin n} {b : Fin 2}

lemma average_lift_linear (P : Population n μ) (h g : ColumnClass n k i b → ℝ) (a : ℝ) :
    average P (liftClass (fun x ↦ h x + a * g x)) =
      average P (liftClass h) + a * average P (liftClass g) := by
  have heq : liftClass (fun x ↦ h x + a * g x) = fun z ↦ liftClass h z + a * liftClass g z := by
    funext z
    unfold liftClass
    split_ifs <;> ring
  unfold average
  rw [heq, mean_add, mean_mul]

lemma average_bounds (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) (L M : ℝ) (hh : ∀ z, L ≤ h z ∧ h z ≤ M) :
    fraction i b P * L ≤ average P (liftClass h) ∧ average P (liftClass h) ≤ fraction i b P * M := by
  have hpoint (u : Fin (μ : ℕ)) :
      L * (if P u i = b then 1 else 0) ≤ liftClass h (P u) ∧
        liftClass h (P u) ≤ M * (if P u i = b then 1 else 0) := by
    by_cases hb : P u i = b
    · have hz : (zeros (P u)).card = k ∧ P u i = b := ⟨hP u, hb⟩
      simpa only [liftClass, dif_pos hz, if_pos hb, mul_one] using hh ⟨P u, hz⟩
    · simp only [liftClass, dif_neg (by tauto : ¬((zeros (P u)).card = k ∧ P u i = b)),
        if_neg hb, mul_zero, le_refl, and_self]
  have hlo := mean_mono (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ (hpoint u).1)
  have hhi := mean_mono (PMF.uniformOfFintype (Fin (μ : ℕ))) (fun u ↦ (hpoint u).2)
  rw [mean_mul] at hlo hhi
  constructor
  · simpa only [average, fraction, mul_comm] using hlo
  · simpa only [average, fraction, mul_comm] using hhi

def fieldAction (P : Population n μ) (A : ReproductiveValues.Kernel (ColumnClass n k i b))
    (h : ColumnClass n k i b → ℝ) : ℝ := average P (liftClass (ReproductiveValues.action A h))

lemma actual_fieldAction (P : Population n μ) (hP : ∀ u, (zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) :
    fieldAction P (mixedKernel (EmpiricalKernels.empirical P)) h = operatorAverage P hP h := by
  unfold fieldAction average operatorAverage
  congr 1
  funext u
  by_cases hb : P u i = b
  · simp only [liftClass, dif_pos (And.intro (hP u) hb), dif_pos hb]
  · simp only [liftClass, dif_neg (by tauto : ¬((zeros (P u)).card = k ∧ P u i = b)), dif_neg hb]

lemma average_change (ψ : BitString n → ℝ) (P : Population n μ) (E : Event n μ) :
    average (next k P E) ψ - average P ψ = change k ψ P E / (μ : ℕ) := by
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  unfold change
  rw [← average_total (next k P E) ψ, ← average_total P ψ]
  field_simp

end
end Lax343628Proofs.ClassFields
