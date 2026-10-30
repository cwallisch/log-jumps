import Lax343628Proofs.ClassFields

namespace Lax343628Proofs.EmpiricalStability

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassIncrements Lax343628Proofs.TaggedDynamics
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.EmpiricalKernels
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+} {i : Fin n} {b : Fin 2}

lemma average_step_abs (P : Population n μ) (E : Event n μ) (f : BitString n → ℝ)
    (M : ℝ) (_hM : 0 ≤ M) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) :
    |average (next k P E) f - average P f| ≤ M / (μ : ℕ) := by
  rw [average_change, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (μ : ℕ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (change_abs f M hf P E) (Nat.cast_nonneg (μ : ℕ))

lemma kernel_step_abs (P : Population n μ) (E : Event n μ) (h : ColumnClass n k i b → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M) (x : ColumnClass n k i b) :
    |ReproductiveValues.action (mixedKernel (empirical (next k P E))) h x -
      ReproductiveValues.action (mixedKernel (empirical P)) h x| ≤ M / (μ : ℕ) := by
  rw [mixed_action, mixed_action, empirical, empirical, mean_map, mean_map]
  exact average_step_abs P E (fun u ↦ action u h x) M hM
    (fun u ↦ ⟨ColumnKernels.action_nonneg u h (fun z ↦ (hh z).1) x,
      ColumnKernels.action_le u h M hM (fun z ↦ (hh z).2) x⟩)

lemma action_sub {α : Type*} [Fintype α] (A : ReproductiveValues.Kernel α) (f g : α → ℝ) (x : α) :
    ReproductiveValues.action A (fun y ↦ f y - g y) x =
      ReproductiveValues.action A f x - ReproductiveValues.action A g x := by
  simp only [ReproductiveValues.action, mul_sub, Finset.sum_sub_distrib]

lemma two_kernel_difference {α : Type*} [Fintype α] (A B : ReproductiveValues.Kernel α)
    (h : α → ℝ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M) (x : α) :
    |ReproductiveValues.action A h x - ReproductiveValues.action B h x| ≤ M := by
  have ha := ReproductiveValues.action_nonneg A h (fun z ↦ (hh z).1) x
  have hb := ReproductiveValues.action_nonneg B h (fun z ↦ (hh z).1) x
  have ha' := ReproductiveValues.action_le A h M hM (fun z ↦ (hh z).2) x
  have hb' := ReproductiveValues.action_le B h M hM (fun z ↦ (hh z).2) x
  rw [abs_le]
  constructor <;> linarith

end
end Lax343628Proofs.EmpiricalStability
