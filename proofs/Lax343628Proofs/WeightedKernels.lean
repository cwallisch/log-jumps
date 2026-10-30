import Lax343628Proofs.ClassFields
import Lax343628Proofs.SparseEnvironment

namespace Lax343628Proofs.WeightedKernels

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+} {i : Fin n} {b : Fin 2}

def partnerAverage (P : Population n mu) (h : ColumnClass n k i b → ℝ) (u : BitString n) : ℝ :=
  average P (liftClass (action u h))

lemma partner_bound (P : Population n mu) (h : ColumnClass n k i b → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hn : ∀ x, 0 ≤ h x) (hratio : ∀ x y, h y ≤ D * h x) (u : BitString n) :
    0 ≤ partnerAverage P h u ∧ partnerAverage P h u ≤ D * average P (liftClass h) := by
  have hact (x : ColumnClass n k i b) : 0 ≤ action u h x ∧ action u h x ≤ D * h x :=
    ⟨ColumnKernels.action_nonneg u h hn x, ColumnKernels.action_le u h _ (mul_nonneg hD (hn x))
      (fun y ↦ hratio x y) x⟩
  have hp (z : BitString n) : 0 ≤ liftClass (action u h) z ∧ liftClass (action u h) z ≤ D * liftClass h z := by
    unfold liftClass
    split_ifs
    · exact hact _
    · simp only [mul_zero, le_refl, and_self]
  constructor
  · exact mean_nonneg _ (fun j ↦ (hp (P j)).1)
  · have ht := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun j ↦ (hp (P j)).2)
    rw [mean_mul] at ht
    exact ht

lemma mean_comm {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β) (f : α → β → ℝ) :
    mean p (fun x ↦ mean q (f x)) = mean q (fun y ↦ mean p (fun x ↦ f x y)) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma fieldAction_mean (P : Population n mu) (partners : PMF (BitString n)) (h : ColumnClass n k i b → ℝ) :
    fieldAction P (mixedKernel partners) h = mean partners (partnerAverage P h) := by
  have hpoint (z : BitString n) :
      liftClass (ReproductiveValues.action (mixedKernel partners) h) z =
        mean partners (fun u ↦ liftClass (action u h) z) := by
    by_cases hz : (Sampling.zeros z).card = k ∧ z i = b
    · simp only [liftClass, dif_pos hz]
      exact mixed_action partners h ⟨z, hz⟩
    · simp only [liftClass, dif_neg hz, mean_const]
  unfold fieldAction average
  simp_rw [hpoint]
  rw [mean_comm]
  rfl

end
end Lax343628Proofs.WeightedKernels
