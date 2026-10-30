import Lax343628Proofs.WeightedFieldControl
import Lax343628Proofs.EmpiricalStability

namespace Lax343628Proofs.AveragedOperators

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open Lax343628Proofs.WeightedFieldControl Lax343628Proofs.EmpiricalStability
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+} {i : Fin n} {b : Fin 2}

lemma average_lift_sub (P : Population n mu) (f g : ColumnClass n k i b → ℝ) :
    average P (liftClass (fun x ↦ f x - g x)) = average P (liftClass f) - average P (liftClass g) := by
  have hp : liftClass (fun x ↦ f x - g x) = fun z ↦ liftClass f z - liftClass g z := by
    funext z
    unfold liftClass
    split_ifs <;> ring
  unfold average
  rw [hp, mean_sub]

lemma fieldAction_sub (P : Population n mu) (A : ReproductiveValues.Kernel (ColumnClass n k i b))
    (f g : ColumnClass n k i b → ℝ) :
    fieldAction P A (fun x ↦ f x - g x) = fieldAction P A f - fieldAction P A g := by
  unfold fieldAction
  have heq : ReproductiveValues.action A (fun x ↦ f x - g x) =
      fun x ↦ ReproductiveValues.action A f x - ReproductiveValues.action A g x := by
    funext x
    exact action_sub A f g x
  rw [heq, average_lift_sub]

def difference (P : Population n mu) (A B : ReproductiveValues.Kernel (ColumnClass n k i b))
    (h : ColumnClass n k i b → ℝ) : ℝ := fieldAction P A h - fieldAction P B h

lemma difference_eq_average (P : Population n mu) (A B : ReproductiveValues.Kernel (ColumnClass n k i b))
    (h : ColumnClass n k i b → ℝ) : difference P A B h =
      average P (liftClass (fun x ↦ ReproductiveValues.action A h x - ReproductiveValues.action B h x)) := by
  rw [average_lift_sub]
  rfl

lemma difference_split (P : Population n mu) (A B C : ReproductiveValues.Kernel (ColumnClass n k i b))
    (f g : ColumnClass n k i b → ℝ) : difference P A C f = difference P A B f +
      difference P B C (fun x ↦ f x - g x) + difference P B C g := by
  unfold difference
  rw [fieldAction_sub, fieldAction_sub]
  ring

lemma fieldAction_bound (P : Population n mu) (A : ReproductiveValues.Kernel (ColumnClass n k i b))
    (h : ColumnClass n k i b → ℝ) (D : ℝ) (hD : 0 ≤ D) (hn : ∀ z, 0 ≤ h z)
    (hratio : ∀ x z, h z ≤ D * h x) :
    0 ≤ fieldAction P A h ∧ fieldAction P A h ≤ D * average P (liftClass h) := by
  have hpoint (x : ColumnClass n k i b) : 0 ≤ ReproductiveValues.action A h x ∧
      ReproductiveValues.action A h x ≤ D * h x :=
    ⟨ReproductiveValues.action_nonneg A h hn x,
      ReproductiveValues.action_le A h _ (mul_nonneg hD (hn x)) (fun z ↦ hratio x z) x⟩
  have hp (z : BitString n) : 0 ≤ liftClass (ReproductiveValues.action A h) z ∧
      liftClass (ReproductiveValues.action A h) z ≤ D * liftClass h z := by
    unfold liftClass
    split_ifs
    · exact hpoint _
    · simp only [mul_zero, le_refl, and_self]
  constructor
  · exact mean_nonneg _ (fun u ↦ (hp (P u)).1)
  · have ht := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) (fun u ↦ (hp (P u)).2)
    rw [mean_mul] at ht
    exact ht

lemma difference_ratio_bound (P : Population n mu) (A B : ReproductiveValues.Kernel (ColumnClass n k i b))
    (h : ColumnClass n k i b → ℝ) (D : ℝ) (hD : 0 ≤ D) (hn : ∀ z, 0 ≤ h z)
    (hratio : ∀ x z, h z ≤ D * h x) : |difference P A B h| ≤ D * average P (liftClass h) := by
  have ha := fieldAction_bound P A h D hD hn hratio
  have hb := fieldAction_bound P B h D hD hn hratio
  unfold difference
  rw [abs_le]
  constructor <;> linarith

lemma difference_normalized (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (A B : ReproductiveValues.Kernel (ColumnClass n k i b)) (h : ColumnClass n k i b → ℝ)
    (M C D y : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hy : 0 < y)
    (hMY : M * ClassChannels.fraction i b P ≤ D * y)
    (hAB : ∀ x, |ReproductiveValues.action A h x - ReproductiveValues.action B h x| ≤ C * M) :
    |difference P A B h| / y ≤ C * D := by
  rw [difference_eq_average]
  exact normalized_average P hP _ M C D y hM hC hy hMY hAB

end
end Lax343628Proofs.AveragedOperators
