import Lax343628Proofs.AveragedOperators

namespace Lax343628Proofs.MismatchPoint

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates
open Lax343628Proofs.ClassChannels Lax343628Proofs.WeightedFieldControl
open Lax343628Proofs.AveragedOperators Lax343628Proofs.EmpiricalStability
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+} {i : Fin n} {b : Fin 2}

lemma field_average_comparison (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (f g : ColumnClass n k i b → ℝ) (M B D : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hz : 0 < average P (liftClass g)) (hMY : M * fraction i b P ≤ D * average P (liftClass g))
    (hfg : ∀ x, 0 ≤ f x - g x ∧ f x - g x ≤ B * M) :
    average P (liftClass g) ≤ average P (liftClass f) ∧
      average P (liftClass f) - average P (liftClass g) ≤ B * D * average P (liftClass g) := by
  have hnon : 0 ≤ average P (liftClass (fun x ↦ f x - g x)) := by
    apply FiniteDrift.mean_nonneg
    intro u
    unfold liftClass
    split_ifs
    · exact (hfg _).1
    · rfl
  have habs (x : ColumnClass n k i b) : |f x - g x| ≤ B * M := by
    rw [abs_of_nonneg (hfg x).1]
    exact (hfg x).2
  have ht := normalized_average P hP (fun x ↦ f x - g x) M B D _ hM hB hz hMY habs
  rw [abs_of_nonneg hnon, average_lift_sub] at ht
  rw [average_lift_sub] at hnon
  have hs := (div_le_iff₀ hz).mp ht
  exact ⟨by linarith, by nlinarith⟩

lemma mismatch_bound (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (A B C : ReproductiveValues.Kernel (ColumnClass n k i b)) (f g : ColumnClass n k i b → ℝ)
    (Mnext Mend popErr fieldErr D y : ℝ) (hMn : 0 ≤ Mnext) (hMe : 0 ≤ Mend)
    (hpop : 0 ≤ popErr) (hfield : 0 ≤ fieldErr) (hD : 0 ≤ D) (hy : 0 < y)
    (hz : 0 < average P (liftClass g)) (hzy : average P (liftClass g) ≤ y)
    (hvar : y - average P (liftClass g) ≤ fieldErr * D * average P (liftClass g))
    (hMYn : Mnext * fraction i b P ≤ D * y)
    (hMYe : Mend * fraction i b P ≤ D * average P (liftClass g))
    (hg : ∀ x, 0 ≤ g x) (hratio : ∀ x z, g z ≤ D * g x)
    (hdelta : ∀ x, 0 ≤ f x - g x ∧ f x - g x ≤ fieldErr * Mend)
    (hAB : ∀ x, |ReproductiveValues.action A f x - ReproductiveValues.action B f x| ≤ popErr * Mnext) :
    |difference P A C f / y - difference P B C g / average P (liftClass g)| ≤
      popErr * D + fieldErr * D + fieldErr * D ^ 2 := by
  have h1 := difference_normalized P hP A B f Mnext popErr D y hMn hpop hy hMYn hAB
  have hMYe' : Mend * fraction i b P ≤ D * y := hMYe.trans (mul_le_mul_of_nonneg_left hzy hD)
  have h2 := difference_normalized P hP B C (fun x ↦ f x - g x) Mend fieldErr D y hMe hfield hy hMYe'
    (fun x ↦ two_kernel_difference B C _ (fieldErr * Mend) (mul_nonneg hfield hMe) hdelta x)
  have h3 := normalization_error hy hz hD (mul_nonneg hfield hD) hzy
    (difference_ratio_bound P B C g D hD hg hratio) hvar
  have heq : difference P A C f / y - difference P B C g / average P (liftClass g) =
      difference P A B f / y + difference P B C (fun x ↦ f x - g x) / y +
        (difference P B C g / y - difference P B C g / average P (liftClass g)) := by
    rw [difference_split P A B C f g]
    ring
  rw [heq]
  have ht := abs_add_le (difference P A B f / y + difference P B C (fun x ↦ f x - g x) / y)
    (difference P B C g / y - difference P B C g / average P (liftClass g))
  have hs := abs_add_le (difference P A B f / y) (difference P B C (fun x ↦ f x - g x) / y)
  simp only [abs_div, abs_of_pos hy] at hs
  nlinarith

end
end Lax343628Proofs.MismatchPoint
