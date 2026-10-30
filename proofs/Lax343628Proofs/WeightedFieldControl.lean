import Lax343628Proofs.GroupSampling

namespace Lax343628Proofs.WeightedFieldControl

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.ClassChannels
open Lax343628Proofs.FiniteDrift Lax343628Proofs.FiniteComparison
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+} {i : Fin n} {b : Fin 2}

lemma ratio_average (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) (D : ℝ) (hratio : ∀ x z, h z ≤ D * h x)
    (z : ColumnClass n k i b) : h z * fraction i b P ≤ D * average P (liftClass h) := by
  have hp (u : Fin (mu : ℕ)) : h z * (if P u i = b then 1 else 0) ≤ D * liftClass h (P u) := by
    by_cases hb : P u i = b
    · simpa only [liftClass, dif_pos (And.intro (hP u) hb), if_pos hb, mul_one] using hratio ⟨P u, hP u, hb⟩ z
    · simp only [liftClass, dif_neg (by tauto : ¬((Sampling.zeros (P u)).card = k ∧ P u i = b)),
        if_neg hb, mul_zero, le_refl]
  have ht := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hp
  rw [mean_mul, mean_mul] at ht
  exact ht

lemma child_bound (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (h : ColumnClass n k i b → ℝ) (D y : ℝ) (hD : 0 ≤ D) (hratio : ∀ x z, h z ≤ D * h x)
    (hy : average P (liftClass h) ≤ y) (hf : 0 < fraction i b P) (z : ColumnClass n k i b) :
    h z ≤ D * y / fraction i b P := by
  apply (le_div_iff₀ hf).mpr
  exact (ratio_average P hP h D hratio z).trans (mul_le_mul_of_nonneg_left hy hD)

lemma average_abs (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (F : ColumnClass n k i b → ℝ) (M : ℝ) (_hM : 0 ≤ M) (hF : ∀ z, |F z| ≤ M) :
    |average P (liftClass F)| ≤ fraction i b P * M := by
  have hp (u : Fin (mu : ℕ)) : |liftClass F (P u)| ≤ M * (if P u i = b then 1 else 0) := by
    by_cases hb : P u i = b
    · simpa only [liftClass, dif_pos (And.intro (hP u) hb), if_pos hb, mul_one] using hF ⟨P u, hP u, hb⟩
    · simp only [liftClass, dif_neg (by tauto : ¬((Sampling.zeros (P u)).card = k ∧ P u i = b)),
        if_neg hb, mul_zero, abs_zero, le_refl]
  have ht := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hp
  rw [mean_mul] at ht
  exact (abs_mean_le _ _).trans (by simpa only [fraction, mul_comm] using ht)

lemma normalized_average (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (F : ColumnClass n k i b → ℝ) (M B D y : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hy : 0 < y) (hMY : M * fraction i b P ≤ D * y) (hF : ∀ z, |F z| ≤ B * M) :
    |average P (liftClass F)| / y ≤ B * D := by
  have ht := average_abs P hP F (B * M) (mul_nonneg hB hM) hF
  apply (div_le_iff₀ hy).mpr
  have hs := mul_le_mul_of_nonneg_left hMY hB
  nlinarith

lemma normalization_error {N y z B C : ℝ} (hy : 0 < y) (hz : 0 < z) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hzy : z ≤ y) (hN : |N| ≤ B * z) (hyz : y - z ≤ C * z) :
    |N / y - N / z| ≤ B * C := by
  have heq : N / y - N / z = -(N * (y - z) / (y * z)) := by field_simp; ring
  rw [heq, abs_neg, abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hzy), abs_of_pos (mul_pos hy hz)]
  apply (div_le_iff₀ (mul_pos hy hz)).mpr
  have h1 := mul_le_mul hN hyz (sub_nonneg.mpr hzy) (mul_nonneg hB hz.le)
  have h2 := mul_le_mul_of_nonneg_left hzy (mul_nonneg (mul_nonneg hB hC) hz.le)
  nlinarith

end
end Lax343628Proofs.WeightedFieldControl
