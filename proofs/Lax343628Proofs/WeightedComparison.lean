import Lax343628Proofs.SparseComparison
import Lax343628Proofs.RunLogOdds

namespace Lax343628Proofs.WeightedComparison

open Lax343628.Algorithm Lax343628Proofs.ColumnKernels
open Lax343628Proofs.ClassFields Lax343628Proofs.ClassBirthEstimates Lax343628Proofs.ClassChannels
open Lax343628Proofs.FiniteDrift
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {mu : ℕ+} {i : Fin n}

lemma average_compare (P : Population n mu) (hP : ∀ u, (Sampling.zeros (P u)).card = k)
    (m : ColumnClass n k i 1 → ℝ) (g : ColumnClass n k i 0 → ℝ) (L D : ℝ)
    (hcomp : ∀ x y, L * g y ≤ D * m x) :
    L * fraction i 1 P * average P (liftClass g) ≤ D * fraction i 0 P * average P (liftClass m) := by
  have hfirst (x : ColumnClass n k i 1) : L * average P (liftClass g) ≤ D * m x * fraction i 0 P := by
    have hpoint (u : Fin (mu : ℕ)) : L * liftClass g (P u) ≤ D * m x * (if P u i = 0 then 1 else 0) := by
      by_cases hb : P u i = 0
      · simpa only [liftClass, dif_pos (And.intro (hP u) hb), if_pos hb, mul_one] using hcomp x ⟨P u, hP u, hb⟩
      · simp only [liftClass, dif_neg (by tauto : ¬((Sampling.zeros (P u)).card = k ∧ P u i = 0)), if_neg hb, mul_zero, le_refl]
    have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hpoint
    rw [mean_mul, mean_mul] at hh
    exact hh
  have hpoint (u : Fin (mu : ℕ)) : L * average P (liftClass g) * (if P u i = 1 then 1 else 0) ≤
      (D * fraction i 0 P) * liftClass m (P u) := by
    by_cases hb : P u i = 1
    · rw [if_pos hb, mul_one]
      unfold liftClass
      rw [dif_pos (And.intro (hP u) hb)]
      have hh := hfirst (⟨P u, hP u, hb⟩ : ColumnClass n k i 1)
      change L * average P (liftClass g) ≤ D * fraction i 0 P * m ⟨P u, hP u, hb⟩
      nlinarith
    · simp only [liftClass, dif_neg (by tauto : ¬((Sampling.zeros (P u)).card = k ∧ P u i = 1)), if_neg hb, mul_zero, le_refl]
  have hh := mean_mono (PMF.uniformOfFintype (Fin (mu : ℕ))) hpoint
  rw [mean_mul, mean_mul] at hh
  change L * average P (liftClass g) * fraction i 1 P ≤ D * fraction i 0 P * average P (liftClass m) at hh
  nlinarith

lemma log_ratio {f ar y z L D : ℝ} (hf : 0 < f) (har : 0 < ar) (_hy : 0 < y) (hz : 0 < z)
    (hL : 0 < L) (hD : 0 < D) (hcomp : L * f * z ≤ D * ar * y) :
    Real.log (f / ar) + Real.log L - Real.log D ≤ Real.log (y / z) := by
  have hdiv : (f * L) / (ar * D) ≤ y / z := by
    apply (div_le_div_iff₀ (mul_pos har hD) hz).mpr
    nlinarith
  have hl := Real.log_le_log (div_pos (mul_pos hf hL) (mul_pos har hD)) hdiv
  rw [Real.log_div (mul_pos hf hL).ne' (mul_pos har hD).ne',
    Real.log_mul hf.ne' hL.ne', Real.log_mul har.ne' hD.ne'] at hl
  rw [Real.log_div hf.ne' har.ne']
  linarith

end
end Lax343628Proofs.WeightedComparison
