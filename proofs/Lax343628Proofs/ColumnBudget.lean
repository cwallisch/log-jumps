import Lax343628Proofs.DrivenTracking
import Lax343628Proofs.ColumnExit

namespace Lax343628Proofs.ColumnBudget

open Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
noncomputable section

structure Budget (n k R ell : ℕ) (mu rs : ℕ+) (pc a fmin amin fmax omega L B : ℝ) : Prop where
  hk : 2 ≤ k
  hn : 4 * k ≤ n
  hell : 1 ≤ ell
  hpc : 0 ≤ pc ∧ pc ≤ 1
  ha : 0 ≤ a
  halpha : a = pc / ((mu : ℕ) + 1 : ℝ)
  hcell : (ell : ℝ) * a ≤ 1
  horizon : R * a * ReproductiveAdmissibility.error n k ≤ 1
  hfmin : 1 / (mu : ℕ) < fmin
  hamin : 1 / (mu : ℕ) < amin
  hfmax : 0 ≤ fmax
  homega : 0 < omega
  hL : 0 < L
  himm : 1 / (n : ℝ) ≤ amin
  hbias : (3 : ℝ) ^ k * ((k : ℝ) + 1) / n ≤ 1
  hsmall : 2 / ((mu : ℕ) + 1 : ℝ) + a * (3 : ℝ) ^ k +
    ((3 : ℝ) ^ k / ((mu : ℕ) * fmin) + 3 * (3 : ℝ) ^ k / (mu : ℕ)) ≤ 1 / 2
  driftBudget : ∀ H : Fin (R + 1), H.val * ((a * (3 : ℝ) ^ k +
    (3 : ℝ) ^ k * (((k : ℝ) + 1) + 1 / amin) / n) / ((mu : ℕ) + 1 : ℝ)) ≤ 1 / 32
  squareBudget : ∀ H : Fin (R + 1), 3 * (H.val * (2 / ((mu : ℕ) + 1 : ℝ)) ^ 2 + H.val * (a * (3 : ℝ) ^ k) ^ 2 +
    2 * ((3 : ℝ) ^ k / ((mu : ℕ) * fmin)) ^ 2 * (6 * R * fmax + 2 * L) +
      18 * H.val * ((3 : ℝ) ^ k / (mu : ℕ)) ^ 2) ≤ 1 / 64
  samplingBudget : ∀ H : Fin (R + 1), 2 * (a * H.val * MismatchTotals.cost (mu : ℕ) ell a ((3 : ℝ) ^ k) +
    (a * H.val * (3 : ℝ) ^ k) / (2 * Real.sqrt (rs : ℕ))) ≤ 1 / 32
  listsBudget : (count R ell : ℝ) * (4 / ((rs : ℕ) * omega ^ 2)) ≤ 1 / 8
  noiseStepM : 2 * (4 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * fmin)) * L ≤ 1 / 64
  noiseVarM : 4 * R * (3 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * fmin)) * L ≤ (1 / 64) ^ 2
  noiseStepR : 2 * (5 * ((3 : ℝ) ^ k) ^ 2 / ((mu : ℕ) * amin)) * L ≤ 1 / 64
  noiseVarR : 4 * R * (4 * ((3 : ℝ) ^ k) ^ 4 / (((mu : ℕ) : ℝ) ^ 2 * amin)) * L ≤ (1 / 64) ^ 2
  shadowSmall : a * (128 * (k : ℝ) ^ 2 / n) * (3 : ℝ) ^ k ≤ 1
  shadowDimension : (128 * (k : ℝ) ^ 2 / n) * (3 : ℝ) ^ k * (1 + (3 : ℝ) ^ k) ≤
    ShadowGaps.delta k * (omega / 2) / 2
  growthTime : Real.log (B * (3 : ℝ) ^ k) + 1 ≤ R * Real.log (SparseGrowth.base k a omega)

lemma Budget.fmin_pos {n k R ell : ℕ} {mu rs : ℕ+} {pc a fmin amin fmax omega L B : ℝ}
    (h : Budget n k R ell mu rs pc a fmin amin fmax omega L B) : 0 < fmin :=
  lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 1 / (mu : ℕ)) h.hfmin

lemma Budget.amin_pos {n k R ell : ℕ} {mu rs : ℕ+} {pc a fmin amin fmax omega L B : ℝ}
    (h : Budget n k R ell mu rs pc a fmin amin fmax omega L B) : 0 < amin :=
  lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 1 / (mu : ℕ)) h.hamin

end
end Lax343628Proofs.ColumnBudget
