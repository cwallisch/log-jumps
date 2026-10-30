import Lax343628Proofs.FairMedian

namespace Lax343628Proofs.FairInterval

open Lax343628Proofs.FairMedian
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma bound (N : ℕ) (hN : 1 ≤ N) (c lo hi : ℝ) (hwidth : lo < hi)
    (hmean : lo ≤ c + (N : ℝ) / 2 ∧ c + (N : ℝ) / 2 ≤ hi)
    (hvariance : 8 * (N : ℝ) ≤ (hi - lo) ^ 2) :
    1 / 8 ≤ probability N {w | lo < c + (w.val : ℝ) ∧ c + (w.val : ℝ) ≤ hi} := by
  let A : Set (Fin (N + 1)) := {w | lo < c + (w.val : ℝ) ∧ c + (w.val : ℝ) ≤ hi}
  let V : Set (Fin (N + 1)) := {w | (hi - lo) / 2 ≤ |(w.val : ℝ) - (N : ℝ) / 2|}
  have hp : 0 < (hi - lo) / 2 := by linarith
  have htail : probability N V ≤ 1 / 8 := by
    apply (deviation N ((hi - lo) / 2) hp).trans
    apply (div_le_iff₀ (by positivity : 0 < 4 * ((hi - lo) / 2) ^ 2)).mpr
    nlinarith
  by_cases hmid : c + (N : ℝ) / 2 ≤ (lo + hi) / 2
  · have hlarge : 1 / 4 ≤ probability N {w | lo < c + (w.val : ℝ)} := by
      apply (strict_upper N hN).trans
      apply mono N
      intro w hw
      have hwR : (N : ℝ) < 2 * (w.val : ℝ) := by exact_mod_cast hw
      change lo < c + (w.val : ℝ)
      linarith [hmean.1]
    have hcover := cover N {w | lo < c + (w.val : ℝ)} A V (by
      intro w hw
      by_cases hhi : c + (w.val : ℝ) ≤ hi
      · exact Or.inl ⟨hw, hhi⟩
      · right
        have habs := le_abs_self ((w.val : ℝ) - (N : ℝ) / 2)
        change (hi - lo) / 2 ≤ |(w.val : ℝ) - (N : ℝ) / 2|
        linarith)
    linarith
  · have hlarge : 1 / 2 ≤ probability N {w | c + (w.val : ℝ) ≤ hi} := by
      apply (weak_lower N).trans
      apply mono N
      intro w hw
      have hwR : 2 * (w.val : ℝ) ≤ N := by exact_mod_cast hw
      change c + (w.val : ℝ) ≤ hi
      linarith [hmean.2]
    have hcover := cover N {w | c + (w.val : ℝ) ≤ hi} A V (by
      intro w hw
      by_cases hlo : lo < c + (w.val : ℝ)
      · exact Or.inl ⟨hlo, hw⟩
      · right
        have habs := neg_le_abs ((w.val : ℝ) - (N : ℝ) / 2)
        change (hi - lo) / 2 ≤ |(w.val : ℝ) - (N : ℝ) / 2|
        linarith)
    linarith

end
end Lax343628Proofs.FairInterval
