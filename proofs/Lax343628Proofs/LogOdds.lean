import Lax343628Proofs.SparseSelection

namespace Lax343628Proofs.LogOdds

open scoped BigOperators
noncomputable section

lemma log_one_add_lower {x : ℝ} (hx : |x| ≤ 1 / 2) :
    x - 2 * x ^ 2 ≤ Real.log (1 + x) := by
  have hx' := abs_le.mp hx
  have hp : 0 < 1 + x := by linarith
  have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  have hl := Real.one_sub_inv_le_log_of_pos hp
  rw [heq] at hl
  apply le_trans _ hl
  apply (le_div_iff₀ hp).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 + 2 * x by linarith)]

lemma lower_step {y yn x : ℝ} (hy : 0 < y) (hyn : 0 < yn)
    (hx : |x| ≤ 1 / 2) (hchange : y * (1 + x) ≤ yn) :
    x - 2 * x ^ 2 ≤ Real.log yn - Real.log y := by
  have hp : 0 < 1 + x := by have := (abs_le.mp hx).1; linarith
  have hr : 1 + x ≤ yn / y := (le_div_iff₀ hy).mpr (by nlinarith)
  have hl := Real.log_le_log hp hr
  rw [Real.log_div hyn.ne' hy.ne'] at hl
  exact (log_one_add_lower hx).trans hl

lemma upper_step {z zn w : ℝ} (hz : 0 < z) (hzn : 0 < zn)
    (hchange : zn ≤ z * (1 + w)) :
    Real.log zn - Real.log z ≤ w := by
  have hr : zn / z ≤ 1 + w := (div_le_iff₀ hz).mpr (by nlinarith)
  have hl := Real.log_le_sub_one_of_pos (div_pos hzn hz)
  rw [Real.log_div hzn.ne' hz.ne'] at hl
  linarith

lemma telescope (H : ℕ) (y z x w : ℕ → ℝ)
    (hy : ∀ t, t ≤ H → 0 < y t) (hz : ∀ t, t ≤ H → 0 < z t)
    (hx : ∀ t, t < H → |x t| ≤ 1 / 2)
    (hyl : ∀ t, t < H → y t * (1 + x t) ≤ y (t + 1))
    (hzu : ∀ t, t < H → z (t + 1) ≤ z t * (1 + w t)) :
    Real.log (y H / z H) - Real.log (y 0 / z 0) ≥
      ∑ t ∈ Finset.range H, (x t - w t - 2 * x t ^ 2) := by
  have hs := Finset.sum_le_sum (s := Finset.range H) (fun t ht ↦
    sub_le_sub (lower_step (hy t (by have := Finset.mem_range.mp ht; omega))
      (hy (t + 1) (by have := Finset.mem_range.mp ht; omega)) (hx t (Finset.mem_range.mp ht))
      (hyl t (Finset.mem_range.mp ht)))
      (upper_step (hz t (by have := Finset.mem_range.mp ht; omega))
        (hz (t + 1) (by have := Finset.mem_range.mp ht; omega)) (hzu t (Finset.mem_range.mp ht))))
  have heq (t : ℕ) : (x t - 2 * x t ^ 2) - w t = x t - w t - 2 * x t ^ 2 := by ring
  simp_rw [heq] at hs
  have htel : (∑ t ∈ Finset.range H,
      (Real.log (y (t + 1)) - Real.log (y t) - (Real.log (z (t + 1)) - Real.log (z t)))) =
        (Real.log (y H) - Real.log (y 0)) - (Real.log (z H) - Real.log (z 0)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun t ↦ Real.log (y t)),
      Finset.sum_range_sub (fun t ↦ Real.log (z t))]
  rw [htel] at hs
  rw [Real.log_div (hy H le_rfl).ne' (hz H le_rfl).ne',
    Real.log_div (hy 0 (Nat.zero_le H)).ne' (hz 0 (Nat.zero_le H)).ne']
  linarith

end
end Lax343628Proofs.LogOdds
