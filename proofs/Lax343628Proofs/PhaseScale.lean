import Lax343628Proofs.PhaseParameters
import Lax343628Proofs.BlockParameterBounds

namespace Lax343628Proofs.PhaseScale

open Lax343628Proofs.PhaseParameters Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma cancel_powers (s W : ℝ) (hs : 0 < s) (hW : 0 < W) (p g : ℕ) :
    s ^ p * W / (s ^ (p + g) * W) = 1 / s ^ g := by
  have heq : s ^ (p + g) * W = (s ^ p * W) * s ^ g := by rw [pow_add]; ring
  rw [heq, div_mul_eq_div_div, div_self (by positivity : s ^ p * W ≠ 0)]

lemma dimension (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1)
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) : ((S : ℕ) : ℝ) ^ 300 ≤ n := by
  have hW := (logarithms_bounds n mu delta hd).1
  have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ ((S : ℕ) : ℝ) ^ 300 by positivity)
  have hh' : ((S : ℕ) : ℝ) ^ 300 ≤ ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta := by
    simpa only [mul_one] using hh
  exact hh'.trans hn

lemma seed_fraction (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (delta : ℝ)
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ)) :
    (seedSize S n k mu delta : ℝ) / (mu : ℕ) ≤ 1 / ((S : ℕ) : ℝ) ^ 50 := by
  have hs : (0 : ℝ) < (S : ℕ) := by exact_mod_cast S.pos
  have hm : (0 : ℝ) < (mu : ℕ) := by exact_mod_cast mu.pos
  have hW : 0 < logarithms n mu delta := by have hh := (logarithms_bounds n mu delta hd).1; linarith
  have h1 := div_le_div_of_nonneg_right (seed_upper S hS n k mu delta hD hd) hm.le
  have h2 := div_le_div_of_nonneg_left
    (show 0 ≤ ((S : ℕ) : ℝ) ^ 250 * logarithms n mu delta by positivity)
    (show 0 < ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta by positivity) hmu
  have heq := cancel_powers ((S : ℕ) : ℝ) (logarithms n mu delta) hs hW 250 50
  exact h1.trans (h2.trans_eq heq)

lemma core_fraction (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (delta : ℝ)
    (hkS : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ)) :
    (k : ℝ) * seedSize S n k mu delta / (mu : ℕ) ≤ 1 / ((S : ℕ) : ℝ) ^ 49 := by
  have hs : (0 : ℝ) < (S : ℕ) := by exact_mod_cast S.pos
  have h1 := mul_le_mul_of_nonneg_left (seed_fraction S hS n k mu delta hD hd hmu) (Nat.cast_nonneg k)
  have hkR : (k : ℝ) ≤ (S : ℕ) := by exact_mod_cast hkS
  have h2 := mul_le_mul_of_nonneg_right hkR (show 0 ≤ 1 / ((S : ℕ) : ℝ) ^ 50 by positivity)
  have heq : ((S : ℕ) : ℝ) * (1 / ((S : ℕ) : ℝ) ^ 50) = 1 / ((S : ℕ) : ℝ) ^ 49 := by
    have hh := cancel_powers ((S : ℕ) : ℝ) 1 hs (by norm_num) 1 49
    simpa only [pow_one, mul_one, div_eq_mul_inv, one_mul] using hh
  have hh := h1.trans (h2.trans_eq heq)
  convert hh using 1 <;> first | rfl | ring

lemma mass_available (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ)) : mass S n mu delta ≤ (mu : ℕ) := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs (by norm_num : 248 ≤ 300))
    (show 0 ≤ logarithms n mu delta by have hW := (logarithms_bounds n mu delta hd).1; linarith)
  rw [mass_eq]
  exact hh.trans hmu

end
end Lax343628Proofs.PhaseScale
