import Lax343628Proofs.SpeciesParameters
import Lax343628Proofs.PhaseScale

namespace Lax343628Proofs.SpeciesScale

open Lax343628Proofs.SpeciesParameters Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma constant_power (s C : ℝ) (hs : 1 ≤ s) (hC : C ≤ s ^ 2) (q p : ℕ) (hqp : q + 2 ≤ p) :
    C * s ^ q ≤ s ^ p := by
  calc
    _ ≤ s ^ 2 * s ^ q := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = s ^ (q + 2) := by rw [pow_add]; ring
    _ ≤ _ := pow_le_pow_right₀ hs hqp

lemma large_dimension (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1)
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) :
    1000000000 * ((S : ℕ) : ℝ) ^ 10 ≤ n := by
  have hs : (16777216 : ℝ) ≤ (S : ℕ) := by exact_mod_cast hS
  exact (constant_power (S : ℕ) 1000000000 (by linarith) (by nlinarith) 10 300 (by norm_num)).trans
    (PhaseScale.dimension S n mu delta hd hn)

lemma threshold_lower (s : ℝ) (hs : 16777216 ≤ s) (k : ℕ) (hk : 1 ≤ k) (hks : (k : ℝ) ≤ s) :
    1 / s ^ 2 ≤ threshold k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hroot : Real.sqrt k ≤ s := (Real.sqrt_le_self_iff.mpr (Or.inr hkR)).trans hks
  have hrootp : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  unfold threshold
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

lemma error_numerator (s : ℝ) (hs : 16777216 ≤ s) (k : ℕ) (hk : 1 ≤ k) (hks : (k : ℝ) ≤ s) :
    4 * (k : ℝ) + 3 * ((k : ℝ) + 2) * (4 * (k : ℝ) + 1) ≤ s ^ 3 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hh : 4 * (k : ℝ) + 3 * ((k : ℝ) + 2) * (4 * (k : ℝ) + 1) ≤ 64 * s ^ 2 := by
    nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ k) hks]
  have hmul := mul_nonneg (show 0 ≤ s - 64 by linarith) (show 0 ≤ s ^ 2 by positivity)
  nlinarith

lemma quotient (s n x : ℝ) (hs : 1 ≤ s) (hn : 1000000000 * s ^ 10 ≤ n)
    (hx : x ≤ s ^ 6) (_hx0 : 0 ≤ x) : x / n ≤ (1 / s ^ 4) / 1000000000 := by
  have hsp : 0 < s := by linarith
  have hnp : 0 < n := (by positivity : 0 < 1000000000 * s ^ 10).trans_le hn
  calc
    x / n ≤ s ^ 6 / n := div_le_div_of_nonneg_right hx hnp.le
    _ ≤ s ^ 6 / (1000000000 * s ^ 10) := div_le_div_of_nonneg_left (by positivity) (by positivity) hn
    _ = _ := by
      rw [show (10 : ℕ) = 6 + 4 by rfl, pow_add]
      field_simp

lemma error_bounds (s : ℝ) (hs : 16777216 ≤ s) (n k : ℕ) (hk : 1 ≤ k)
    (hks : (k : ℝ) ≤ s) (hn : 1000000000 * s ^ 10 ≤ n) :
    PlateauKernelApproximation.approximationError n k ≤ (1 / s ^ 4) / 1000000000 ∧
      PlateauKernelApproximation.approximationError n k ^ 2 * n ≤ (1 / s ^ 4) / 1000000000 := by
  let b : ℝ := 4 * (k : ℝ) + 3 * ((k : ℝ) + 2) * (4 * (k : ℝ) + 1)
  have hs1 : 1 ≤ s := by linarith
  have hnp : (0 : ℝ) < n := (by positivity : 0 < 1000000000 * s ^ 10).trans_le hn
  have hb : b ≤ s ^ 3 := error_numerator s hs k hk hks
  have hb0 : 0 ≤ b := by positivity
  have h36 : s ^ 3 ≤ s ^ 6 := pow_le_pow_right₀ hs1 (by norm_num)
  constructor
  · exact quotient s n b hs1 hn (hb.trans h36) hb0
  · have hsquare : b ^ 2 ≤ s ^ 6 := by
      have hh := pow_le_pow_left₀ hb0 hb 2
      simpa only [← pow_mul] using hh
    have heq : PlateauKernelApproximation.approximationError n k ^ 2 * n = b ^ 2 / n := by
      unfold PlateauKernelApproximation.approximationError
      change (b / (n : ℝ)) ^ 2 * n = b ^ 2 / n
      field_simp
    rw [heq]
    exact quotient s n (b ^ 2) hs1 hn hsquare (sq_nonneg b)

end
end Lax343628Proofs.SpeciesScale
