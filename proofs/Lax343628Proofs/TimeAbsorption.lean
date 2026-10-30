import Lax343628Proofs.AttemptTime

namespace Lax343628Proofs.TimeAbsorption

open Lax343628Proofs.AttemptLengths Lax343628Proofs.AttemptTime Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma scale (s W x y : ℝ) (hs : 16777216 ≤ s) (hW : 1 ≤ W)
    (hx : s ^ 300 * W ≤ x) (hy : s ^ 300 * W ≤ y) :
    (x + y) * s ^ 282 * W ≤ x * y / 16 := by
  have hs1 : 1 ≤ s := by linarith
  have hp18 : s ≤ s ^ 18 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 18 by norm_num)
  have hp300 : 1 ≤ s ^ 300 := one_le_pow₀ hs1
  have hxy : 1 ≤ s ^ 300 * W := one_le_mul_of_one_le_of_one_le hp300 hW
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hh := mul_le_mul_of_nonneg_left (show (32 : ℝ) ≤ s ^ 18 by linarith)
    (show 0 ≤ s ^ 282 * W by positivity)
  have heq : s ^ 282 * W * s ^ 18 = s ^ 300 * W := by
    rw [mul_right_comm, ← pow_add]
  rw [heq] at hh
  have hxscale : 32 * (s ^ 282 * W) ≤ x := by linarith
  have hyscale : 32 * (s ^ 282 * W) ≤ y := by linarith
  have h1 := mul_le_mul_of_nonneg_left hxscale hy0
  have h2 := mul_le_mul_of_nonneg_left hyscale hx0
  nlinarith

lemma decision (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) :
    (AttemptLengths.decision S n mu delta : ℝ) ≤ (mu : ℕ) * (n : ℝ) / 16 := by
  have hs : (16777216 : ℝ) ≤ (S : ℕ) := by exact_mod_cast hS
  have hh := scale (S : ℕ) (logarithms n mu delta) n (mu : ℕ) hs
    (logarithms_bounds n mu delta hd).1 hn hmu
  simpa only [mul_comm (n : ℝ) ((mu : ℕ) : ℝ)] using (decision_upper S hS n mu delta hd).trans hh

lemma terminal (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) :
    (AttemptLengths.terminal S : ℝ) ≤ (mu : ℕ) * (n : ℝ) / 16 := by
  let s : ℝ := (S : ℕ)
  let W := logarithms n mu delta
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hs1 : 1 ≤ s := by linarith
  have hW : 1 ≤ W := (logarithms_bounds n mu delta hd).1
  have h5 : s ^ 5 ≤ s ^ 300 := pow_le_pow_right₀ hs1 (by norm_num)
  have h1 : s ≤ s ^ 300 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 300 by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hW (show 0 ≤ s ^ 300 by positivity)
  have hsmall : 64 * s ^ 4 ≤ s ^ 5 := by
    rw [pow_succ]
    nlinarith [mul_nonneg (show 0 ≤ s - 64 by linarith) (show 0 ≤ s ^ 4 by positivity)]
  have hterm : (AttemptLengths.terminal S : ℝ) ≤ n := by
    simp only [AttemptLengths.terminal, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    change 64 * s ^ 4 ≤ n
    linarith
  have hmu16 : (16 : ℝ) ≤ (mu : ℕ) := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right hmu16 hn0
  linarith

lemma total (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ (mu : ℕ))
    (hn : ((S : ℕ) : ℝ) ^ 300 * logarithms n mu delta ≤ n) :
    ((AttemptLengths.decision S n mu delta + AttemptLengths.terminal S : ℕ) : ℝ) ≤
      (mu : ℕ) * (n : ℝ) / 8 := by
  have h1 := decision S hS n mu delta hd hmu hn
  have h2 := terminal S hS n mu delta hd hmu hn
  rw [Nat.cast_add]
  linarith

end
end Lax343628Proofs.TimeAbsorption
