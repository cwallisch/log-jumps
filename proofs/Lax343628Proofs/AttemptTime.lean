import Lax343628Proofs.AttemptLengths

namespace Lax343628Proofs.AttemptTime

open Lax343628Proofs.AttemptLengths Lax343628Proofs.PhaseParameters Lax343628Proofs.BlockParameters
open Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma scale_product (s x W : ℝ) (p q : ℕ) : s ^ p * (x * s ^ q * W) = x * s ^ (p + q) * W := by
  rw [pow_add]
  ring

lemma wait_upper (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1) :
    (wait S n mu delta : ℝ) ≤ ((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 267 * logarithms n mu delta := by
  let s : ℝ := (S : ℕ)
  have hs : (65 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast (show 65 ≤ (S : ℕ) by omega)
  have hc := waitCost_one S n mu delta hd
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ s ^ 12 * waitCost S n mu delta by positivity)
  have hupper := (AttemptLengths.wait_upper S n mu delta hd).trans (by convert hh using 1; ring)
  have heq : s * (s ^ 12 * waitCost S n mu delta) =
      ((n : ℝ) + (mu : ℕ)) * s ^ 267 * logarithms n mu delta := by
    rw [← mul_assoc, ← pow_succ', waitCost, scale_product]
  exact hupper.trans_eq heq

lemma service_upper (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1) :
    (service S mu : ℝ) ≤ ((mu : ℕ) : ℝ) * ((S : ℕ) : ℝ) ^ 13 * logarithms n mu delta := by
  let s : ℝ := (S : ℕ)
  have hs : (18 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast (show 18 ≤ (S : ℕ) by omega)
  have hW := (logarithms_bounds n mu delta hd).1
  have hround := rounds_upper n mu delta hd
  have hR : (horizon (S : ℕ) mu : ℝ) ≤ (mu : ℕ) * s ^ 12 := by
    have hh := horizon_bound (S : ℕ) (by omega) mu
    have hh' : (horizon (S : ℕ) mu : ℝ) ≤ (((mu : ℕ) * (S : ℕ) ^ 12 : ℕ) : ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_mul, Nat.cast_pow, s] using hh' 
  have hh := mul_le_mul hround hR (by positivity) (by positivity : 0 ≤ 18 * logarithms n mu delta)
  have hscale := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ ((mu : ℕ) : ℝ) * s ^ 12 * logarithms n mu delta by positivity)
  unfold service
  rw [Nat.cast_mul]
  apply hh.trans
  convert hscale using 1
  · ring
  · change (mu : ℕ) * s ^ 13 * logarithms n mu delta = _
    rw [pow_succ]
    ring

lemma decision_upper (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+) (delta : ℝ)
    (hd : 0 < delta ∧ delta ≤ 1) :
    (decision S n mu delta : ℝ) ≤ ((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 282 * logarithms n mu delta := by
  let s : ℝ := (S : ℕ)
  let W := logarithms n mu delta
  let x : ℝ := (n : ℝ) + (mu : ℕ)
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hs1 : 1 ≤ s := by linarith
  have hW : 1 ≤ W := (logarithms_bounds n mu delta hd).1
  have hx : 0 ≤ x := by positivity
  have hp : s ^ 13 ≤ s ^ 267 := pow_le_pow_right₀ hs1 (by norm_num)
  have hserv := service_upper S hS n mu delta hd
  have hserv' : (service S mu : ℝ) ≤ x * s ^ 267 * W := by
    apply hserv.trans
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    apply mul_le_mul (by dsimp [x]; have := Nat.cast_nonneg (α := ℝ) n; linarith) hp (by positivity) hx
  have hwait := wait_upper S hS n mu delta hd
  have hsum : (wait S n mu delta : ℝ) + service S mu ≤ x * s ^ 268 * W := by
    have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ s by linarith) (show 0 ≤ x * s ^ 267 * W by positivity)
    have heq : s * (x * s ^ 267 * W) = x * s ^ 268 * W := by rw [pow_succ]; ring
    rw [heq] at hh
    linarith
  have hE : (((2 * (S : ℕ) ^ 12 + 2 : ℕ) : ℝ)) ≤ s ^ 14 := by
    have hp1 : 1 ≤ s ^ 12 := one_le_pow₀ hs1
    have hs2 : 4 ≤ s ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ s ^ 12 by positivity)
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    change 2 * s ^ 12 + 2 ≤ s ^ 14
    rw [show (14 : ℕ) = 12 + 2 by rfl, pow_add]
    linarith
  have hh := mul_le_mul hE hsum (by positivity) (by positivity : 0 ≤ s ^ 14)
  simpa only [decision, Nat.cast_mul, Nat.cast_add, s, x, W] using hh.trans_eq (scale_product s x W 14 268)

end
end Lax343628Proofs.AttemptTime
