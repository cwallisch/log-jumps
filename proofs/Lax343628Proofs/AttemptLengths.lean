import Lax343628Proofs.PhaseParameters
import Lax343628Proofs.BlockParameters

namespace Lax343628Proofs.AttemptLengths

open Lax343628Proofs.PhaseParameters Lax343628Proofs.BlockParameters Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

def waitCost (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) : ℝ :=
  ((n : ℝ) + (mu : ℕ)) * ((S : ℕ) : ℝ) ^ 254 * logarithms n mu delta

def wait (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) : ℕ :=
  Nat.ceil (64 * ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta)

def service (S : ℕ+) (mu : ℕ+) : ℕ := rounds mu * horizon (S : ℕ) mu

def decision (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) : ℕ :=
  (2 * (S : ℕ) ^ 12 + 2) * (wait S n mu delta + service S mu)

def terminal (S : ℕ+) : ℕ := 64 * (S : ℕ) ^ 4

lemma waitCost_one (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    1 ≤ waitCost S n mu delta := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hW := (logarithms_bounds n mu delta hd).1
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hs)) hW

lemma wait_pos (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    0 < wait S n mu delta := by
  have hw := waitCost_one S n mu delta hd
  have hh := Nat.le_ceil (64 * ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta)
  have hp : 0 < 64 * ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta := by positivity
  have hp' : (0 : ℝ) < wait S n mu delta := hp.trans_le hh
  exact_mod_cast hp'

lemma service_pos (S mu : ℕ+) : 0 < service S mu := by
  unfold service rounds horizon
  positivity

lemma wait_error (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    (((2 * (S : ℕ) ^ 12 + 2 : ℕ) : ℝ) * (waitCost S n mu delta / ((wait S n mu delta : ℝ) + 1))) ≤ 1 / 16 := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hpow : (1 : ℝ) ≤ ((S : ℕ) : ℝ) ^ 12 := one_le_pow₀ hs
  have hcost := waitCost_one S n mu delta hd
  have hceil := Nat.le_ceil (64 * ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta)
  have hwait : 64 * ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta ≤ (wait S n mu delta : ℝ) := hceil
  have hE : (((2 * (S : ℕ) ^ 12 + 2 : ℕ) : ℝ)) ≤ 4 * ((S : ℕ) : ℝ) ^ 12 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (wait S n mu delta : ℝ) + 1)).mpr
  have hh := mul_le_mul_of_nonneg_right hE (show 0 ≤ waitCost S n mu delta by linarith)
  linarith

lemma wait_upper (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    (wait S n mu delta : ℝ) ≤ 65 * ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hcost := waitCost_one S n mu delta hd
  have hprod : 1 ≤ ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs) hcost
  have hh := (Nat.ceil_lt_add_one (show 0 ≤ 64 * ((S : ℕ) : ℝ) ^ 12 * waitCost S n mu delta by positivity)).le
  change (wait S n mu delta : ℝ) ≤ _ at hh
  linarith

lemma rounds_upper (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    (rounds mu : ℝ) ≤ 18 * logarithms n mu delta := by
  have hW := logarithms_bounds n mu delta hd
  have hm : (1 : ℝ) ≤ (mu : ℕ) := by exact_mod_cast mu.pos
  have hlog : 0 ≤ Real.log ((mu : ℕ) : ℝ) := Real.log_nonneg hm
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.log ((mu : ℕ) : ℝ) by positivity)).le
  have hlogle : Real.log ((mu : ℕ) : ℝ) ≤ logarithms n mu delta := by
    exact (Real.log_le_log (by positivity) (by linarith : ((mu : ℕ) : ℝ) ≤ (mu : ℕ) + 1)).trans hW.2.2.1
  unfold rounds
  rw [Nat.cast_add, Nat.cast_one]
  linarith

end
end Lax343628Proofs.AttemptLengths
