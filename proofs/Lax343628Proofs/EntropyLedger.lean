import Lax343628Proofs.UniformBlockBudget

namespace Lax343628Proofs.EntropyLedger

open Lax343628Proofs.BlockParameters Lax343628Proofs.SparseEnvironment Lax343628Proofs.SparseGroups
noncomputable section
set_option backward.isDefEq.respectTransparency false

def logarithms (n : ℕ) (mu : ℕ+) (delta : ℝ) : ℝ :=
  Real.log ((n : ℝ) + 1) + Real.log ((mu : ℕ) + 1 : ℝ) + Real.log (1 / delta) + 1

def level (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) : ℝ :=
  ((S : ℕ) : ℝ) ^ 184 * logarithms n mu delta

def mass (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) : ℝ :=
  ((S : ℕ) : ℝ) ^ 64 * level S n mu delta

lemma logarithms_bounds (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    1 ≤ logarithms n mu delta ∧ Real.log ((n : ℝ) + 1) ≤ logarithms n mu delta ∧
      Real.log ((mu : ℕ) + 1 : ℝ) ≤ logarithms n mu delta ∧ Real.log (1 / delta) ≤ logarithms n mu delta := by
  have hn := Real.log_nonneg (show (1 : ℝ) ≤ n + 1 by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hm := Real.log_nonneg (show (1 : ℝ) ≤ (mu : ℕ) + 1 by have := Nat.cast_nonneg (α := ℝ) (mu : ℕ); linarith)
  have hd' := Real.log_nonneg ((one_le_div hd.1).mpr hd.2)
  unfold logarithms
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma level_one (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    1 ≤ level S n mu delta := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hp : 1 ≤ ((S : ℕ) : ℝ) ^ 184 := one_le_pow₀ hs
  have hW := (logarithms_bounds n mu delta hd).1
  unfold level
  nlinarith

lemma mass_one (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    1 ≤ mass S n mu delta := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hp : 1 ≤ ((S : ℕ) : ℝ) ^ 64 := one_le_pow₀ hs
  have hW := level_one S n mu delta hd
  unfold mass
  nlinarith

lemma group_condition (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1)
    (hmu : mass S n mu delta ≤ (mu : ℕ)) : (S : ℕ) ^ 40 ≤ (mu : ℕ) := by
  have hs : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  have hp : ((S : ℕ) : ℝ) ^ 40 ≤ ((S : ℕ) : ℝ) ^ 64 := pow_le_pow_right₀ hs (by norm_num)
  have hW := level_one S n mu delta hd
  have hm := mul_le_mul_of_nonneg_left hW (show 0 ≤ ((S : ℕ) : ℝ) ^ 64 by positivity)
  change ((S : ℕ) : ℝ) ^ 64 * level S n mu delta ≤ (mu : ℕ) at hmu
  have hh : ((S : ℕ) : ℝ) ^ 40 ≤ (mu : ℕ) := by nlinarith
  exact_mod_cast hh

lemma horizon_log (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n : ℕ) (mu : ℕ+)
    (delta : ℝ) (hd : 0 < delta ∧ delta ≤ 1) :
    Real.log ((horizon (S : ℕ) mu : ℝ) + 1) ≤ ((S : ℕ) : ℝ) ^ 2 * logarithms n mu delta := by
  let s : ℝ := (S : ℕ)
  let W := logarithms n mu delta
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hsp : 0 < s := by linarith
  have hS1 : 1 ≤ s := by linarith
  have hpow : 1 ≤ s ^ 10 := one_le_pow₀ hS1
  have hb := logarithms_bounds n mu delta hd
  have hW : 1 ≤ W := hb.1
  have hR : (horizon (S : ℕ) mu : ℝ) = ((mu : ℕ) + 1 : ℝ) * s ^ 10 := by
    simp only [horizon, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, s]
  have hRp : 1 ≤ (horizon (S : ℕ) mu : ℝ) := by
    rw [hR]
    have hm : (1 : ℝ) ≤ (mu : ℕ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (mu : ℕ); linarith
    nlinarith
  have hlog := Real.log_le_log (show 0 < (horizon (S : ℕ) mu : ℝ) + 1 by positivity)
    (show (horizon (S : ℕ) mu : ℝ) + 1 ≤ 2 * (((mu : ℕ) + 1 : ℝ) * s ^ 10) by rw [← hR]; linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (((mu : ℕ) + 1 : ℝ) * s ^ 10) ≠ 0),
    Real.log_mul (by positivity : ((mu : ℕ) + 1 : ℝ) ≠ 0) (by positivity : s ^ 10 ≠ 0), Real.log_pow] at hlog
  have hls := Real.log_le_sub_one_of_pos hsp
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hbound : Real.log ((horizon (S : ℕ) mu : ℝ) + 1) ≤ W + 10 * s + 1 := by
    norm_num only [Nat.cast_ofNat] at hlog
    linarith [hb.2.2.1]
  have hpoly : 10 * s + 2 ≤ s ^ 2 := by nlinarith
  have hm1 := mul_nonneg (show 0 ≤ W - 1 by linarith) (show 0 ≤ 10 * s + 1 by positivity)
  have hm2 := mul_le_mul_of_nonneg_right hpoly (show 0 ≤ W by linarith)
  change Real.log ((horizon (S : ℕ) mu : ℝ) + 1) ≤ s ^ 2 * W
  nlinarith

end
end Lax343628Proofs.EntropyLedger
