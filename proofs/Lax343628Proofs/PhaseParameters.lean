import Lax343628Proofs.EntropyLedger

namespace Lax343628Proofs.PhaseParameters

open Lax343628Proofs.EntropyLedger
noncomputable section
set_option backward.isDefEq.respectTransparency false

def theta (S : ℕ+) : ℝ := 1 / ((S : ℕ) : ℝ) ^ 8

def lowerZero (S : ℕ+) (k : ℕ) : ℝ := theta S / (16 * (3 : ℝ) ^ k)

def processed (S : ℕ+) (k : ℕ) : ℝ := lowerZero S k / 2

def seedSize (S : ℕ+) (n k : ℕ) (mu : ℕ+) (delta : ℝ) : ℕ :=
  Nat.ceil (8 * (3 : ℝ) ^ k * mass S n mu delta)

def rounds (mu : ℕ+) : ℕ := Nat.ceil (16 * Real.log ((mu : ℕ) : ℝ)) + 1

def services (S : ℕ+) (k : ℕ) : ℕ := Nat.ceil ((k : ℝ) / processed S k)

lemma theta_bounds (S : ℕ+) : 0 < theta S ∧ theta S ≤ 1 := by
  have hS : (1 : ℝ) ≤ (S : ℕ) := by exact_mod_cast S.pos
  unfold theta
  constructor
  · positivity
  · apply (div_le_one (by positivity : 0 < ((S : ℕ) : ℝ) ^ 8)).mpr
    exact one_le_pow₀ hS

lemma lower_bounds (S : ℕ+) (k : ℕ) : 0 < lowerZero S k ∧ lowerZero S k ≤ 1 / 16 := by
  have ht := theta_bounds S
  have hD : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  unfold lowerZero
  constructor
  · exact div_pos ht.1 (by positivity)
  · apply (div_le_div_of_nonneg_right ht.2 (by positivity : (0 : ℝ) ≤ 16 * (3 : ℝ) ^ k)).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

lemma processed_bounds (S : ℕ+) (k : ℕ) : 0 < processed S k ∧ processed S k ≤ 1 / 2 := by
  have hu := lower_bounds S k
  unfold processed
  constructor
  · exact div_pos hu.1 (by norm_num)
  · linarith

lemma lower_scale (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (k : ℕ)
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) :
    1 / ((S : ℕ) : ℝ) ^ 10 ≤ lowerZero S k := by
  let s : ℝ := (S : ℕ)
  have hs : (16777216 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hS
  have hsp : 0 < s := by linarith
  have hD0 : 0 ≤ (3 : ℝ) ^ k := by positivity
  have hden : 16 * (3 : ℝ) ^ k * s ^ 8 ≤ s ^ 10 := by
    have hh := mul_le_mul (show (16 : ℝ) ≤ s by linarith) hD hD0 hsp.le
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ s ^ 8 by positivity)
    nlinarith
  have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (show 0 < 16 * (3 : ℝ) ^ k * s ^ 8 by positivity) hden
  unfold lowerZero theta
  convert hh using 1 <;> first | rfl | (field_simp; ring)

lemma processed_scale (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (k : ℕ)
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) :
    1 / ((S : ℕ) : ℝ) ^ 11 ≤ processed S k := by
  have hs : (16777216 : ℝ) ≤ (S : ℕ) := by exact_mod_cast hS
  have hh := div_le_div_of_nonneg_right (lower_scale S hS k hD) (show (0 : ℝ) ≤ 2 by norm_num)
  have hden : 2 * ((S : ℕ) : ℝ) ^ 10 ≤ ((S : ℕ) : ℝ) ^ 11 := by
    have hm := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (S : ℕ) by linarith)
      (show 0 ≤ ((S : ℕ) : ℝ) ^ 10 by positivity)
    nlinarith
  have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (show 0 < 2 * ((S : ℕ) : ℝ) ^ 10 by positivity) hden
  have heq : 1 / (2 * ((S : ℕ) : ℝ) ^ 10) = (1 / ((S : ℕ) : ℝ) ^ 10) / 2 := by ring
  rw [heq] at hd
  exact hd.trans hh

lemma services_bound (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (k : ℕ)
    (hk : k ≤ (S : ℕ)) (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) : services S k ≤ (S : ℕ) ^ 12 := by
  have ha := processed_scale S hS k hD
  have hap := (processed_bounds S k).1
  have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ ((S : ℕ) : ℝ) ^ 12 by positivity)
  have heq : ((S : ℕ) : ℝ) ^ 12 * (1 / ((S : ℕ) : ℝ) ^ 11) = (S : ℕ) := by field_simp
  rw [heq] at hh
  have hkR : (k : ℝ) ≤ (S : ℕ) := by exact_mod_cast hk
  unfold services
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow]
  apply (div_le_iff₀ hap).mpr
  exact hkR.trans hh

lemma rounds_lower (mu : ℕ+) : 16 * Real.log ((mu : ℕ) : ℝ) + 1 ≤ (rounds mu : ℝ) := by
  have hh := Nat.le_ceil (16 * Real.log ((mu : ℕ) : ℝ))
  unfold rounds
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

lemma mass_eq (S : ℕ+) (n : ℕ) (mu : ℕ+) (delta : ℝ) :
    mass S n mu delta = ((S : ℕ) : ℝ) ^ 248 * logarithms n mu delta := by
  unfold mass level
  ring

lemma seed_lower (S : ℕ+) (n k : ℕ) (mu : ℕ+) (delta : ℝ) :
    8 * (3 : ℝ) ^ k * mass S n mu delta ≤ (seedSize S n k mu delta : ℝ) := Nat.le_ceil _

lemma seed_upper (S : ℕ+) (hS : 16777216 ≤ (S : ℕ)) (n k : ℕ) (mu : ℕ+) (delta : ℝ)
    (hD : (3 : ℝ) ^ k ≤ (S : ℕ)) (hd : 0 < delta ∧ delta ≤ 1) :
    (seedSize S n k mu delta : ℝ) ≤ ((S : ℕ) : ℝ) ^ 250 * logarithms n mu delta := by
  have hs : (16777216 : ℝ) ≤ (S : ℕ) := by exact_mod_cast hS
  have hD1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hM := mass_one S n mu delta hd
  have hM0 : 0 ≤ mass S n mu delta := by linarith
  have hDM : 1 ≤ (3 : ℝ) ^ k * mass S n mu delta := by nlinarith
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 8 * (3 : ℝ) ^ k * mass S n mu delta by positivity)).le
  have h1 : (seedSize S n k mu delta : ℝ) ≤ 9 * (3 : ℝ) ^ k * mass S n mu delta := by
    change (Nat.ceil (8 * (3 : ℝ) ^ k * mass S n mu delta) : ℝ) ≤ _
    nlinarith
  have h9 : 9 * (3 : ℝ) ^ k ≤ ((S : ℕ) : ℝ) ^ 2 := by
    have hh := mul_le_mul (show (9 : ℝ) ≤ (S : ℕ) by linarith) hD (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ k)
      (show (0 : ℝ) ≤ (S : ℕ) by positivity)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right h9 hM0
  have heq : ((S : ℕ) : ℝ) ^ 2 * mass S n mu delta =
      ((S : ℕ) : ℝ) ^ 250 * logarithms n mu delta := by
    rw [mass_eq, ← mul_assoc, ← pow_add]
  exact h1.trans (hh.trans_eq heq)

end
end Lax343628Proofs.PhaseParameters
